import Lean
import CettaProofTactics

/- The wire format is JSON. Helper declarations and the final tactic are
   parsed separately. The target type comes from the imported
   environment; the final declaration is checked by Lean's kernel. This is
   an acceptance boundary, not an operating-system sandbox for metaprograms. -/
namespace CettaITP

open Lean Elab Command Meta

def schema := "ai-math.itp.v1"

def response (target kind reason : String) (fields : List (String × Json) := []) : Json :=
  Json.mkObj <| [("schema", toJson schema), ("target", toJson target),
    ("kind", toJson kind), ("reason", toJson reason)] ++ fields

def textField (request : Json) (key : String) : Except String String :=
  request.getObjVal? key >>= Json.getStr?

def natField (request : Json) (key : String) : Except String Nat :=
  request.getObjVal? key >>= Json.getNat?

def resourceError (messages : MessageLog) : Bool :=
  messages.reportedPlusUnreported.any fun message =>
    message.severity == .error && message.data.stripNestedTags.hasTag
      (fun tag => tag == `runtime.maxHeartbeats || tag == `runtime.maxRecDepth)

def messageFailure (target : String) (messages : MessageLog) : IO Json := do
  let diagnostics ← messages.reportedPlusUnreported.toArray.mapM fun message =>
    message.toString
  return response target (if resourceError messages then "unfinished" else "rejected")
    "lean-errors" [("messages", toJson diagnostics)]

-- Imported constants are the source-order frontier. Local tactic-generated
-- auxiliaries are expanded through both types and opaque theorem bodies.
def dependencies (base env : Environment) (root : Name) : Except String (Array Name) := Id.run do
  let mut seen : NameSet := {}
  let mut pending := #[root]
  let mut used : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | return .error s!"missing proof dependency: {name}"
    if base.contains name then
      used := used.insert (privateToUserName name)
    else
      if info matches .axiomInfo _ then
        return .error s!"new local axiom: {name}"
      pending := pending ++ info.type.getUsedConstants
      if let some value := info.value? (allowOpaque := true) then
        pending := pending ++ value.getUsedConstants
  return .ok <| used.toArray.qsort Name.lt

def attempt (base : Environment) (request : Json) (target : String) : CommandElabM Json := do
  let operation := (textField request "operation").toOption.getD "check"
  if operation == "statements" then
    let .ok targets := request.getObjVal? "targets" >>= fromJson? (α := Array String)
      | return response target "protocol-fault" "invalid-targets"
    let statements ← runTermElabM fun _ => targets.mapM fun name => do
      let some (.thmInfo info) := base.find? (Name.str `Megalodon name)
        | throwError "unknown theorem: {name}"
      return (name, toString (← ppExpr info.type))
    return response target "statements" "ok" [("statements", toJson statements)]
  let targetName := Name.str `Megalodon target
  let original ← match base.find? targetName with
    | some (.thmInfo info) => pure info.toConstantVal
    | _ =>
      let some (.defnInfo expected) := base.find? `CettaITPRequest.expectedType
        | return response target "rejected" "unknown-theorem"
      pure { name := targetName, levelParams := expected.levelParams, type := expected.value }
  if operation == "statement" then
    let statement ← runTermElabM fun _ => return toString (← ppExpr original.type)
    return response target "statement" "ok" [("statement", toJson statement)]
  if operation == "context" then
    let .ok premises := request.getObjVal? "premises" >>= fromJson? (α := Array String)
      | return response target "protocol-fault" "invalid-premises"
    let .ok definitions := request.getObjVal? "definitions" >>= fromJson? (α := Array String)
      | return response target "protocol-fault" "invalid-definitions"
    let (statement, facts, defs) ← runTermElabM fun _ => do
      let describe (name : String) (includeValue : Bool) := do
        let full := Name.str `Megalodon name
        let some info := base.find? full | throwError "unknown context name: {name}"
        let type := toString (← ppExpr info.type)
        if includeValue then
          let .defnInfo defn := info | throwError "not a source definition: {name}"
          let value := toString (← ppExpr defn.value)
          return (name, s!"noncomputable def «{name}» : {type} := {value}")
        else
          -- A fact exposes only its type, never the imported proof body.
          return (name, s!"«{name}» : {type}")
      return (toString (← ppExpr original.type),
        ← premises.mapM (describe · false), ← definitions.mapM (describe · true))
    return response target "context" "ok" [
      ("statement", toJson statement), ("facts", toJson facts), ("definitions", toJson defs)]
  unless operation == "check" || operation == "case" do
    return response target "protocol-fault" "unknown-operation"
  let prelude ← match request.getObjVal? "prelude" with
    | .error _ => pure ""
    | .ok value =>
      let .ok text := value.getStr?
        | return response target "protocol-fault" "invalid-prelude"
      pure text
  if !prelude.isEmpty then
    let input := Parser.mkInputContext prelude "<proposed-helpers>"
    let parsed ← Elab.IO.processCommands input {} (← get)
    set parsed.commandState
    unless input.atEnd parsed.parserState.pos do
      return response target "protocol-fault" "incomplete-prelude"
    if (← get).messages.hasErrors then
      return response target "rejected" "helper-errors"
  let .ok tactic := textField request "tactic"
    | return response target "protocol-fault" "missing-tactic"
  let source := "by\n" ++ String.intercalate "\n"
    (tactic.splitOn "\n" |>.map ("  " ++ ·))
  let proofSyntax ← match Parser.runParserCategory (← getEnv) `term source "<proposed-tactic>" with
    | .ok stx => pure stx
    | .error message => throwError "tactic syntax: {message}"
  let attemptName := if operation == "case" then `CettaITP.checkedCase else `CettaITP.checkedAttempt
  let (expectedType, caseCount) ← runTermElabM fun _ => Term.withDeclName attemptName <|
    Term.withLevelNames original.levelParams do
      if operation == "case" then
        let .ok prefixText := textField request "prefix"
          | throwError "missing induction prefix"
        let .ok caseIndex := natField request "case"
          | throwError "invalid induction case index"
        let prefixSource := "by\n" ++ String.intercalate "\n" (prefixText.splitOn "\n" |>.map ("  " ++ ·))
        let prefixSyntax ← match Parser.runParserCategory base `term prefixSource "<induction-prefix>" with
          | .ok stx => pure stx
          | .error message => throwError "induction prefix syntax: {message}"
        let root ← mkFreshExprMVar (some original.type)
        let caseGoals ← Tactic.run root.mvarId! <| Tactic.evalTactic prefixSyntax[1]
        let some selected := caseGoals[caseIndex]?
          | throwError "induction case {caseIndex} is not one of {caseGoals.length} goals"
        let remaining ← Tactic.run selected <| Tactic.evalTactic proofSyntax[1]
        Term.synthesizeSyntheticMVarsNoPostponing
        unless remaining.isEmpty do
          throwError "induction case has unsolved goals"
        return ← selected.withContext do
          let proof ← instantiateMVars (mkMVar selected)
          let type ← instantiateMVars (← selected.getType)
          let variables := (← getLCtx).getFVars
          let closedType ← mkForallFVars variables type
          let closedProof ← mkLambdaFVars variables proof
          if closedProof.hasMVar || closedProof.hasFVar || closedType.hasMVar || closedType.hasFVar then
            throwError "induction case is not closed"
          addDecl (.thmDecl {
            name := attemptName, levelParams := original.levelParams,
            type := closedType, value := closedProof })
          return (closedType, caseGoals.length)
      let proof ← Term.elabTermEnsuringType proofSyntax (some original.type)
      Term.synthesizeSyntheticMVarsNoPostponing
      let proof ← instantiateMVars proof
      if proof.hasMVar || proof.hasFVar then
        throwError "proof contains unresolved variables"
      addDecl (.thmDecl {
        name := attemptName, levelParams := original.levelParams,
        type := original.type, value := proof })
      return (original.type, 0)
  if (← get).messages.hasErrors then
    return response target "rejected" "lean-errors"
  let env ← getEnv
  let some (.thmInfo checked) := env.checked.get.find? attemptName
    | return response target "rejected" "kernel-declaration-missing"
  unless checked.type == expectedType do
    return response target "rejected" "statement-mismatch"
  let .ok used := dependencies base env attemptName
    | return response target "rejected" "unaccounted-local-dependency"
  let axioms ← liftCoreM <| collectAxioms attemptName
  if axioms.contains `sorryAx then
    return response target "rejected" "sorry"
  let fields := [("used", toJson (used.map toString)), ("axioms", toJson (axioms.map toString))]
  if operation == "case" then
    return response target "case-checked" "ok" <| fields ++
      [("case", request.getObjValAs? Nat "case" |>.toOption |>.getD 0 |> toJson),
       ("caseCount", toJson caseCount)]
  return response target "checked" "ok" fields

def executeIn (env : Environment) (options : Options) (request : Json)
    (target : String) (certificate : System.FilePath) : IO Json := do
  let context : Command.Context := {
    fileName := "<proof-request>", fileMap := FileMap.ofString "",
    snap? := none, cancelTk? := none }
  let initial := { Command.mkState env {} options with
    scopes := [{ header := "", currNamespace := `Megalodon, opts := options }] }
  let result ← ((attempt env request target context).run initial).toIO'
  match result with
  | .error error =>
    let kind := if error.isMaxHeartbeat || error.isMaxRecDepth || error.isInterrupt
      then "unfinished" else "rejected"
    return response target kind "lean-exception"
      [("message", toJson (← error.toMessageData.toString))]
  | .ok (result, state) =>
    if state.messages.hasErrors then
      return ← messageFailure target state.messages
    if (textField result "kind").toOption ∈ [some "checked", some "case-checked"] then
      writeModule state.env certificate (writeIR := false)
    return result

-- Each attempt starts from the imported environment, not the preceding
-- attempt's state. Its elaboration budget and messages start afresh too.
def executeBatch (env : Environment) (options : Options) (request : Json)
    (target : String) (certificateDir : System.FilePath) : IO Json := do
  let .ok candidates := request.getObjVal? "candidates" >>= Json.getArr?
    | return response target "protocol-fault" "invalid-candidates"
  let mut replies := #[]
  for candidate in candidates do
    let .ok label := textField candidate "label"
      | return response target "protocol-fault" "invalid-candidate-label"
    let .ok tactic := textField candidate "tactic"
      | return response target "protocol-fault" "invalid-candidate-tactic"
    let isCase := (textField request "operation").toOption == some "case-batch"
    let single := Json.mkObj <| [
      ("operation", toJson (if isCase then "case" else "check")), ("tactic", toJson tactic),
      ("prelude", request.getObjVal? "prelude" |>.toOption |>.getD (toJson ""))] ++
      if isCase then [("prefix", request.getObjVal? "prefix" |>.toOption |>.getD Json.null),
                      ("case", candidate.getObjVal? "case" |>.toOption |>.getD Json.null)] else []
    let result ← executeIn env options single target
      (certificateDir / s!"{replies.size}.olean")
    replies := replies.push <| Json.mkObj [
      ("index", toJson replies.size), ("label", toJson label), ("result", result)]
  let kind := if (textField request "operation").toOption == some "case-batch" then "case-batch" else "batch"
  return response target kind "ok" [("attempts", toJson replies)]

def execute (request : Json) (certificateDir : System.FilePath) : IO Json := do
  let .ok target := textField request "target"
    | return response "" "protocol-fault" "missing-target"
  unless (textField request "schema").toOption == some schema do
    return response target "protocol-fault" "wrong-schema"
  let .ok heartbeats := natField request "heartbeats"
    | return response target "protocol-fault" "invalid-heartbeats"
  let .ok recursion := natField request "recursion"
    | return response target "protocol-fault" "invalid-recursion"
  let options := ({} : Options)
    |>.setBool `Elab.async false
    |>.set `maxHeartbeats heartbeats
    |>.set `maxRecDepth recursion
  let profile := (textField request "profile").toOption.getD "core"
  unless profile == "core" || profile == "duper" do
    return response target "protocol-fault" "unknown-profile"
  let modules := #[{ module := `Lean }, { module := `CettaProofTactics }] ++
    if profile == "duper" then #[{ module := `Duper }] else #[]
  let env ← importModules modules options 0
    (loadExts := true)
  let env := env.setMainModule `CettaITPRequest
  if [some "batch", some "case-batch"].contains (textField request "operation").toOption then
    executeBatch env options request target certificateDir
  else
    executeIn env options request target (certificateDir / "0.olean")

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let some directory := args.head? | return 2
  let certificateDir := System.FilePath.mk directory
  let input ← (← IO.getStdin).readToEnd
  let result ← match Json.parse input with
    | .error _ => pure <| response "" "protocol-fault" "invalid-json"
    | .ok request => do
      try
        execute request certificateDir
      catch error =>
        pure <| response "" "process-fault" "runner-exception"
          [("message", toJson error.toString)]
  IO.FS.writeFile (certificateDir / "response.json") result.compress
  return 0

end CettaITP
