import CettaITP
import Lean.Replay

/- The proposer runs in a child process. A separate process reads its module
   as data and replays every new declaration into a fixed imported environment.
   The child's JSON is never evidence that a theorem was checked. -/
namespace CettaITPGuard

open Lean

private def problem (target reason : String) : Json :=
  CettaITP.response target "process-fault" reason

private def importedDependencies (base : Environment)
    (locals : Std.HashMap Name ConstantInfo) (root : Name) :
    Except String (Array Name) := Id.run do
  let mut seen : NameSet := {}
  let mut pending := #[root]
  let mut used : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    if base.contains name then
      used := used.insert name
      continue
    let some info := locals[name]?
      | return .error s!"missing local proof dependency: {name}"
    if info matches .axiomInfo _ then
      return .error s!"local axiom: {name}"
    pending := pending ++ info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      pending := pending ++ value.getUsedConstants
  return .ok <| used.toArray.qsort Name.lt

private def importedAxioms (base : Environment) (used : Array Name) :
    IO (Array Name) := do
  let context : Core.Context := {
    fileName := "<certificate>", fileMap := FileMap.ofString "" }
  let state : Core.State := { env := base }
  let mut names : NameSet := {}
  for name in used do
    let axioms ← Lean.Core.CoreM.toIO' (collectAxioms name) context state
    for ax in axioms do
      names := names.insert ax
  return names.toArray.qsort Name.lt

private def verifyCertificate (base : Environment) (path : System.FilePath)
    (target : String) (isCase : Bool) (request reply : Json) : IO Json := do
  unless (← path.pathExists) do
    return problem target "missing-certificate"
  let (moduleData, _region) ← readModuleData path
  unless !moduleData.isModule do
    return problem target "invalid-certificate-profile"
  unless moduleData.constNames.size == moduleData.constants.size do
    return problem target "invalid-certificate-constants"
  let mut locals : Std.HashMap Name ConstantInfo := {}
  for h : i in [:moduleData.constants.size] do
    let info := moduleData.constants[i]
    unless moduleData.constNames[i]! == info.name do
      return problem target "invalid-certificate-name"
    if locals.contains info.name || base.contains info.name ||
        info.isUnsafe || info.isPartial || (info matches .axiomInfo _) then
      return problem target "inadmissible-certificate-declaration"
    locals := locals.insert info.name info
  let checked ← try
    base.toKernelEnv.replay locals
  catch _ =>
    return problem target "kernel-replay"
  let attemptName := if isCase then `CettaITP.checkedCase else `CettaITP.checkedAttempt
  let some (.thmInfo proved) := checked.find? attemptName
    | return problem target "missing-checked-theorem"
  let some (.thmInfo original) := base.find? (Name.str `Megalodon target)
    | return problem target "unknown-theorem"
  if !isCase && (proved.type != original.type ||
      proved.levelParams != original.levelParams) then
    return problem target "statement-mismatch"
  let .ok rawUsed := importedDependencies base locals attemptName
    | return problem target "unaccounted-local-dependency"
  let axioms ← importedAxioms base rawUsed
  if axioms.contains `sorryAx then
    return problem target "sorry"
  let used := rawUsed.map (toString ∘ privateToUserName)
  let fields := [("used", toJson used), ("axioms", toJson (axioms.map toString))]
  if isCase then
    let .ok caseIndex := CettaITP.natField request "case"
      | return problem target "invalid-case-index"
    let .ok caseCount := CettaITP.natField reply "caseCount"
      | return problem target "invalid-case-count"
    unless caseIndex < caseCount do
      return problem target "invalid-case-count"
    return CettaITP.response target "case-checked" "ok" <|
      fields ++ [("case", toJson caseIndex), ("caseCount", toJson caseCount)]
  return CettaITP.response target "checked" "ok" fields

private def validateResult (base : Environment) (directory : System.FilePath)
    (target : String) (isCase : Bool) (index : Nat) (request reply : Json) :
    IO Json := do
  unless (CettaITP.textField reply "schema").toOption == some CettaITP.schema &&
      (CettaITP.textField reply "target").toOption == some target do
    return problem target "worker-response-identity"
  let kind := (CettaITP.textField reply "kind").toOption.getD ""
  if kind == (if isCase then "case-checked" else "checked") then
    return ← verifyCertificate base (directory / s!"{index}.olean")
      target isCase request reply
  if ["rejected", "unfinished", "protocol-fault", "process-fault"].contains kind then
    return reply
  return problem target "worker-response-kind"

private def validateReply (base : Environment) (directory : System.FilePath)
    (target operation : String) (request reply : Json) : IO Json := do
  if operation == "check" || operation == "case" then
    return ← validateResult base directory target (operation == "case") 0 request reply
  if operation == "batch" || operation == "case-batch" then
    unless (CettaITP.textField reply "schema").toOption == some CettaITP.schema &&
        (CettaITP.textField reply "target").toOption == some target &&
        (CettaITP.textField reply "kind").toOption == some operation do
      return problem target "worker-batch-identity"
    let .ok candidates := request.getObjVal? "candidates" >>= Json.getArr?
      | return problem target "invalid-candidates"
    let .ok rows := reply.getObjVal? "attempts" >>= Json.getArr?
      | return problem target "invalid-worker-batch"
    unless rows.size == candidates.size do
      return problem target "worker-batch-length"
    let mut verified := #[]
    for h : i in [:candidates.size] do
      let candidate := candidates[i]
      let .ok label := CettaITP.textField candidate "label"
        | return problem target "invalid-candidate-label"
      let .ok result := rows[i]!.getObjVal? "result"
        | return problem target "invalid-worker-row"
      let single := Json.mkObj <| [("operation", toJson
        (if operation == "case-batch" then "case" else "check"))] ++
        (if operation == "case-batch" then
          [("case", candidate.getObjVal? "case" |>.toOption.getD Json.null)]
         else [])
      let checked ← validateResult base directory target
        (operation == "case-batch") i single result
      verified := verified.push <| Json.mkObj [
        ("index", toJson i), ("label", toJson label), ("result", checked)]
    return CettaITP.response target operation "ok" [("attempts", toJson verified)]
  unless (CettaITP.textField reply "schema").toOption == some CettaITP.schema &&
      (CettaITP.textField reply "target").toOption == some target do
    return problem target "worker-response-identity"
  return reply

private def fixedBase (profile : String) : IO Environment := do
  let options := ({} : Options) |>.setBool `Elab.async false
  let modules := #[{ module := `Lean }, { module := `CettaProofTactics }] ++
    if profile == "duper" then #[{ module := `Duper }] else #[]
  return ← importModules modules options 0 (loadExts := false)

private def runWorker (command : String) (arguments : Array String) (input : String)
    (directory : System.FilePath) : IO UInt32 := do
  let (stdin, child) ← (← IO.Process.spawn {
    cmd := command,
    args := arguments.push directory.toString,
    stdin := .piped, stdout := .null, stderr := .null }).takeStdin
  stdin.putStr input
  stdin.flush
  return ← child.wait

private def run (command : String) (arguments : Array String) (input : String) : IO Json := do
  let .ok request := Json.parse input
    | return problem "" "invalid-request-json"
  let target := (CettaITP.textField request "target").toOption.getD ""
  let operation := (CettaITP.textField request "operation").toOption.getD ""
  let profile := (CettaITP.textField request "profile").toOption.getD "core"
  unless profile == "core" || profile == "duper" do
    return problem target "unknown-profile"
  let base ← fixedBase profile
  IO.FS.withTempDir fun directory => do
    let code ← runWorker command arguments input directory
    unless code == 0 do
      return problem target "worker-process"
    let responseFile := directory / "response.json"
    unless (← responseFile.pathExists) do
      return problem target "missing-worker-response"
    let .ok reply := Json.parse (← IO.FS.readFile responseFile)
      | return problem target "invalid-worker-response"
    validateReply base directory target operation request reply

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let input ← (← IO.getStdin).readToEnd
  let target := match Json.parse input with
    | .ok request => (CettaITP.textField request "target").toOption.getD ""
    | .error _ => ""
  let result ← match args with
    | ["--worker", workerExecutable] =>
      try
        run workerExecutable #[] input
      catch _ =>
        pure <| problem target "guard-exception"
    | [leanExecutable, workerScript] =>
      try
        run leanExecutable #["--run", workerScript] input
      catch _ =>
        pure <| problem target "guard-exception"
    | _ => pure <| problem "" "guard-arguments"
  IO.println result.compress
  return 0

end CettaITPGuard
