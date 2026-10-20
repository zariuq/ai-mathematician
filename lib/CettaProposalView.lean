import Lean

/- A proposer receives real earlier declarations, not replacement axioms.
   The target's type is data; its proof and all later declarations are omitted.
   The independent guard retains its original imported environment. -/
namespace CettaProposalView

open Lean

def expectedTypeName : Name := `CettaITPRequest.expectedType

private def before (a b : Position) : Bool :=
  a.line < b.line || (a.line == b.line && a.column < b.column)

def prepare (base : Environment) (target : String) (directory : System.FilePath) : IO Unit := do
  let name := Name.str `Megalodon target
  let some (.thmInfo original) := base.find? name
    | throw <| IO.userError "unknown proposal target"
  let some cutoff := declRangeExt.find? (level := .server) base name
    | throw <| IO.userError "missing target source position"
  let sourceModule := base.getModuleIdxFor? name
  let (data, _) ← readModuleData (← findOLean `MegLib)
  unless !data.isModule && !base.contains expectedTypeName do
    throw <| IO.userError "unsupported proposal module layout"
  let mut constants := #[]
  let mut retained : NameSet := {}
  for ci in data.constants do
    let some ranges := declRangeExt.find? (level := .server) base ci.name
      | throw <| IO.userError s!"missing declaration source position: {ci.name}"
    if before ranges.range.pos cutoff.range.pos then
      constants := constants.push ci
      retained := retained.insert ci.name
  unless !retained.contains name do
    throw <| IO.userError "target entered its own proposal frontier"
  let checkReferences (expression : Expr) := do
    for dependency in expression.getUsedConstants do
      if base.getModuleIdxFor? dependency == sourceModule && !retained.contains dependency then
        throw <| IO.userError s!"proposal frontier is not closed: {dependency}"
  checkReferences original.type
  for ci in constants do
    checkReferences ci.type
    if let some value := ci.value? (allowOpaque := true) then
      checkReferences value
  constants := constants.push <| .defnInfo {
    name := expectedTypeName, levelParams := original.levelParams,
    type := .sort .zero, value := original.type, hints := .opaque, safety := .safe }
  let view : ModuleData := { data with
    constants := constants
    constNames := constants.map (·.name)
    extraConstNames := #[]
    entries := #[] }
  IO.FS.createDirAll directory
  saveModuleData (directory / "MegLib.olean") `MegLib view

end CettaProposalView
