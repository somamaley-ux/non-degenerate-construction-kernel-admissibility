import Lean
import AASC
import AASCKernelPaperClean

/-!
# Environment-based project declaration inventory

This command selects constants by their defining module, not by theorem-name
prefixes or source regexes. Dependency theorems from mathlib and Lean are not
counted as project theorems. The axiom audit subsequently follows every selected
theorem transitively, including private helpers used by those theorems.
-/

open Lean Elab Command

private def isProjectModule (n : Name) : Bool :=
  n == `AASC || (`AASC).isPrefixOf n || (`Extensions).isPrefixOf n ||
    (`KernelReference).isPrefixOf n || n == `AASCKernelPaperClean

run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames.filter isProjectModule
  for m in modules do
    let item := Json.mkObj [("module", toJson m.toString)]
    liftIO <| IO.println ("PROJECT_MODULE_JSON|" ++ item.compress)
  let mut count := 0
  let mut projectConstantCount := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[idx.toNat]!
    unless isProjectModule moduleName do continue
    projectConstantCount := projectConstantCount + 1
    let forbiddenKind := match info with
      | .axiomInfo _ => true
      | .opaqueInfo _ => true
      | _ => false
    let containsPlaceholder := info.type.hasSorry ||
      (info.value? true).any Expr.hasSorry
    if forbiddenKind || info.isUnsafe || containsPlaceholder then
      throwError "Rejected project declaration {name} in {moduleName}: forbidden kind, unsafe definition, or placeholder"
    match info with
    | .thmInfo _ =>
      unless isPrivateName name || name.isInternalDetail do
        let item := Json.mkObj [
          ("name", toJson name.toString),
          ("module", toJson moduleName.toString)]
        liftIO <| IO.println ("PROJECT_THEOREM_JSON|" ++ item.compress)
        count := count + 1
    | _ => pure ()
  let summary := Json.mkObj [
    ("publicTheorems", toJson count),
    ("allProjectConstants", toJson projectConstantCount),
    ("projectModules", toJson modules.size)]
  liftIO <| IO.println ("PROJECT_INVENTORY_JSON|" ++ summary.compress)
