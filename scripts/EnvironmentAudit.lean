module
import all Solution
import Lean.Util.CollectAxioms

open Lean Elab Command

/-! Inventory constants by their defining module, including generated helper declarations.
This executable audit is tooling; it introduces no mathematical axiom or library declaration. -/
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Quot.sound, `Classical.choice]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[index.toNat]!
      if mod == `Solution || mod == `Gershkov || (`Gershkov).isPrefixOf mod then
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Forbidden axiom {ax} in {name}, defined by {mod}"
        logInfo m!"ENV-AUDIT {mod} {name}: {axioms}"
        count := count + 1
  unless count > 100 do
    throwError "Environment inventory unexpectedly small: {count}"
  logInfo m!"ENV-AUDIT PASS: {count} authored constants, including generated helpers"
