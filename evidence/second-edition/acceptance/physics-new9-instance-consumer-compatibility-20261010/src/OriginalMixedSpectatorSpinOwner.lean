import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.NamedColorQtNext.Charge.MixedSpectatorSpin
import Lean
set_option autoImplicit false
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for text in ["LowEnergy.MixedSpectatorCandidate.instDecidableEqIndex"] do
    let name := (text.splitOn ".").foldl Name.str .anonymous
    let some info := env.checked.get.find? name | throwError "Missing checked constant {name}"
    let some index := env.getModuleIdxFor? name | throwError "Missing owner {name}"
    unless (info.value? true).isSome do throwError "Missing value {name}"
    logInfo m!"OWNER {name} = {env.header.moduleNames[index]!}"
    logInfo m!"TYPE {name} = {info.type}"
