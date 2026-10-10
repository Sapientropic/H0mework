import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeDiracRay
import Lean
set_option autoImplicit false
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for text in ["LowEnergy.SourcePropagationNativeActionHessian.instNormedAddCommGroupLorentzianCoframe_1", "LowEnergy.SourcePropagationNativeActionHessian.instSeminormedAddCommGroupLorentzianCoframe_1", "LowEnergy.SourcePropagationNativeActionHessian.instNormedSpaceRealLorentzianCoframe_1"] do
    let name := (text.splitOn ".").foldl Name.str .anonymous
    let some constant := env.find? name | throwError "Missing constant {name}"
    let some index := env.getModuleIdxFor? name | throwError "Missing owner {name}"
    logInfo m!"OWNER {name} = {env.header.moduleNames[index]!}"
    logInfo m!"TYPE {name} = {constant.type}"
