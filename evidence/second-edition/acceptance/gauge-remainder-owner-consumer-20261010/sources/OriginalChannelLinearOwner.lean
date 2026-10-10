import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedStaticLaurent
import Lean
set_option autoImplicit false
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let wanted := `LowEnergy.PreparationVacuumChargedLongRangeRead.linear_matrix
  let owner := "H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceChargedStaticLaurent"
  let candidates := env.constants.toList.filter fun (name, _) => privateToUserName name == wanted
  logInfo m!"ALL {wanted}: {candidates.map Prod.fst}"
  let exact := candidates.filter fun (name, _) => name.toString.startsWith ("_private." ++ owner ++ ".")
  unless exact.length == 1 do throwError "Expected one actual canonical producer: {exact.map Prod.fst}"
  let (name, info) := exact[0]!
  let some index := env.getModuleIdxFor? name | throwError "No checked module for {name}"
  unless env.header.moduleNames[index]!.toString == owner do throwError "Wrong owner for {name}"
  let some value := info.value? true | throwError "No checked value for {name}"
  logInfo m!"OWNER {name} MODULE {env.header.moduleNames[index]!}"
  logInfo m!"TYPE {name} = {info.type}"
  logInfo m!"VALUE {name} = {value}"
