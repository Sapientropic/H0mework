import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceMasterSimpleNumerator
import Lean
set_option autoImplicit false
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (text, owner) in [("LowEnergy.PreparationPhysicalJointRadialForcing.spatial_positive", "H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceJointRadialSpatialReturn"), ("LowEnergy.PreparationPhysicalJointRadialForcing.physical_price_shape", "H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceJointRadialPrice")] do
    let wanted := text.toName
    let candidates := env.constants.toList.filter fun (name, _) => privateToUserName name == wanted
    logInfo m!"ALL {wanted}: {candidates.map Prod.fst}"
    let exact := candidates.filter fun (name, _) => name.toString.startsWith ("_private." ++ owner ++ ".")
    unless exact.length == 1 do throwError "Expected one actual producer {owner}: {exact.map Prod.fst}"
    let (name, info) := exact[0]!
    let some index := env.getModuleIdxFor? name | throwError "No module for {name}"
    unless env.header.moduleNames[index]!.toString == owner do throwError "Wrong module {name}"
    unless (info.value? true).isSome do throwError "No checked value {name}"
    logInfo m!"OWNER {wanted} = {name} MODULE {env.header.moduleNames[index]!}"
    logInfo m!"TYPE {name} = {info.type}"
