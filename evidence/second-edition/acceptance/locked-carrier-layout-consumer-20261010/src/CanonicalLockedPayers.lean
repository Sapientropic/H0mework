import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceBackgroundLockedDirection
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceLockedFieldReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMOriginFields
import Lean
set_option autoImplicit false
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (text, owner) in [("LowEnergy.PreparationVacuumPhysicalElectromagneticDirection.sourceRestLockedMixing", "H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceLockedPoleCurrent"), ("LowEnergy.PreparationVacuumPhysicalElectromagneticDirection.actualRestState_locked_current", "H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceLockedPoleCurrent"), ("LowEnergy.PreparationVacuumPhysicalElectromagneticDirection.sourceLockedField", "H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceLockedFieldReturn"), ("LowEnergy.PreparationVacuumPhysicalElectromagneticDirection.sourceLockedField_lorentz", "H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceLockedFieldReturn"), ("LowEnergy.PreparationVacuumPhysicalElectromagneticDirection.sourceLockedField_connection", "H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceLockedFieldReturn")] do
    let name := text.toName
    let some info := env.find? name | throwError "Missing original payer {name}"
    let some index := env.getModuleIdxFor? name | throwError "Missing owner {name}"
    unless env.header.moduleNames[index]!.toString == owner do throwError "Wrong owner {name}"
    unless (info.value? true).isSome do throwError "Missing original value {name}"
    logInfo m!"OWNER {name} = {env.header.moduleNames[index]!}"
    logInfo m!"TYPE {name} = {info.type}"
