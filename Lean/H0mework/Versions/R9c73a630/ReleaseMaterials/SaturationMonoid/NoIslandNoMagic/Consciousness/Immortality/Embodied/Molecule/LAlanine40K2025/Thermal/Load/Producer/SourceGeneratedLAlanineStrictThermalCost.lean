import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer.EnvironmentHeat
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Quantum.StrictGibbsBound

/-! # Source-clock heat and strictly paid thermodynamic cost -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Source
open StrictThermal
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The actual first load action has a strictly positive, source-clock-sized heat output. -/
theorem loadFirst_strictHeat :
    (Propagation.Producer.nativeClockStep : ℝ) ^ 2 / 4 <
      environmentEnergy (loadStateNext loadInitialState).joint - environmentEnergy loadInitialState.joint := by
  have incoming : 11 / 8 < Powered.Dynamics.controllerEnergy 2 loadParentCurrent.joint -
      Powered.Dynamics.controllerEnergy 2 (Matrix.kronecker loadParentCurrent.joint environmentState) := by
    have exactGap := loadInitial_energyImbalance_lower
    rw [loadInitialState_received] at exactGap
    exact exactGap
  have generated := HeatProbability.environment_heat_lower_of_quarter_error
    loadParentCurrent.joint loadParentCurrent.positive loadParentCurrent.normalized
    (loadInteractionPicture (Propagation.Producer.nativeClockStep : ℝ))
    (Propagation.Producer.nativeClockStep : ℝ) nativeClock_small.1
    loadInteractionPicture_actual_error incoming
  rw [loadInteractionPicture_energy] at generated
  rw [loadStateNext_joint, loadInitialState_received]
  exact generated

theorem loadFirst_environment_changed :
    environmentEnergy (loadStateNext loadInitialState).joint ≠ environmentEnergy loadInitialState.joint := by
  have positiveClockSquare : 0 < (Propagation.Producer.nativeClockStep : ℝ) ^ 2 / 4 := by
    have positiveClock := nativeClock_small.1
    positivity
  exact (sub_pos.mp (positiveClockSquare.trans loadFirst_strictHeat)).ne'

theorem loadFirst_strictGibbsCost : 0 < loadGibbsExcess (loadStateNext loadInitialState) :=
  loadGibbsExcess_pos_of_environment_changed _ loadFirst_environment_changed

theorem loadFirst_strictEntropyCost : 0 < loadEntropyProduction (loadStateNext loadInitialState) :=
  loadEntropy_pos_of_environment_changed _ loadFirst_environment_changed

theorem loadFirst_strictFreeEnergyDebit :
    0 < loadBindingAccountedFreeEnergy loadInitialState -
      loadBindingAccountedFreeEnergy (loadStateNext loadInitialState) := by
  rw [← loadFirst_entropy_paid]
  exact loadFirst_strictEntropyCost

theorem loadFirst_sourceGeneratedThermodynamicCost :
    type_of% loadFirst_strictHeat ∧ type_of% loadFirst_strictGibbsCost ∧
      type_of% loadFirst_strictEntropyCost ∧ type_of% loadFirst_strictFreeEnergyDebit :=
  ⟨loadFirst_strictHeat, loadFirst_strictGibbsCost, loadFirst_strictEntropyCost, loadFirst_strictFreeEnergyDebit⟩

end

end LAlanine40K2025.Thermal.Load.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
