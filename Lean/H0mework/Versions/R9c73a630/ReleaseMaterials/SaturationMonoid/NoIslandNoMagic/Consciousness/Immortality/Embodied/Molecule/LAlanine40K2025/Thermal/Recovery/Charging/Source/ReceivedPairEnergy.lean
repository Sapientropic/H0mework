import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Charging.Source.GramEnergyUpper
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Refill.Producer.SourceRaisingMoment
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Producer.SourceGeneratedLAlanineRecovery

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Charging.PairEnergy

open Collision Propagation.Interface Propagation.Producer
open Load.Producer.StrictThermal Load.Producer.HeatProbability
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Dynamics
noncomputable section
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

theorem source_bare_pair_energy :
    energy (jointHamiltonian Thermal.Source.energyHamiltonian) Thermal.Producer.generatedJoint =
      energy Thermal.Source.energyHamiltonian Thermal.Source.systemCurrent +
        energy Thermal.Source.energyHamiltonian Thermal.Source.bathCurrent := by
  rw [Quantum.jointEnergy_real_eq_reduced]
  exact reducedEnergy_conserved _ _ _ _ _ Thermal.Source.exchange_normalized
    Thermal.Source.systemCurrent_trace Thermal.Source.bathCurrent_trace

theorem source_before_field_energy_lt :
    energy Work.Drive.fieldBaseline Work.Drive.sourceFieldCycleCurrent < -10 := by
  change energy (pairH Thermal.Source.energyHamiltonian Thermal.Source.pairCoupling)
    (Thermal.Producer.rememberedJoint _) < -10
  rw [Thermal.Producer.rememberedPair_totalEnergy, Thermal.Producer.couplingSetup_disposition,
    source_bare_pair_energy]
  have swapBound : Thermal.Producer.couplingSetupEnergy ≤ 1 := by
    apply (le_abs_self _).trans ((energy_abs_le_norm _ _ Thermal.Producer.generatedJoint_posSemidef
      Thermal.Producer.generatedJoint_trace).trans _)
    change ‖(1 : ℂ) • (swapOperator : JointMatrix Basis)‖ ≤ 1
    rw [one_smul, swap_norm]
  linarith [SourceBounds.source_system_mean_lt_two, GibbsEnergy.source_bath_mean_lt_neg_thirteen]

theorem source_field_work_upper : Work.Drive.fieldCycleWork Work.Drive.sourceFieldCycleCurrent ≤ 4 / 5 := by
  let oldH := pairH Thermal.Source.energyHamiltonian Thermal.Source.pairCoupling
  let offH := pairH Work.Drive.fieldOffHamiltonian Thermal.Source.pairCoupling
  have first : Work.Drive.fieldCycleOffWork Work.Drive.sourceFieldCycleCurrent ≤ 2 / 5 := by
    change energy offH _ - energy oldH _ ≤ _
    rw [← energy_sub_left]
    exact (le_abs_self _).trans ((energy_abs_le_norm _ _
      Work.Drive.sourceFieldCycleCurrent_positive_normalized.1
      Work.Drive.sourceFieldCycleCurrent_positive_normalized.2).trans SourceMoment.source_pair_difference_norm)
  have second : Work.Drive.fieldCycleOnWork Work.Drive.sourceFieldCycleCurrent ≤ 2 / 5 := by
    change energy oldH Work.Drive.sourceFieldCycleTarget - energy offH Work.Drive.sourceFieldCycleTarget ≤ _
    rw [← energy_sub_left]
    apply (le_abs_self _).trans ((energy_abs_le_norm _ _
      Work.Drive.sourceFieldCycleTarget_positive_normalized.1
      Work.Drive.sourceFieldCycleTarget_positive_normalized.2).trans _)
    rw [norm_sub_rev oldH offH]
    exact SourceMoment.source_pair_difference_norm
  change Work.Drive.fieldCycleOffWork _ + Work.Drive.fieldCycleOnWork _ ≤ _
  linarith

theorem source_received_pair_energy_lt :
    energy Work.Drive.fieldBaseline Powered.Producer.sourceReceivedPair < -(46 / 5 : ℝ) := by
  rw [Powered.Producer.sourceReceivedPair_eq_fieldTarget]
  have balance := Work.Drive.fieldCycle_workBalance Work.Drive.sourceFieldCycleCurrent
  change Work.Drive.fieldCycleWork Work.Drive.sourceFieldCycleCurrent =
    energy Work.Drive.fieldBaseline Work.Drive.sourceFieldCycleTarget -
      energy Work.Drive.fieldBaseline Work.Drive.sourceFieldCycleCurrent at balance
  linarith [source_before_field_energy_lt, source_field_work_upper]

end
end LAlanine40K2025.Thermal.Recovery.Charging.PairEnergy
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
