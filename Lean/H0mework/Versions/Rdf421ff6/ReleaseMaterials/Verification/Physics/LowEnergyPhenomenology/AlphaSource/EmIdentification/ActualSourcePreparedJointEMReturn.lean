import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMEnclosure
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedClockJointReturn

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedJointEMReturn
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumSourcePreparedState ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualSourcePreparedClockJointReturn ActualSourcePreparedEMEnclosure
open LowEnergy.ActualSourceQuantumCoefficientErrorOwn Filter
open scoped Topology

/-- The same generated preparation and positive physical observation curve pay
both normalized Ward error and all complete-field/EM window errors. Regularity
remains the original physical chart; this does not assert a limit of the reads. -/
theorem source_prepared_joint_em_return (event : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ) (damping : ℕ → ℝ)
    (positive : ∀k, 0 < damping k) (small : ∀k, damping k ≤ 2)
    (regular : ∀k, correctedDet
      (sourceClockWardRefinedEvent event epsilon (damping k) n branch sheet
        (preparationPrecision k) (preparationPrecision_positive k)) epsilon 0 (damping k) n ≠ 0) :
    let preparedEvent := fun k => sourceClockWardRefinedEvent event epsilon (damping k) n branch sheet
      (preparationPrecision k) (preparationPrecision_positive k)
    ∃bits : ℕ → ℕ,
      (∀k, 0 < sourceCommonDeterminantMargin (preparedEvent k) epsilon (damping k) n (bits k)) ∧
      (∀i j, Tendsto (fun k =>
        sourcePreparedFullGreenRead (preparedEvent k) epsilon (damping k) n i j-
          sourceFullGreenBinaryRead (preparedEvent k) epsilon (damping k) n (bits k) i j) atTop (𝓝 0)) ∧
      (∀mu nu, Tendsto (fun k =>
        sourcePreparedEMTensorRead (preparedEvent k) epsilon (damping k) n mu nu-
          sourceEMBinaryRead (preparedEvent k) epsilon (damping k) n (bits k) mu nu) atTop (𝓝 0)) ∧
      Tendsto (fun k => sourcePhysicalClockWardLowerRead (preparedEvent k)
        epsilon (damping k) n branch sheet) atTop (𝓝 0) := by
  dsimp only
  let preparedEvent := fun k => sourceClockWardRefinedEvent event epsilon (damping k) n branch sheet
    (preparationPrecision k) (preparationPrecision_positive k)
  let bits := fun k => sourcePreparedBinaryBits (preparedEvent k) epsilon (damping k) n
    (positive k) (small k) (regular k) (preparationPrecision k) (preparationPrecision_positive k)
  refine ⟨bits, ?_, ?_, ?_, ?_⟩
  · intro k
    exact (source_binary_generated_precision (preparedEvent k) epsilon (damping k) n
      (positive k) (small k) (regular k) (preparationPrecision k) (preparationPrecision_positive k)).1
  · intro i j
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    exact ((source_prepared_generated_enclosure (preparedEvent k) epsilon (damping k) n
      (positive k) (small k) (regular k) (preparationPrecision k) (preparationPrecision_positive k)).1 i j).le
  · intro mu nu
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    exact ((source_prepared_generated_enclosure (preparedEvent k) epsilon (damping k) n
      (positive k) (small k) (regular k) (preparationPrecision k) (preparationPrecision_positive k)).2 mu nu).le
  · exact (source_clock_joint_physical_return event epsilon n branch sheet damping positive).2

end LowEnergy.GaussComposite.ActualSourcePreparedJointEMReturn
