import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRCorrectionActionSource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtROutsideCorrectionNonzeroSource
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalRieszSource
open OriginalKPairedBEulerJunctionSource

open private source_inner_continuousOn source_outer_continuousOn
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource
open private source_norm_strict observation_kernel_source_nonzero
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerSource
open private correction_B
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRCorrectionActionSource
open private firstMap
  from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandFullStockAction

local notation "q" => (1 / 4 : ℝ)
local notation "p" => junctionPoint
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier

private theorem source_jump_zero_of_correction_zero (c : BurnolCompletedMellinCoordinate)
    (i : Fin 2) (zero : sourceCorrection c i = 0) : sourceJump c i = 0 := by
  have zeroLp : (sourceCorrection c i : Hq) = 0 :=
    congrArg (fun value : M => (value : Hq)) zero
  have rawZero : sourceRaw c i =ᵐ[volume.restrict (symmetricInterval q)] (fun _ => (0 : ℂ)) :=
    (source_correction_read c i).symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp zeroLp)
  have leftSubset : Icc 0 p ⊆ symmetricInterval q := by
    intro x hx
    change -q ≤ x ∧ x ≤ q
    constructor <;> linarith [hx.1, hx.2, junctionPoint_bounds.2]
  have rightSubset : Icc p q ⊆ symmetricInterval q := by
    intro x hx
    change -q ≤ x ∧ x ≤ q
    exact ⟨by linarith [hx.1, junctionPoint_bounds.1], hx.2⟩
  have leftRead : sourceInnerRaw c i =ᵐ[volume.restrict (Icc 0 p)] (fun _ => (0 : ℂ)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset leftSubset rawZero,
      ae_restrict_mem measurableSet_Icc] with x zero hx
    simpa only [sourceRaw, abs_of_nonneg hx.1, if_pos hx.2] using zero
  have rightRead : sourceOuterRaw c i =ᵐ[volume.restrict (Icc p q)] (fun _ => (0 : ℂ)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset rightSubset rawZero,
      ae_restrict_of_ae (volume.ae_ne p), ae_restrict_mem measurableSet_Icc] with x zero ne hx
    have pos : 0 ≤ x := junctionPoint_bounds.1.le.trans hx.1
    have outside : ¬x ≤ p := not_le.mpr (lt_of_le_of_ne hx.1 ne.symm)
    simpa only [sourceRaw, abs_of_nonneg pos, if_neg outside] using zero
  have left := Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt junctionPoint_bounds.1)
    leftRead (source_inner_continuousOn c i) continuousOn_const
  have right := Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt junctionPoint_bounds.2)
    rightRead (source_outer_continuousOn c i) continuousOn_const
  rw [←source_internal_jump, left ⟨junctionPoint_bounds.1.le, le_rfl⟩,
    right ⟨le_rfl, junctionPoint_bounds.2.le⟩, sub_self]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

theorem original_A_ne_zero : Kernel.A c ≠ 0 := by
  have native := observation_kernel_source_nonzero observation nontrivial half.down
  have strict := source_norm_strict c native
  intro zero
  rw [zero, norm_zero] at strict
  exact (not_lt_of_ge (norm_nonneg _)) strict

/-- The fixed paired source retains the original K jump before any physical projection. -/
theorem original_sourceJump_ne_zero : sourceJump c 0 ≠ 0 := by
  change (Real.exp (junctionShift / 2) : ℂ) / 2 * (-Kernel.A c) ≠ 0
  exact mul_ne_zero (div_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) (by norm_num))
    (neg_ne_zero.mpr (original_A_ne_zero observation nontrivial half))

theorem original_sourceFirst_ne_zero : sourceFirst c ≠ 0 := by
  intro zero
  have first : sourceCorrection c 0 = 0 := zero
  exact original_sourceJump_ne_zero observation nontrivial half
    (source_jump_zero_of_correction_zero c 0 first)

/-- The complete correction retains its first B foot, so the two legs cannot erase the source jump. -/
theorem original_correction_ne_zero : BandFullStockEuler.correctionRaw c ≠ 0 := by
  intro zero
  have first := (correction_B c).1
  change firstMap (BandFullStockEuler.correctionRaw c) = sourceFirst c at first
  rw [zero, map_zero] at first
  exact original_sourceFirst_ne_zero observation nontrivial half first.symm

end OriginalWholeDebtROutsideCorrectionNonzeroSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
