import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FixedFourierParameterGerm
import H0mework.Versions.R7e4da746.Arithmetic.RiemannBandResponse.ActionBand

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead

open BurnolPhysicalState MeasureTheory Filter Set
open scoped InnerProductSpace

local notation "D" => burnolMultiplicativeDilation
local notation "K" => burnolCompletedMellinRieszVector
local notation "F" => fourierL2
local notation "seed" => (burnolPaCombApproximation 0:BurnolL2)

/-- The time window is paid by the margin of the original compact comb band. -/
def combDelay : ℝ := 2 * Real.log 2

theorem combDelay_pos : 0 < combDelay :=
  mul_pos (by norm_num) (Real.log_pos (by norm_num))

/-- Actual inward transport stays in the original infinite Pa during the first band window. -/
theorem actual_comb_delay (anchor : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta anchor.value = 0) {t : ℝ} (inside : t ∈ Icc 0 combDelay) :
    inner ℂ (F (K anchor:BurnolL2)) (D (-t/2) seed) = 0 := by
  have small : |t/2| ≤ Real.log 2 := by
    rw [abs_of_nonneg (by linarith [inside.1])]
    have upper := inside.2
    unfold combDelay at upper
    linarith
  obtain ⟨w, member, transported⟩ := Submodule.mem_map.mp
    (burnolPaInteriorBand_dilation_mem (3/2) (t/2) (by norm_num) le_rfl small)
  have width : 1+burnolPaCombSourceWidth 0 = (3/2:ℝ) := by norm_num [burnolPaCombSourceWidth]
  rw [burnolPaCombApproximation_raw, width, map_smul, show -t/2 = -(t/2) by ring,
    ← fourierL2_burnolMultiplicativeDilation, ← transported, inner_smul_right]
  simp only [Nat.cast_zero, zero_add, fourierL2.inner_map_map]
  have gone : inner ℂ (K anchor:BurnolL2) (w:BurnolL2) = 0 :=
    inner_eq_zero_symm.mp ((riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal anchor zero) _ member)
  simp [gone]

private def rightWeightRead (anchor : BurnolCompletedMellinCoordinate) (w : ℂ) (t : ℝ) : ℂ :=
  inner ℂ (F (K anchor:BurnolL2)) (burnolDirectRightResolventIntegrand w seed t)

def delayBudget (anchor : BurnolCompletedMellinCoordinate) : ℝ :=
  ∫ t in Ioi combDelay, ‖rightWeightRead anchor (anchor.value/2) t‖

theorem delayBudget_nonneg (anchor : BurnolCompletedMellinCoordinate) : 0 ≤ delayBudget anchor :=
  integral_nonneg fun _ => norm_nonneg _

private theorem right_read_integrable (anchor : BurnolCompletedMellinCoordinate)
    (w : ℂ) (right : (1/4:ℝ) < w.re) : IntegrableOn (rightWeightRead anchor w) (Ioi (0:ℝ)) :=
  (innerSL ℂ (F (K anchor:BurnolL2))).integrable_comp
    (burnolDirectRightResolventIntegrand_integrableOn w right seed)

private theorem original_price_as_delayed (anchor : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta anchor.value = 0) (w : ℂ) (right : (1/4:ℝ) < w.re) :
    inner ℂ (F (K anchor:BurnolL2)) (burnolDirectRightResolvent w seed) =
      -∫ t in Ioi combDelay, rightWeightRead anchor w t := by
  let read := innerSL ℂ (F (K anchor:BurnolL2))
  change read (burnolDirectRightResolvent w seed) = _
  rw [burnolDirectRightResolvent, map_neg, ← read.integral_comp_comm
    (burnolDirectRightResolventIntegrand_integrableOn w right seed)]
  change -(∫ t in Ioi (0:ℝ), rightWeightRead anchor w t) = _
  have ing := right_read_integrable anchor w right
  have disjoint : Disjoint (Ioc (0:ℝ) combDelay) (Ioi combDelay) :=
    Set.disjoint_left.mpr (fun _ lower upper => (not_lt_of_ge lower.2) upper)
  have tail : Ioi combDelay ⊆ Ioi (0:ℝ) := fun _ h => combDelay_pos.trans h
  have split := setIntegral_union disjoint measurableSet_Ioi (ing.mono_set Ioc_subset_Ioi_self)
    (ing.mono_set tail)
  rw [Ioc_union_Ioi_eq_Ioi combDelay_pos.le] at split
  have empty : (∫ t in Ioc (0:ℝ) combDelay, rightWeightRead anchor w t) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    rw [rightWeightRead, burnolDirectRightResolventIntegrand, inner_smul_right,
      actual_comb_delay anchor zero ⟨ht.1.le,ht.2⟩, mul_zero]
  rw [split, empty, zero_add]

private theorem read_weight_shift (anchor : BurnolCompletedMellinCoordinate) (x t : ℝ) :
    ‖rightWeightRead anchor (anchor.value/2+(x:ℂ)) t‖ =
      Real.exp (-x*t) * ‖rightWeightRead anchor (anchor.value/2) t‖ := by
  simp only [rightWeightRead, burnolDirectRightResolventIntegrand, inner_smul_right,
    norm_mul, norm_positiveMellinQuarterRightResolventWeight]
  rw [← mul_assoc, ← Real.exp_add]
  simp only [Complex.add_re, Complex.ofReal_re]
  congr 2
  ring

/-- The fixed original price has a source-generated exponential bound on its rightward ray. -/
theorem actual_delayed_rightward_price (anchor : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta anchor.value = 0) {x : ℝ} (nonnegative : 0 ≤ x) :
    ‖inner ℂ (F (K anchor:BurnolL2)) (burnolDirectRightResolvent (anchor.value/2+(x:ℂ)) seed)‖ ≤
      Real.exp (-x*combDelay) * delayBudget anchor := by
  have right : (1/4:ℝ)<(anchor.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [anchor.rightHalf]
  have shifted : (1/4:ℝ)<(anchor.value/2+(x:ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  rw [original_price_as_delayed anchor zero _ shifted, norm_neg]
  apply (norm_integral_le_integral_norm _).trans
  have tail : Ioi combDelay ⊆ Ioi (0:ℝ) := fun _ h => combDelay_pos.trans h
  have reference := ((right_read_integrable anchor _ right).mono_set tail).norm
  unfold delayBudget
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
    (reference.const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [read_weight_shift]
  exact mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht.le (neg_nonpos.mpr nonnegative))) (norm_nonneg _)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
