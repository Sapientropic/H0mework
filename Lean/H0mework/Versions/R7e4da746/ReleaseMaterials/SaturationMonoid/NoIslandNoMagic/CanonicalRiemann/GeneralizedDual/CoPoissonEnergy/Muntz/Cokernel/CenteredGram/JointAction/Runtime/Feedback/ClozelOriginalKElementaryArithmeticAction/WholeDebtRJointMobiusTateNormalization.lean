import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusLocalNormalization
import H0mework.Versions.R7e4da746.Arithmetic.RemainderSource.RemainderKernel
import H0mework.Arithmetic.MellinTateSource.FourierPairing

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusTateNormalization
open Complex MeasureTheory Set Filter FourierTransform BurnolPhysicalState OriginalRieszSource
open scoped Topology InnerProductSpace BigOperators
namespace N
export OriginalWholeDebtRJointMobiusLocalNormalization
  (sourceKernel sourceKernelAction calculatedNormalization actual_q_normalization)
end N
namespace T
export OriginalWholeDebtRJointMobiusTemperedSource (actual_source_growth)
end T
namespace U
export OriginalWholeDebtRJointMobiusUnitSource (sourceRaw actual_source_zero_window)
end U
open private term term_bound from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusLocalNormalization
open private source_measurable from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusTailGrowthSource
open private remainder_fourier from H0mework.Versions.R7e4da746.Arithmetic.RemainderSource.RemainderKernel
open private integral_fourier_eq_zero_value from H0mework.Arithmetic.MellinTateSource.FourierPairing
local notation "q" => (1 / 4 : ℝ)

def tateSourceRaw (c : BurnolCompletedMellinCoordinate) : ℝ → ℂ := burnolTateReciprocalRaw (U.sourceRaw c)
/-- The zero contact belongs to the same integer-comb kernel; it cannot be split from the mean at t=0. -/
def tateKernel (test : SchwartzMap ℝ ℂ) (t : ℝ) : ℂ := coPoissonMuntzScaleRemainder test t + test 0

private theorem kernel_summable (test : SchwartzMap ℝ ℂ) {u : ℝ} (nonzero : u ≠ 0) :
    Summable (fun n : ℕ+ => test ((n : ℝ) * u)) := by
  have all := summable_integer_evaluation
    (ClozelEndpointSourceEffect.scaledSchwartzTest u nonzero test)
  have injective : Function.Injective (fun n : ℕ+ => ((n : ℕ) : ℤ)) := by
    intro left right same
    exact PNat.coe_injective (Int.ofNat_inj.mp same)
  simpa only [Function.comp_def, ClozelEndpointSourceEffect.scaledSchwartzTest_apply,
    Int.cast_natCast, mul_comm] using all.comp_injective injective

private theorem theta_pair (test : SchwartzMap ℝ ℂ) {u : ℝ} (positive : 0 < u) :
    N.sourceKernel test u + N.sourceKernel test (-u) = coPoissonMuntzThetaNonzero test u := by
  unfold OriginalWholeDebtRJointMobiusLocalNormalization.sourceKernel
  rw [← (kernel_summable test positive.ne').tsum_add (kernel_summable test (neg_ne_zero.mpr positive.ne')),
    coPoissonMuntzThetaNonzero_eq_positive_tsum test positive.ne']
  have reindex := tsum_pnat_eq_tsum_succ (f := fun n : ℕ => test ((n : ℝ) * u) + test (-((n : ℝ) * u)))
  calc
    _ = ∑' n : ℕ+, (test ((n : ℝ) * u) + test (-((n : ℝ) * u))) := by
      apply tsum_congr
      intro n
      rw [mul_neg]
    _ = ∑' n : ℕ, (test (((n + 1 : ℕ) : ℝ) * u) + test (-(((n + 1 : ℕ) : ℝ) * u))) := reindex
    _ = _ := by rfl

/-- Actual Poisson keeps the zero mode together with the full original mean subtraction. -/
theorem actual_tate_kernel (test : SchwartzMap ℝ ℂ) {u : ℝ} (positive : 0 < u) :
    N.sourceKernel (𝓕 test) u + N.sourceKernel (𝓕 test) (-u) =
      (u : ℂ)⁻¹ * tateKernel test u⁻¹ := by
  have original := coPoissonMuntzScaleRemainder_eq (𝓕 test) positive
  rw [← theta_pair (𝓕 test) positive, integral_fourier_eq_zero_value test] at original
  have reciprocal := remainder_fourier test positive
  rw [reciprocal] at original
  simp only [Complex.real_smul, Complex.ofReal_inv] at original
  unfold tateKernel
  linear_combination -original

private theorem source_even (c : BurnolCompletedMellinCoordinate) (x : ℝ) : U.sourceRaw c (-x) = U.sourceRaw c x := by
  have inverse : OriginalWholeDebtRJointMobiusProgramme.fullSourceRaw c (-x) =
      OriginalWholeDebtRJointMobiusProgramme.fullSourceRaw c x := by
    unfold OriginalWholeDebtRJointMobiusProgramme.fullSourceRaw burnolCenteredMobiusInverse
    apply tsum_congr
    intro n
    simp only [neg_div, OriginalWholeDebtRJointMobiusSource.jointRaw, abs_neg]
  by_cases small : |x| ≤ (4 : ℝ)
  · rw [U.actual_source_zero_window c (by simpa only [abs_neg] using small), U.actual_source_zero_window c small]
  have inside : x ∈ (symmetricInterval (4 : ℝ))ᶜ := by intro h; exact small (abs_le.mpr h)
  have negative : -x ∈ (symmetricInterval (4 : ℝ))ᶜ := by intro h; exact small (by simpa only [abs_neg] using abs_le.mpr h)
  unfold OriginalWholeDebtRJointMobiusUnitSource.sourceRaw OriginalWholeDebtRJointMobiusProgramme.outsideSourceRaw
  rw [indicator_of_mem inside, indicator_of_mem negative, inverse]
  simp only [OriginalWholeDebtRJointMobiusUnitSource.unitRaw, burnolRadiusUnitTailRaw, abs_neg]

private theorem kernel_product_integrable (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    Integrable (fun u : ℝ => U.sourceRaw c u * N.sourceKernel test u) volume := by
  obtain ⟨C, nonnegative, bound⟩ := T.actual_source_growth c
  have series : Summable (fun n : ℕ+ => ((n : ℝ) ^ 4)⁻¹) :=
    (Real.summable_nat_pow_inv.mpr (by decide : 1 < 4)).comp_injective PNat.coe_injective
  let B := 4 * C * SchwartzMap.seminorm ℂ 4 0 test
  have Bpos : 0 ≤ B := by dsimp only [B]; positivity
  have measured : AEStronglyMeasurable (fun u : ℝ => U.sourceRaw c u * N.sourceKernel test u) volume := by
    apply AEMeasurable.aestronglyMeasurable
    apply (source_measurable c).aemeasurable.mul
    exact AEMeasurable.tsum (fun n : ℕ+ => (test.continuous.comp (by fun_prop)).measurable.aemeasurable)
  apply (integrable_inv_one_add_sq.const_mul (B * ∑' n : ℕ+, ((n : ℝ) ^ 4)⁻¹)).mono' measured
  apply Eventually.of_forall
  intro u
  have majorant : Summable (fun n : ℕ+ => B * ((n : ℝ) ^ 4)⁻¹ * (1 + u ^ 2)⁻¹) :=
    (series.mul_left B).mul_right _
  have norms : Summable (fun n : ℕ+ => ‖term c test n u‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (term_bound c test C nonnegative bound · u) majorant
  have triangle : ‖U.sourceRaw c u * N.sourceKernel test u‖ ≤ ∑' n : ℕ+, ‖term c test n u‖ := by
    have same : U.sourceRaw c u * N.sourceKernel test u = ∑' n : ℕ+, term c test n u := by
      unfold OriginalWholeDebtRJointMobiusLocalNormalization.sourceKernel term
      exact (tsum_mul_left : _ = U.sourceRaw c u * ∑' n : ℕ+, test ((n : ℝ) * u)).symm
    rw [same]
    exact norm_tsum_le_tsum_norm norms
  have total := norms.tsum_le_tsum (term_bound c test C nonnegative bound · u) majorant
  rw [tsum_mul_right, tsum_mul_left] at total
  exact triangle.trans total

private def combinedForward (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) (u : ℝ) : ℂ :=
  U.sourceRaw c u * (N.sourceKernel (𝓕 test) u + N.sourceKernel (𝓕 test) (-u))

private theorem combined_integrable (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    Integrable (combinedForward c test) volume := by
  have original := kernel_product_integrable c (𝓕 test)
  have flipped := original.comp_neg
  have second : Integrable (fun u : ℝ => U.sourceRaw c u * N.sourceKernel (𝓕 test) (-u)) volume := by
    simpa only [source_even] using flipped
  change Integrable (fun u : ℝ => U.sourceRaw c u * (N.sourceKernel (𝓕 test) u + N.sourceKernel (𝓕 test) (-u))) volume
  simpa only [Pi.add_def, mul_add] using original.add second

private theorem combined_positive_integral (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    (∫ u : ℝ in Ioi 0, combinedForward c test u) = N.sourceKernelAction c (𝓕 test) := by
  have original := kernel_product_integrable c (𝓕 test)
  have flipped := original.comp_neg
  have second : Integrable (fun u : ℝ => U.sourceRaw c u * N.sourceKernel (𝓕 test) (-u)) volume := by
    simpa only [source_even] using flipped
  have changed : (∫ u : ℝ in Ioi 0, U.sourceRaw c u * N.sourceKernel (𝓕 test) (-u)) =
      ∫ u : ℝ in Iic 0, U.sourceRaw c u * N.sourceKernel (𝓕 test) u := by
    have actual := integral_comp_neg_Ioi 0 (fun u : ℝ => U.sourceRaw c u * N.sourceKernel (𝓕 test) u)
    simpa only [neg_zero, source_even] using actual
  unfold combinedForward
  simp_rw [mul_add]
  rw [integral_add original.integrableOn second.integrableOn, changed, add_comm]
  have whole := integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic original
  simpa only [compl_Iic, OriginalWholeDebtRJointMobiusLocalNormalization.sourceKernelAction] using whole

private theorem tate_pullback (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ)
    {t : ℝ} (positive : 0 < t) :
    tateSourceRaw c t * tateKernel test t =
      (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) • combinedForward c test (t ^ (-1 : ℝ)) := by
  have nonzero : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  have action := actual_tate_kernel test (inv_pos.mpr positive)
  rw [inv_inv] at action
  unfold tateSourceRaw burnolTateReciprocalRaw combinedForward
  rw [Real.rpow_neg_one, action]
  simp only [abs_of_pos positive, abs_neg, abs_one, one_mul, Complex.ofReal_inv, inv_inv, Complex.real_smul]
  rw [show ((-1 : ℝ) - 1) = -2 by norm_num, Real.rpow_neg positive.le, Real.rpow_two]
  push_cast
  field_simp

/-- The true Tate source acts on the whole zero-contact/mean kernel; both convergence and action are generated. -/
theorem actual_tate_action (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    IntegrableOn (fun t : ℝ => tateSourceRaw c t * tateKernel test t) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, tateSourceRaw c t * tateKernel test t) = N.sourceKernelAction c (𝓕 test) := by
  have native := (integrableOn_Ioi_comp_rpow_iff (combinedForward c test) (by norm_num : (-1 : ℝ) ≠ 0)).mpr
    (combined_integrable c test).integrableOn
  have read : (fun t : ℝ => tateSourceRaw c t * tateKernel test t) =ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ => (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) • combinedForward c test (t ^ (-1 : ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t positive
    exact tate_pullback c test positive
  refine ⟨native.congr read.symm, ?_⟩
  rw [integral_congr_ae read, integral_comp_rpow_Ioi (combinedForward c test) (by norm_num : (-1 : ℝ) ≠ 0),
    combined_positive_integral]

/-- The original q-normalization is the calculated counterterm of this actual Tate action. -/
theorem actual_tate_normalization (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (half : OriginalKCombCalculation.Half observation) (test : SchwartzMap ℝ ℂ)
    (supported : ∀ x : ℝ, q < |x| → test x = 0) :
    let c := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
    (∫ t : ℝ in Ioi 0, tateSourceRaw c t * (coPoissonMuntzScaleRemainder test t + test 0)) =
      N.calculatedNormalization c * (∫ x : ℝ, test x) := by
  change (∫ t : ℝ in Ioi 0, tateSourceRaw (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) t * tateKernel test t) = _
  rw [(actual_tate_action _ test).2]
  exact N.actual_q_normalization observation nontrivial half test supported

end OriginalWholeDebtRJointMobiusTateNormalization
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
