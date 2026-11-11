import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusTailGrowthSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusStrictSource
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusTemperedSource
open Complex MeasureTheory Set Filter FourierTransform BurnolPhysicalState OriginalRieszSource
open scoped Topology InnerProductSpace BigOperators ArithmeticFunction
local notation "q" => (1 / 4 : ℝ)
open private source_measurable from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusTailGrowthSource

/-- This decaying weight only qualifies an unchanged polynomially bounded raw. -/
def sourcePolynomial (x : ℝ) : ℂ := ((1 + x ^ 2 : ℝ) : ℂ) ^ 2

def weightedRaw (raw : ℝ → ℂ) (x : ℝ) : ℂ := raw x / sourcePolynomial x

private theorem polynomial_norm (x : ℝ) : ‖sourcePolynomial x‖ = (1 + x ^ 2) ^ 2 := by
  unfold sourcePolynomial
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

private theorem weighted_bound (raw : ℝ → ℂ) (C : ℝ) (_nonnegative : 0 ≤ C)
    (bound : ∀ x : ℝ, ‖raw x‖ ≤ C * (1 + x ^ 2)) (x : ℝ) :
    ‖weightedRaw raw x‖ ≤ C * (1 + x ^ 2)⁻¹ := by
  have denominator : 0 < 1 + x ^ 2 := by positivity
  unfold weightedRaw
  rw [norm_div, polynomial_norm]
  apply (div_le_iff₀ (sq_pos_of_pos denominator)).mpr
  have cancel : C * (1 + x ^ 2)⁻¹ * (1 + x ^ 2) ^ 2 = C * (1 + x ^ 2) := by field_simp
  rw [cancel]
  exact bound x

private theorem qualified_memLp (raw : ℝ → ℂ)
    (measured : AEStronglyMeasurable raw volume)
    (growth : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖raw x‖ ≤ C * (1 + x ^ 2)) :
    MemLp (weightedRaw raw) 2 volume := by
  obtain ⟨C, nonnegative, bound⟩ := growth
  have inverse : AEStronglyMeasurable (fun x : ℝ => (sourcePolynomial x)⁻¹) volume := by
    apply Measurable.aestronglyMeasurable
    unfold sourcePolynomial
    fun_prop
  have weightedMeasured : AEStronglyMeasurable (weightedRaw raw) volume := by
    change AEStronglyMeasurable (fun x : ℝ => raw x / sourcePolynomial x) volume
    simpa only [div_eq_mul_inv, Pi.mul_def] using measured.mul inverse
  have integrable : Integrable (weightedRaw raw) volume :=
    (integrable_inv_one_add_sq.const_mul C).mono' weightedMeasured
      (Eventually.of_forall (weighted_bound raw C nonnegative bound))
  have bounded (x : ℝ) : ‖weightedRaw raw x‖ ≤ C := by
    have inverse : (1 + x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
    exact (weighted_bound raw C nonnegative bound x).trans (by nlinarith)
  apply (memLp_two_iff_integrable_sq_norm weightedMeasured).mpr
  exact (integrable.norm.const_mul C).mono'
    (by fun_prop) (Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [bounded x, norm_nonneg (weightedRaw raw x)]))

private def qualifiedDistribution (raw : ℝ → ℂ)
    (measured : AEStronglyMeasurable raw volume)
    (growth : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖raw x‖ ≤ C * (1 + x ^ 2)) : TemperedDistribution ℝ ℂ :=
  TemperedDistribution.smulLeftCLM ℂ sourcePolynomial
    (Lp.toTemperedDistributionCLM ℂ volume 2 ((qualified_memLp raw measured growth).toLp (weightedRaw raw)))

private theorem qualified_distribution_read (raw : ℝ → ℂ)
    (measured : AEStronglyMeasurable raw volume)
    (growth : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖raw x‖ ≤ C * (1 + x ^ 2))
    (test : SchwartzMap ℝ ℂ) :
    qualifiedDistribution raw measured growth test = ∫ x : ℝ, test x * raw x := by
  have polynomial : sourcePolynomial.HasTemperateGrowth := by unfold sourcePolynomial; fun_prop
  unfold qualifiedDistribution
  rw [TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistributionCLM_apply,
    Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(qualified_memLp raw measured growth).coeFn_toLp] with x actual
  rw [SchwartzMap.smulLeftCLM_apply_apply polynomial, actual]
  change (sourcePolynomial x * test x) * weightedRaw raw x = _
  have nonzero : sourcePolynomial x ≠ 0 := by
    unfold sourcePolynomial
    exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (by positivity : (1 + x ^ 2 : ℝ) ≠ 0))
  unfold weightedRaw
  field_simp

private theorem source_quadratic_growth (c : BurnolCompletedMellinCoordinate) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖U.sourceRaw c x‖ ≤ C * (1 + x ^ 2) := by
  obtain ⟨C, nonnegative, bound⟩ := actual_source_growth c
  refine ⟨2 * C, by positivity, fun x => (bound x).trans ?_⟩
  have size : 1 + |x| ≤ 2 * (1 + x ^ 2) := by nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  nlinarith

def weightedSourceRaw (c : BurnolCompletedMellinCoordinate) : ℝ → ℂ := weightedRaw (U.sourceRaw c)

theorem actual_weighted_source_memLp (c : BurnolCompletedMellinCoordinate) :
    MemLp (weightedSourceRaw c) 2 volume := qualified_memLp _ (source_measurable c) (source_quadratic_growth c)

/-- The actual full inverse source is independently qualified on the existing distribution carrier. -/
def sourceDistribution (c : BurnolCompletedMellinCoordinate) : TemperedDistribution ℝ ℂ :=
  qualifiedDistribution (U.sourceRaw c) (source_measurable c) (source_quadratic_growth c)

theorem actual_source_distribution (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    sourceDistribution c test = ∫ x : ℝ, test x * U.sourceRaw c x :=
  qualified_distribution_read _ _ _ test

open private forward_cut from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusProgrammeSource

private theorem forward_measurable (c : BurnolCompletedMellinCoordinate) :
    AEStronglyMeasurable (burnolInnerGapForward (U.sourceRaw c)) volume := by
  apply AEMeasurable.aestronglyMeasurable
  unfold burnolInnerGapForward
  apply AEMeasurable.tsum
  intro n
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => x / (n : ℕ)) volume volume := by
    simpa only [div_eq_mul_inv, smul_eq_mul, mul_comm] using
      Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := ((n : ℕ) : ℝ)⁻¹) (inv_ne_zero (by exact_mod_cast n.ne_zero))
  exact ((source_measurable c).comp_quasiMeasurePreserving qmp).aemeasurable.const_mul (((n : ℕ) : ℂ)⁻¹)

private theorem forward_quadratic_growth (c : BurnolCompletedMellinCoordinate) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖burnolInnerGapForward (U.sourceRaw c) x‖ ≤ C * (1 + x ^ 2) := by
  classical
  obtain ⟨C, nonnegative, bound⟩ := actual_source_growth c
  refine ⟨8 * C, by positivity, ?_⟩
  intro x
  have gap : ∀ {x : ℝ}, |x| ≤ q → U.sourceRaw c x = 0 :=
    fun inside => OriginalWholeDebtRJointMobiusUnitSource.actual_source_zero_window c (by linarith)
  rw [forward_cut _ gap]
  have summand (n : ℕ+) : ‖(((n : ℕ) : ℂ)⁻¹) * U.sourceRaw c (x / (n : ℕ))‖ ≤ C * (1 + |x|) := by
    have np : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
    have one : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.pos
    have argument : |x / (n : ℕ)| ≤ |x| := by
      rw [abs_div, abs_of_pos np]
      exact div_le_self (abs_nonneg _) one
    have denominator : ‖(((n : ℕ) : ℂ)⁻¹)‖ ≤ 1 := by
      rw [norm_inv, Complex.norm_natCast]
      exact inv_le_one_of_one_le₀ one
    rw [norm_mul]
    calc
      _ ≤ 1 * (C * (1 + |x / (n : ℕ)|)) := by gcongr; exact bound _
      _ ≤ C * (1 + |x|) := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left (by linarith : 1 + |x / (n : ℕ)| ≤ 1 + |x|) nonnegative
  have card : (burnolCenteredMobiusCutoffFinset x).card ≤ burnolCenteredMobiusCutoff x := by
    simpa only [Finset.card_range] using Finset.card_le_card_of_injOn
      (s := burnolCenteredMobiusCutoffFinset x) (t := Finset.range (burnolCenteredMobiusCutoff x))
      (fun n : ℕ+ => (n : ℕ))
      (fun n member => Finset.mem_range.mpr ((mem_burnolCenteredMobiusCutoffFinset x n).mp member))
      (Set.injOn_of_injective PNat.coe_injective)
  have natural : ((burnolCenteredMobiusCutoffFinset x).card : ℝ) ≤ (burnolCenteredMobiusCutoff x : ℝ) := by exact_mod_cast card
  have count : ((burnolCenteredMobiusCutoffFinset x).card : ℝ) ≤ 4 * |x| + 1 := natural.trans (by
    unfold burnolCenteredMobiusCutoff
    exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * |x|)).le)
  calc
    _ ≤ ∑ n ∈ burnolCenteredMobiusCutoffFinset x, ‖(((n : ℕ) : ℂ)⁻¹) * U.sourceRaw c (x / (n : ℕ))‖ := norm_sum_le _ _
    _ ≤ (burnolCenteredMobiusCutoffFinset x).card * (C * (1 + |x|)) := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        Finset.sum_le_sum (fun n (_ : n ∈ burnolCenteredMobiusCutoffFinset x) => summand n)
    _ ≤ (8 * C) * (1 + x ^ 2) := by
      have size : (4 * |x| + 1) * (1 + |x|) ≤ 8 * (1 + x ^ 2) := by
        nlinarith [sq_nonneg (|x| - 1), sq_abs x]
      have finite := mul_le_mul_of_nonneg_right count (by positivity : 0 ≤ C * (1 + |x|))
      have coarse := mul_le_mul_of_nonneg_left size nonnegative
      nlinarith

/-- The divisor action is generated from the raw source and growth, before an L² response is read. -/
def forwardDistribution (c : BurnolCompletedMellinCoordinate) : TemperedDistribution ℝ ℂ :=
  qualifiedDistribution (burnolInnerGapForward (U.sourceRaw c)) (forward_measurable c) (forward_quadratic_growth c)

theorem actual_forward_distribution (c : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    forwardDistribution c test = ∫ x : ℝ, test x * burnolInnerGapForward (U.sourceRaw c) x :=
  qualified_distribution_read _ _ _ test

/-- The original actual response is an independent consumer of the source-generated complete arithmetic action. -/
theorem actual_response_realization (c : BurnolCompletedMellinCoordinate) :
    forwardDistribution c = Lp.toTemperedDistributionCLM ℂ volume 2 (OriginalWholeDebtRJointMobiusUnitSource.response c) := by
  ext test
  rw [actual_forward_distribution, Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [OriginalWholeDebtRJointMobiusUnitSource.actual_raw c] with x actual
  rw [actual]
  rfl


theorem actual_fourier_response_realization (c : BurnolCompletedMellinCoordinate) :
    𝓕 (forwardDistribution c) = Lp.toTemperedDistributionCLM ℂ volume 2
      (fourierL2 (OriginalWholeDebtRJointMobiusUnitSource.response c)) := by
  rw [actual_response_realization, Lp.toTemperedDistributionCLM_apply, Lp.fourier_toTemperedDistribution_eq]
  rfl

/-- Both actual old means remain in the true whole unit payment before this generated action is consumed. -/
theorem actual_whole_unit_update (c : BurnolCompletedMellinCoordinate) :
    (OriginalWholeDebtRJointMobiusProgramme.outsideResponse c : TemperedDistribution ℝ ℂ) =
      U.unitCoefficient c • (burnolUnitTailResponse c 4 : TemperedDistribution ℝ ℂ) + forwardDistribution c := by
  have update := congrArg (Lp.toTemperedDistributionCLM ℂ volume 2)
    (OriginalWholeDebtRJointMobiusUnitSource.actual_source_update c)
  rw [map_add, map_smul, ← actual_response_realization] at update
  exact update

/-- The independent original source price detects the nonzero generated full arithmetic action. -/
theorem actual_forward_ne_zero (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (half : OriginalKCombCalculation.Half observation) :
    forwardDistribution (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) ≠ 0 := by
  let c := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
  intro zero
  have mapped : Lp.toTemperedDistributionCLM ℂ volume 2
      (OriginalWholeDebtRJointMobiusUnitSource.response c) = 0 :=
    (actual_response_realization c).symm.trans zero
  have kernel : OriginalWholeDebtRJointMobiusUnitSource.response c ∈
      (Lp.toTemperedDistributionCLM ℂ volume 2).ker := mapped
  rw [Lp.ker_toTemperedDistributionCLM_eq_bot] at kernel
  have valueZero : OriginalWholeDebtRJointMobiusUnitSource.response c = 0 := by simpa using kernel
  have price := OriginalWholeDebtRJointMobiusUnitSource.actual_programme_price observation nontrivial half
  rw [valueZero, inner_zero_right, neg_zero] at price
  exact OriginalWholeDebtRJointMobiusStrictSource.actual_programme_ne_zero observation nontrivial half price


end OriginalWholeDebtRJointMobiusTemperedSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
