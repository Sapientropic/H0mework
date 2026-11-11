import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusRPrefixSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.Volterra.Raw

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusTateRSource
open Complex MeasureTheory Set Filter FourierTransform BurnolPhysicalState OriginalRieszSource
open OriginalKDirectRCofinalOutsideVolterraSource OriginalKCrossParameterRAdjointSource OriginalPaPhysicalGreen
open scoped Topology InnerProductSpace BigOperators
namespace U
export OriginalWholeDebtRJointMobiusUnitSource
  (sourceRaw responseRaw response actual_raw actual_source_zero_window actual_response_zero_window)
end U
namespace D
export OriginalWholeDebtRJointMobiusRActionSource (sourceInput sourceNext actual_complete_update)
end D
namespace T
export OriginalWholeDebtRJointMobiusTateNormalization (tateSourceRaw)
end T
open private source_measurable from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusTailGrowthSource
open private forward_cut from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusProgrammeSource
open private tail_tate_to_core from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCenteredMobiusRSource
open private quarter_read_of_source from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial
local notation "q" => (1 / 4 : ℝ)
local notation "F" => fourierL2

/-- The whole source receives the finite outward operation before either face is read. -/
def outwardRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  2 * ((|x| : ℝ) : ℂ) ^ (c.value - 1) *
    ∫ u : ℝ in (0 : ℝ)..|x|, (u : ℂ) ^ (-c.value) * U.sourceRaw c u

def tateOutwardRaw (c : BurnolCompletedMellinCoordinate) : ℝ → ℂ :=
  burnolTateReciprocalRaw (outwardRaw c)

def powerRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ((|x| : ℝ) : ℂ) ^ (c.value - 1)

/-- This foot is an actual original K action on the complete generated response. -/
def homogeneousCoefficient (c : BurnolCompletedMellinCoordinate) : ℂ :=
  -2 * inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2) (U.response c)

def actionRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  burnolInnerGapForward (outwardRaw c) x + homogeneousCoefficient c * powerRaw c x

private theorem source_local (c : BurnolCompletedMellinCoordinate) : LocallyIntegrable (U.sourceRaw c) volume := by
  obtain ⟨C, nonnegative, bound⟩ := OriginalWholeDebtRJointMobiusTemperedSource.actual_source_growth c
  rw [locallyIntegrable_iff]
  intro k compact
  obtain ⟨B, bounded⟩ := compact.exists_bound_of_continuousOn (show ContinuousOn (fun x : ℝ => |x|) k from continuous_abs.continuousOn)
  apply IntegrableOn.of_bound compact.measure_lt_top (source_measurable c).restrict (C * (1 + B))
  filter_upwards [ae_restrict_mem compact.measurableSet] with x inside
  have actualBound : |x| ≤ B := by simpa only [Real.norm_eq_abs, abs_abs] using bounded x inside
  exact (bound x).trans (mul_le_mul_of_nonneg_left (by linarith) nonnegative)

private theorem weighted_prefix (z : ℂ) (raw : ℝ → ℂ) (localRaw : LocallyIntegrable raw volume)
    (gap : ∀ {u : ℝ}, |u| ≤ q → raw u = 0) (x : ℝ) (positive : 0 < x) :
    IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ z * raw u) volume 0 x := by
  let safe : ℝ → ℂ := fun u => ((max q u : ℝ) : ℂ) ^ z
  have regular : Continuous safe := by
    have base : Continuous (fun u : ℝ => ((max q u : ℝ) : ℂ)) := Complex.continuous_ofReal.comp (continuous_const.max continuous_id)
    exact continuousOn_univ.mp (base.continuousOn.cpow_const (fun u _ =>
      Complex.ofReal_mem_slitPlane.mpr (lt_of_lt_of_le (by norm_num : (0 : ℝ) < q) (le_max_left q u))))
  have first : IntervalIntegrable raw volume 0 x := (localRaw.integrableOn_isCompact isCompact_Icc).intervalIntegrable
  apply (first.continuousOn_mul regular.continuousOn).congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with u inside
  have bounds : 0 ≤ u ∧ u ≤ x := by
    rw [uIoc_of_le positive.le] at inside
    exact ⟨inside.1.le, inside.2⟩
  by_cases small : u ≤ q
  · rw [gap (by rwa [abs_of_nonneg bounds.1]), mul_zero, mul_zero]
  · dsimp only [safe]
    rw [max_eq_right (le_of_not_ge small)]

theorem actual_outward_gap (c : BurnolCompletedMellinCoordinate) {x : ℝ} (inside : |x| ≤ (4 : ℝ)) : outwardRaw c x = 0 := by
  have zero : (∫ u : ℝ in (0 : ℝ)..|x|, (u : ℂ) ^ (-c.value) * U.sourceRaw c u) = 0 := by
    rw [intervalIntegral.integral_of_le (abs_nonneg x)]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro u bounds
    rw [U.actual_source_zero_window c (by rw [abs_of_nonneg bounds.1.le]; exact bounds.2.trans inside), mul_zero]
  rw [outwardRaw, zero, mul_zero]

private theorem scaled_power (z : ℂ) (v : ℝ) (nonnegative : 0 ≤ v) (n : ℕ+) :
    ((n : ℕ) : ℂ) ^ z * ((v / (n : ℕ) : ℝ) : ℂ) ^ z = (v : ℂ) ^ z := by
  have np : 0 < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  calc
    _ = ((((n : ℕ) : ℝ) * (v / (n : ℕ)) : ℝ) : ℂ) ^ z := by
      rw [Complex.ofReal_mul]
      simpa only [Complex.ofReal_natCast] using (Complex.mul_cpow_ofReal_nonneg np.le (div_nonneg nonnegative np.le) z).symm
    _ = _ := by congr 1; field_simp

private theorem scaled_integrable (c : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0 < x) (n : ℕ+) :
    IntervalIntegrable (fun v : ℝ => (v : ℂ) ^ (-c.value) * U.sourceRaw c (v / (n : ℕ))) volume 0 x := by
  have np : 0 < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  have prior := weighted_prefix (-c.value) (U.sourceRaw c) (source_local c)
    (fun inside => U.actual_source_zero_window c (by linarith)) (x / (n : ℕ)) (div_pos positive np)
  have changed := prior.comp_mul_right (c := ((n : ℕ) : ℝ)⁻¹)
  have domains : IntervalIntegrable (fun v : ℝ => ((v / (n : ℕ) : ℝ) : ℂ) ^ (-c.value) * U.sourceRaw c (v / (n : ℕ))) volume 0 x := by
    simpa only [zero_div, div_inv_eq_mul, div_mul_cancel₀ _ np.ne', ← div_eq_mul_inv, zero_mul] using changed
  apply (domains.const_mul (((n : ℕ) : ℂ) ^ (-c.value))).congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with v inside
  rw [uIoc_of_le positive.le] at inside
  rw [← mul_assoc, scaled_power (-c.value) v inside.1.le n]

private theorem prefix_scaled (c : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0 < x) (n : ℕ+) :
    (∫ v : ℝ in (0 : ℝ)..x, (v : ℂ) ^ (-c.value) * U.sourceRaw c (v / (n : ℕ))) =
      ((n : ℕ) : ℂ) ^ (1 - c.value) *
        ∫ v : ℝ in (0 : ℝ)..(x / (n : ℕ)), (v : ℂ) ^ (-c.value) * U.sourceRaw c v := by
  have np : 0 < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  calc
    _ = ∫ v : ℝ in (0 : ℝ)..x, ((n : ℕ) : ℂ) ^ (-c.value) *
        ((((v / (n : ℕ)) : ℝ) : ℂ) ^ (-c.value) * U.sourceRaw c (v / (n : ℕ))) := by
      apply intervalIntegral.integral_congr
      intro v inside
      have nonnegative : 0 ≤ v := (show 0 ≤ v ∧ v ≤ x by simpa only [uIcc_of_le positive.le, mem_Icc] using inside).1
      dsimp only
      rw [← mul_assoc, scaled_power (-c.value) v nonnegative n]
    _ = ((n : ℕ) : ℂ) ^ (-c.value) * (((n : ℕ) : ℝ) •
        ∫ v : ℝ in (0 : ℝ)..(x / (n : ℕ)), (v : ℂ) ^ (-c.value) * U.sourceRaw c v) := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      simpa only [zero_div] using intervalIntegral.integral_comp_div
        (fun v : ℝ => (v : ℂ) ^ (-c.value) * U.sourceRaw c v) (a := 0) (b := x) np.ne'
    _ = _ := by
      rw [Complex.real_smul, Complex.ofReal_natCast]
      have power : ((n : ℕ) : ℂ) ^ (-c.value) * ((n : ℕ) : ℂ) = ((n : ℕ) : ℂ) ^ (1 - c.value) := by
        calc
          _ = ((n : ℕ) : ℂ) ^ (-c.value) * ((n : ℕ) : ℂ) ^ (1 : ℂ) := by rw [Complex.cpow_one]
          _ = ((n : ℕ) : ℂ) ^ (-c.value + 1) := (Complex.cpow_add _ _ (by exact_mod_cast np.ne')).symm
          _ = _ := by congr 1; ring
      rw [← mul_assoc, power]

private theorem forward_prefix_cutoff (c : BurnolCompletedMellinCoordinate) (x v : ℝ)
    (positive : 0 < x) (nonnegative : 0 ≤ v) (before : v ≤ x) :
    U.responseRaw c v = ∑ n ∈ burnolCenteredMobiusCutoffFinset x, (((n : ℕ) : ℂ)⁻¹) * U.sourceRaw c (v / (n : ℕ)) := by
  apply tsum_eq_sum
  intro n outside
  have large : burnolCenteredMobiusCutoff x ≤ (n : ℕ) := by simpa only [mem_burnolCenteredMobiusCutoffFinset, not_lt] using outside
  have np : 0 < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  change Nat.ceil (4 * |x|) ≤ (n : ℕ) at large
  rw [abs_of_pos positive] at large
  have scaled : |v / (n : ℕ)| ≤ q := by
    rw [abs_div, abs_of_nonneg nonnegative, abs_of_pos np, div_le_iff₀ np]
    have highBase : 4 * |x| ≤ (Nat.ceil (4 * |x|) : ℝ) := Nat.le_ceil _
    rw [abs_of_pos positive] at highBase
    have high : 4 * x ≤ ((n : ℕ) : ℝ) := highBase.trans (by exact_mod_cast large)
    nlinarith
  rw [U.actual_source_zero_window c (by linarith), mul_zero]

/-- The finite weighted source action commutes with every actual divisor before its read. -/
theorem actual_forward_outward (c : BurnolCompletedMellinCoordinate) {x : ℝ} (positive : 0 < x) :
    burnolInnerGapForward (outwardRaw c) x =
      2 * (x : ℂ) ^ (c.value - 1) *
        ∫ v : ℝ in (0 : ℝ)..x, (v : ℂ) ^ (-c.value) * U.responseRaw c v := by
  have sourceGap : ∀ {u : ℝ}, |u| ≤ q → outwardRaw c u = 0 :=
    fun inside => actual_outward_gap c (by linarith)
  rw [forward_cut _ sourceGap]
  have integrals : ∀ n ∈ burnolCenteredMobiusCutoffFinset x,
      IntervalIntegrable (fun v : ℝ => (((n : ℕ) : ℂ)⁻¹) * ((v : ℂ) ^ (-c.value) * U.sourceRaw c (v / (n : ℕ)))) volume 0 x :=
    fun n _ => (scaled_integrable c x positive n).const_mul _
  have prefixRead : (∫ v : ℝ in (0 : ℝ)..x, (v : ℂ) ^ (-c.value) * U.responseRaw c v) =
      ∑ n ∈ burnolCenteredMobiusCutoffFinset x, (((n : ℕ) : ℂ)⁻¹) *
        ∫ v : ℝ in (0 : ℝ)..x, (v : ℂ) ^ (-c.value) * U.sourceRaw c (v / (n : ℕ)) := by
    calc
      _ = ∫ v : ℝ in (0 : ℝ)..x, ∑ n ∈ burnolCenteredMobiusCutoffFinset x,
          (((n : ℕ) : ℂ)⁻¹) * ((v : ℂ) ^ (-c.value) * U.sourceRaw c (v / (n : ℕ))) := by
        apply intervalIntegral.integral_congr
        intro v inside
        have bounds : 0 ≤ v ∧ v ≤ x := by simpa only [uIcc_of_le positive.le, mem_Icc] using inside
        dsimp only
        rw [forward_prefix_cutoff c x v positive bounds.1 bounds.2, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = _ := by rw [intervalIntegral.integral_finsetSum integrals]; simp only [intervalIntegral.integral_const_mul]
  rw [prefixRead, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  have np : 0 < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  have power : ((x / (n : ℕ) : ℝ) : ℂ) ^ (c.value - 1) =
      (x : ℂ) ^ (c.value - 1) * ((n : ℕ) : ℂ) ^ (1 - c.value) := by
    rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg positive.le np.le]
    simp only [Complex.ofReal_natCast, div_eq_mul_inv, ← Complex.cpow_neg]
    congr 1
    ring
  rw [outwardRaw, abs_of_pos (div_pos positive np), power, prefix_scaled c x positive n]
  ring

/-- The candidate outward Tate integral is generated by that same finite source action. -/
theorem actual_tate_outward (c : BurnolCompletedMellinCoordinate) {t : ℝ} (positive : 0 < t) :
    tateOutwardRaw c t = 2 * (t : ℂ) ^ (-c.value) *
      ∫ u : ℝ in Ioi t, (u : ℂ) ^ (c.value - 1) * T.tateSourceRaw c u := by
  have change := tail_tate_to_core (1 - c.value) (U.sourceRaw c) (inv_pos.mpr positive)
  rw [inv_inv] at change
  have one : (1 - c.value) - 1 = -c.value := by ring
  have two : -(1 - c.value) = c.value - 1 := by ring
  rw [one, two] at change
  unfold tateOutwardRaw burnolTateReciprocalRaw outwardRaw
  rw [abs_of_pos positive, abs_of_pos (inv_pos.mpr positive), ← change]
  have power : (t : ℂ)⁻¹ * ((t⁻¹ : ℝ) : ℂ) ^ (c.value - 1) = (t : ℂ) ^ (-c.value) := by
    rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg positive.le, ← Complex.cpow_neg,
      show (t : ℂ)⁻¹ = (t : ℂ) ^ (-1 : ℂ) by rw [Complex.cpow_neg, Complex.cpow_one],
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne')]
    congr 1
    ring
  let integralValue : ℂ := ∫ u : ℝ in Ioi t, (u : ℂ) ^ (c.value - 1) * burnolTateReciprocalRaw (U.sourceRaw c) u
  change (t : ℂ)⁻¹ * (2 * ((t⁻¹ : ℝ) : ℂ) ^ (c.value - 1) * integralValue) =
    2 * (t : ℂ) ^ (-c.value) * integralValue
  calc
    _ = 2 * ((t : ℂ)⁻¹ * ((t⁻¹ : ℝ) : ℂ) ^ (c.value - 1)) * integralValue := by ring
    _ = _ := by rw [power]

private theorem actual_tate_source_support (c : BurnolCompletedMellinCoordinate) {t : ℝ}
    (positive : 0 < t) (large : q ≤ t) : T.tateSourceRaw c t = 0 := by
  have small : |t⁻¹| ≤ (4 : ℝ) := by
    rw [abs_of_pos (inv_pos.mpr positive)]
    simpa only [one_div] using (div_le_iff₀ positive).mpr (show (1 : ℝ) ≤ 4 * t by nlinarith)
  unfold OriginalWholeDebtRJointMobiusTateNormalization.tateSourceRaw burnolTateReciprocalRaw
  rw [U.actual_source_zero_window c small, mul_zero]

/-- The outward Tate source is a genuinely finite original-source tail, with no supplied homogeneous constant. -/
theorem actual_tate_outward_finite (c : BurnolCompletedMellinCoordinate) {t : ℝ}
    (positive : 0 < t) (before : t ≤ q) :
    tateOutwardRaw c t = 2 * (t : ℂ) ^ (-c.value) *
      ∫ u : ℝ in t..q, (u : ℂ) ^ (c.value - 1) * T.tateSourceRaw c u := by
  rw [actual_tate_outward c positive, intervalIntegral.integral_of_le before]
  have truncate : (∫ u : ℝ in Ioi t, (u : ℂ) ^ (c.value - 1) * T.tateSourceRaw c u) =
      ∫ u : ℝ in Ioc t q, (u : ℂ) ^ (c.value - 1) * T.tateSourceRaw c u := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    intro u inside
    have after : q < u := by
      have past : t < u := inside.1
      have : ¬ (t < u ∧ u ≤ q) := inside.2
      grind
    rw [actual_tate_source_support c (lt_of_lt_of_le (by norm_num : (0 : ℝ) < q) after.le) after.le, mul_zero]
  rw [truncate]

private theorem response_tail_integrable (c : BurnolCompletedMellinCoordinate) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-c.value) * U.responseRaw c u) (Ioi 0) := by
  have tail := (burnolMellinWeight_integrableOn_tail c.value c.rightHalf (U.response c)).congr
    ((ae_restrict_of_ae (U.actual_raw c)).mono (fun u same => congrArg (fun z : ℂ => (u : ℂ) ^ (-c.value) * z) same))
  have low : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-c.value) * U.responseRaw c u) (Ioc 0 q) := by
    apply (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℂ)) (Ioc 0 q) volume).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u inside
    rw [U.actual_response_zero_window c (by rw [abs_of_pos inside.1]; linarith [inside.2]), mul_zero]
  have union : Ioc (0 : ℝ) q ∪ Ioi q = Ioi 0 := by ext u; simp only [mem_union, mem_Ioc, mem_Ioi]; constructor <;> intro h <;> grind
  rw [← union]
  exact low.union tail

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "coordinate" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "response" => U.response coordinate
local notation "input" => D.sourceInput observation nontrivial half
local notation "next" => D.sourceNext observation nontrivial half

theorem actual_K_tail :
    inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2) response =
      ∫ u : ℝ in Ioi 0, (u : ℂ) ^ (-(coordinate).value) * U.responseRaw coordinate u := by
  let value : BurnolPaAmbientCarrier := ⟨response, OriginalWholeDebtRJointMobiusUnitSource.actual_physical observation nontrivial half⟩
  have restrictionZero : restrictToInterval burnolUnscaledCommonGapRadius (value : BurnolL2) = 0 := by
    apply Lp.ext
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval burnolUnscaledCommonGapRadius) (value : BurnolL2),
      ae_restrict_of_ae (U.actual_raw coordinate),
      ae_restrict_mem (measurableSet_symmetricInterval burnolUnscaledCommonGapRadius),
      Lp.coeFn_zero ℂ 2 (volume.restrict (symmetricInterval burnolUnscaledCommonGapRadius))] with x restricted raw inside zero
    have actual : restrictToInterval burnolUnscaledCommonGapRadius (value : BurnolL2) x = response x := restricted
    have small : |x| ≤ q := abs_le.mpr inside
    rw [actual, raw, U.actual_response_zero_window coordinate (by linarith), zero]
    rfl
  have mean : burnolConstantGapCoefficient burnolUnscaledCommonGapRadius value = 0 :=
    burnolConstantGapCoefficient_eq burnolUnscaledCommonGapRadius (by norm_num [burnolUnscaledCommonGapRadius]) value 0
      (by rw [zero_smul]; exact restrictionZero.symm)
  have read := burnolCompletedMellinRieszVector_readback coordinate value
  rw [burnolCompletedMellinEvaluator_apply, mean, smul_zero, zero_add, burnolMellinTailEvaluator_eq_integral] at read
  change inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2) response =
    ∫ u : ℝ in Ioi q, (u : ℂ) ^ (-(coordinate).value) * response u at read
  rw [read]
  calc
    _ = ∫ u : ℝ in Ioi q, (u : ℂ) ^ (-(coordinate).value) * U.responseRaw coordinate u := by
      exact integral_congr_ae ((ae_restrict_of_ae (U.actual_raw coordinate)).mono
        (fun u same => congrArg (fun z : ℂ => (u : ℂ) ^ (-(coordinate).value) * z) same))
    _ = _ := by
      symm
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ q))
      intro u inside
      rw [U.actual_response_zero_window coordinate (by rw [abs_of_pos inside.1]; have after : u ≤ q := le_of_not_gt inside.2; linarith), mul_zero]

private theorem actual_fourier_next : F next = sourceVolterraResolvent coordinate response := by
  have read := source_fourier_input coordinate (input : BurnolL2)
  change sourceVolterraResolvent coordinate (F (input : BurnolL2)) = F next at read
  change sourceVolterraResolvent coordinate (F (F response)) = F next at read
  rw [fourierL2_fourierL2,
    mem_evenL2ClosedFace_iff.mp (OriginalWholeDebtRJointMobiusUnitSource.actual_physical observation nontrivial half).2] at read
  exact read.symm

private theorem actual_positive_read : ∀ᵐ x : ℝ ∂volume, 0 < x → F next x = actionRaw coordinate x := by
  have native := OriginalPaPhysicalGreen.sourceVolterraResolvent_coeFn coordinate response
  rw [← actual_fourier_next observation nontrivial half] at native
  filter_upwards [native] with x atx positive
  rw [atx, burnolFourierRightDivisionRaw_eq_tail _ _ positive]
  have tailRead : (∫ u : ℝ in Ioi x, (u : ℂ) ^ (-(coordinate).value) * response u) =
      ∫ u : ℝ in Ioi x, (u : ℂ) ^ (-(coordinate).value) * U.responseRaw coordinate u :=
    integral_congr_ae ((ae_restrict_of_ae (U.actual_raw coordinate)).mono
      (fun u same => congrArg (fun z : ℂ => (u : ℂ) ^ (-(coordinate).value) * z) same))
  have split := intervalIntegral.integral_interval_add_Ioi (response_tail_integrable coordinate)
    ((response_tail_integrable coordinate).mono_set (Ioi_subset_Ioi positive.le))
  have parameter : 2 * ((coordinate).value / 2) - 1 = (coordinate).value - 1 := by ring
  have negativeParameter : -2 * ((coordinate).value / 2) = -(coordinate).value := by ring
  rw [parameter, negativeParameter, tailRead]
  rw [actionRaw, actual_forward_outward coordinate positive, powerRaw, abs_of_pos positive,
    homogeneousCoefficient, actual_K_tail observation nontrivial half]
  linear_combination -2 * (x : ℂ) ^ ((coordinate).value - 1) * split

private theorem action_even (c : BurnolCompletedMellinCoordinate) (x : ℝ) : actionRaw c (-x) = actionRaw c x := by
  have forward : burnolInnerGapForward (outwardRaw c) (-x) = burnolInnerGapForward (outwardRaw c) x := by
    unfold burnolInnerGapForward
    apply tsum_congr
    intro n
    simp only [neg_div, outwardRaw, abs_neg]
  rw [actionRaw, actionRaw, forward]
  simp only [powerRaw, abs_neg]

/-- The source operation and its true K-generated homogeneous foot realize the literal original R. -/
theorem actual_whole_action : (F next : ℝ → ℂ) =ᵐ[volume] actionRaw coordinate := by
  have evenResponse : reflectL2 response = response :=
    mem_evenL2ClosedFace_iff.mp (OriginalWholeDebtRJointMobiusUnitSource.actual_physical observation nontrivial half).2
  have evenNext : reflectL2 (F next) = F next := by
    rw [actual_fourier_next, sourceVolterraResolvent_reflect, evenResponse]
  have positive := actual_positive_read observation nontrivial half
  filter_upwards [positive, negMeasurePreserving.quasiMeasurePreserving.ae positive,
    Lp.coeFn_compMeasurePreserving (F next) negMeasurePreserving, volume.ae_ne (0 : ℝ)] with x first second reflected nonzero
  have parity : F next x = F next (-x) := by
    change reflectL2 (F next) x = F next (-x) at reflected
    rw [evenNext] at reflected
    exact reflected
  by_cases pos : 0 < x
  · exact first pos
  · have negative : 0 < -x := by have := lt_of_le_of_ne (le_of_not_gt pos) nonzero; linarith
    exact parity.trans ((second negative).trans (action_even coordinate x))

theorem actual_whole_native : MemLp (actionRaw coordinate) 2 volume :=
  (Lp.memLp (F next)).ae_eq (actual_whole_action observation nontrivial half)

def updatedWave : BurnolL2 :=
  (actual_whole_native observation nontrivial half).toLp (actionRaw coordinate)

theorem actual_updated_wave : updatedWave observation nontrivial half = F next :=
  Lp.ext ((actual_whole_native observation nontrivial half).coeFn_toLp.trans
    (actual_whole_action observation nontrivial half).symm)

theorem actual_source_writeback : fourierL2.symm (updatedWave observation nontrivial half) = next := by
  rw [actual_updated_wave, fourierL2.symm_apply_apply]

theorem actual_homogeneous_coefficient : homogeneousCoefficient coordinate =
    2 * OriginalNextEndpointProgramme.programmePrice coordinate (Real.log stageZeroSonineQ) := by
  rw [homogeneousCoefficient, OriginalWholeDebtRJointMobiusUnitSource.actual_programme_price observation nontrivial half]
  ring

theorem actual_homogeneous_ne_zero : homogeneousCoefficient coordinate ≠ 0 := by
  rw [actual_homogeneous_coefficient]
  exact mul_ne_zero (by norm_num) (OriginalWholeDebtRJointMobiusStrictSource.actual_programme_ne_zero observation nontrivial half)

/-- Dropping the source-born power foot changes the actual full update. -/
theorem actual_power_foot_not_droppable : actionRaw coordinate ≠ burnolInnerGapForward (outwardRaw coordinate) := by
  intro same
  have atOne := congrFun same 1
  simp only [actionRaw, powerRaw, abs_one, Complex.ofReal_one, Complex.one_cpow, mul_one] at atOne
  exact actual_homogeneous_ne_zero observation nontrivial half (by linear_combination atOne)

/-- The same R occurrence retains the zero-contact calculated from the complete original Tate source. -/
theorem actual_zero_end_transport :
    burnolAmbientGapCoefficient q (fourierL2.symm (updatedWave observation nontrivial half)) =
      -2 * OriginalWholeDebtRJointMobiusLocalNormalization.calculatedNormalization coordinate / (coordinate).value := by
  rw [actual_source_writeback, OriginalWholeDebtRJointMobiusRPrefixSource.actual_next_mean]
  rfl

/-- This very source-generated power amplitude writes back through the full existing original B column. -/
theorem actual_complete_B_writeback : fourierL2.symm (updatedWave observation nontrivial half) =
    (burnolEvenAmbientProjection next : BurnolL2) +
      homogeneousCoefficient coordinate • PhysicalOutsideSource.physicalOutsideColumn coordinate := by
  rw [actual_source_writeback, actual_homogeneous_coefficient]
  exact D.actual_complete_update observation nontrivial half

end OriginalWholeDebtRJointMobiusTateRSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
