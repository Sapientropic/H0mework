import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.CountedUnitDecay
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.CountedGapVisibility

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.CountedNativeReentry

open BurnolPhysicalState MeasureTheory Set Filter
open BurnolPhysicalState.OriginalRSourceJointContact.OutsideHistory
open scoped InnerProductSpace Topology

attribute [local instance] OriginalKCombCofinalPaAction.physicalComplete

open private gap_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.AmbientMellin
open private reciprocalTail tailBudget unit_gap from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.CountedGapVisibility
open private unit_invisible from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.NativeReturnImpulse
open private vector_ne from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.AdjointCofinalReturn
open private projected_source from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.FirstPaReturn

local notation "E" => OriginalKCombCofinalPaAction.E
local notation "D" => burnolMultiplicativeDilation
local notation "q" => burnolUnscaledCommonGapRadius
local notation "window" => symmetricInterval q
local notation "P" => fun (c : BurnolCompletedMellinCoordinate) => burnolUnitTailResponse c 4
local notation "T" => fun (n : Nat) => (n : ℝ) * Real.log 2
local notation "χ" => fullMellinTranslationCharacter

private theorem orthogonal_read (value test : BurnolL2) (inside : test ∈ burnolOriginalPaInL2)
    (silent : E value = 0) : inner ℂ test value = 0 := by
  obtain ⟨p, admitted, rfl⟩ := Submodule.mem_map.mp inside
  have actual := OriginalKCombCofinalPaAction.wholePa_normal_read value p admitted
  rw [silent, inner_zero_right] at actual
  exact actual.symm

private theorem unit_shell (c : BurnolCompletedMellinCoordinate) :
    D (Real.log 2) (P c) - χ c.value (Real.log 2) • P c ∈ burnolOriginalPaInL2 := by
  have radius : (4 : ℝ) * Real.exp (-Real.log 2) = 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have moved := burnolUnitTailResponse_radius_dilation c 4 (by norm_num) (by norm_num)
    (Real.log 2) (by rw [radius]; norm_num)
  rw [radius] at moved
  rw [moved, ← smul_sub, burnolUnitTailResponse_shell c 2 (by norm_num) (by norm_num)]
  exact Submodule.smul_mem _ _ (burnolUnitPowerShellWave_originalPa c 2 (by norm_num) (by norm_num))

private def price (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) (h : ℝ) : ℂ :=
  inner ℂ (D h (P c)) value

private theorem price_step (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (silent : ∀ h : ℝ, 0 ≤ h → E (D (-h) value) = 0) (h : ℝ) (nonneg : 0 ≤ h) :
    price c value (h + Real.log 2) = star (χ c.value (Real.log 2)) * price c value h := by
  let defect := D (Real.log 2) (P c) - χ c.value (Real.log 2) • P c
  have quiet := orthogonal_read (D (-h) value) defect (unit_shell c) (silent h nonneg)
  have moved := (D h).inner_map_eq_flip defect value
  rw [← burnolMultiplicativeDilation_neg_eq_symm, quiet] at moved
  dsimp only [defect] at moved
  rw [map_sub, map_smul, inner_sub_left, inner_smul_left, starRingEnd_apply,
    burnolMultiplicativeDilation_add] at moved
  exact sub_eq_zero.mp moved

private theorem character_norm (c : BurnolCompletedMellinCoordinate) :
    ‖χ c.value (Real.log 2)‖ = Real.exp ((1 / 2 - c.value.re) * Real.log 2) := by
  rw [fullMellinTranslationCharacter, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.sub_re, Complex.div_re]
  norm_num

private theorem dyadic_norm (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (silent : ∀ h : ℝ, 0 ≤ h → E (D (-h) value) = 0) (n : Nat) :
    ‖price c value (T n)‖ =
      Real.exp ((1 / 2 - c.value.re) * T n) * ‖inner ℂ (P c) value‖ := by
  have logPos := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  induction n with
  | zero => simp only [Nat.cast_zero, zero_mul, mul_zero, Real.exp_zero, one_mul, price,
      burnolMultiplicativeDilation_zero]
  | succ n prior =>
    change ‖price c value (((n + 1 : Nat) : ℝ) * Real.log 2)‖ = _
    rw [Nat.cast_succ, add_mul, one_mul, price_step c value silent _ (by positivity),
      norm_mul, norm_star, character_norm, prior]
    change Real.exp ((1 / 2 - c.value.re) * Real.log 2) *
      (Real.exp ((1 / 2 - c.value.re) * T n) * ‖inner ℂ (P c) value‖) = _
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    push_cast
    ring

private theorem scaled_raw (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    (D h (P c) : ℝ → ℂ) =ᵐ[volume] fun x =>
      (Real.exp (h / 2) : ℂ) * burnolUnitTailDirichletRaw c.value 4 (Real.exp h * x) := by
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp h * x) volume volume := by
    simpa only [smul_eq_mul] using (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
      (r := Real.exp h) (Real.exp_pos h).ne')
  filter_upwards [burnolMultiplicativeDilation_coeFn h (P c),
    qmp.ae (burnolUnitTailResponse_coeFn c 4 (by norm_num) (by norm_num))] with x actual raw
  change (D h (P c) : ℝ → ℂ) x = _ at actual
  rw [actual, burnolL2RawNormalizedDilation, raw]

private theorem exterior_price_bound (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (value : BurnolL2)
    (gap : burnolQuarterRestriction value = 0) (h : ℝ) (scale : 16 ≤ Real.exp h) :
    ‖price c value h‖ ≤ CountedUnitDecay.tailConstant c * Real.exp (-(h / 2)) * tailBudget value := by
  let C := CountedUnitDecay.tailConstant c * Real.exp (-(h / 2))
  have Cnonneg : 0 ≤ C := mul_nonneg (CountedUnitDecay.tailConstant_nonneg c) (Real.exp_pos _).le
  have gapRead := gap_read value 0 (gap.trans (zero_smul ℂ (intervalConstant q)).symm)
  have inside : (∫ x in window, inner ℂ ((D h (P c)) x) (value x)) = 0 := by
    calc
      _ = ∫ _ : ℝ in window, (0 : ℂ) := by
        apply integral_congr_ae
        filter_upwards [gapRead] with x atX
        rw [atX, inner_zero_right]
      _ = 0 := integral_zero ℝ ℂ
  have int := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (D h (P c)) value
  have exterior : (∫ x in windowᶜ, inner ℂ ((D h (P c)) x) (value x)) = price c value h := by
    have split := integral_add_compl (measurableSet_symmetricInterval q) int
    rw [inside, zero_add] at split
    rw [price, MeasureTheory.L2.inner_def]
    exact split
  have raw := ae_restrict_of_ae (s := windowᶜ) (scaled_raw c h)
  have kernel := ae_restrict_of_ae (s := windowᶜ)
    (burnolSourceScaleReciprocalPrimitive_coeFn 4 (by norm_num))
  have outside : ∀ᵐ x ∂volume.restrict windowᶜ, x ∈ windowᶜ :=
    ae_restrict_mem (measurableSet_symmetricInterval q).compl
  have paid : ∀ᵐ x ∂volume.restrict windowᶜ,
      ‖inner ℂ ((D h (P c)) x) (value x)‖ ≤ C * ‖inner ℂ (reciprocalTail x) (value x)‖ := by
    filter_upwards [raw, kernel, outside] with x actual kernelAt away
    have rad : (1 / 4 : ℝ) < |x| := lt_of_not_ge (fun inGap => away (abs_le.mp inGap))
    have absPos : 0 < |x| := (by norm_num : (0 : ℝ) < 1 / 4).trans rad
    have invBound : |x|⁻¹ < 4 := by
      rw [inv_eq_one_div, div_lt_iff₀ absPos]
      linarith
    change reciprocalTail x = _ at kernelAt
    rw [if_pos invBound] at kernelAt
    have address : 4 ≤ |Real.exp h * x| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos h)]
      calc
        4 = 16 * (1 / 4 : ℝ) := by norm_num
        _ ≤ Real.exp h * |x| := mul_le_mul scale rad.le (by norm_num) (Real.exp_pos h).le
    have bound := CountedUnitDecay.tail_bound c zero _ address
    have factor : Real.exp (h / 2) * (Real.exp h)⁻¹ = Real.exp (-(h / 2)) := by
      rw [← Real.exp_neg, ← Real.exp_add]
      congr 1
      ring
    simp only [RCLike.inner_apply, starRingEnd_apply, norm_mul, norm_star, actual, kernelAt,
      norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ ‖value x‖ * (Real.exp (h / 2) *
          (CountedUnitDecay.tailConstant c * |Real.exp h * x|⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left bound (Real.exp_pos _).le) (norm_nonneg _)
      _ = _ := by
        rw [abs_mul, abs_of_pos (Real.exp_pos h), mul_inv_rev]
        unfold C
        rw [← factor]
        ring
  have majorant := (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) reciprocalTail value).norm
  have bound := norm_integral_le_of_norm_le (majorant.const_mul C).integrableOn paid
  rw [exterior, integral_const_mul] at bound
  apply bound.trans
  apply mul_le_mul_of_nonneg_left _ Cnonneg
  unfold tailBudget
  rw [← integral_add_compl (measurableSet_symmetricInterval q) majorant]
  exact le_add_of_nonneg_left (integral_nonneg fun _ => norm_nonneg _)

/-- A silent position-gap field pairs to zero with the original radius-four unit itself. -/
theorem unit_read_zero_of_inward_silence (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (value : BurnolL2) (gap : value ∈ locallyConstantFace q)
    (silent : ∀ h : ℝ, 0 ≤ h → E (D (-h) value) = 0) :
    inner ℂ (P c) value = 0 := by
  have erased := CountedGapVisibility.gap_zero_of_inward_silence value gap silent
  let d := (1 - c.value.re) * Real.log 2
  let C := CountedUnitDecay.tailConstant c * tailBudget value
  have dpos : 0 < d := mul_pos (sub_pos.mpr c.belowOne) (Real.log_pos (by norm_num))
  have estimate : ∀ᶠ n : Nat in atTop, ‖inner ℂ (P c) value‖ ≤ C * Real.exp (-(d * (n : ℝ))) := by
    filter_upwards [eventually_ge_atTop (4 : Nat)] with n late
    have scale : (16 : ℝ) ≤ Real.exp (T n) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      simpa only [show (2 : ℝ)^4 = 16 by norm_num] using
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) late
    have main := exterior_price_bound c zero value erased (T n) scale
    rw [dyadic_norm c value silent] at main
    apply le_of_mul_le_mul_left _ (Real.exp_pos ((1 / 2 - c.value.re) * T n))
    calc
      _ ≤ CountedUnitDecay.tailConstant c * Real.exp (-(T n / 2)) * tailBudget value := main
      _ = _ := by
        unfold C d
        rw [show -(T n / 2) = (1 / 2 - c.value.re) * T n +
            -((1 - c.value.re) * Real.log 2 * (n : ℝ)) by ring, Real.exp_add]
        ring
  have advance := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop dpos
  have limit := (Real.tendsto_exp_neg_atTop_nhds_zero.comp advance).const_mul C
  rw [mul_zero] at limit
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto limit estimate) (norm_nonneg _))

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "U" => NativeReturnImpulse.unit observation half
local notation "R" => burnolDirectRightResolventCLM c
local notation "V" => (OriginalKDirectRCofinalReentrySourceAction.sourceReentryVector c : BurnolPaAmbientCarrier)
local notation "fee" => ReentryDifferenceClock.fee observation nontrivial half depth
local notation "pa" => OriginalKCombCofinalPaAction.actualPa observation nontrivial half depth

include nontrivial in
private theorem unit_nonzero : U ≠ 0 := by
  intro erased
  have paid : P c - (E (P c) : BurnolL2) = 0 := erased
  let unit := burnolZeroOwnedUnitTailState observation nontrivial half.down
  have projected : unit = E (P c) := Subtype.ext (sub_eq_zero.mp paid)
  apply burnolZeroOwnedUnitTailState_notInPa observation nontrivial half.down
  change unit ∈ _
  rw [projected]
  exact Submodule.starProjection_apply_mem _ _

private theorem unit_read : inner ℂ (P c) U = inner ℂ U U := by
  have split : P c = U + (E (P c) : BurnolL2) := (sub_add_cancel _ _).symm
  have invisible := unit_invisible observation half
  calc
    _ = inner ℂ (U + (E (P c) : BurnolL2)) U := congrArg (fun x : BurnolL2 => inner ℂ x U) split
    _ = _ := by
      rw [inner_add_left, orthogonal_read _ _ (projected_source (P c)) invisible, add_zero]

include nontrivial in
/-- The same original injected residual is seen somewhere on its actual full R orbit. -/
theorem actual_injected_unit_returns : ∃ lag : Nat, E ((R ^ lag) U) ≠ 0 := by
  by_contra! silent
  have inward (h : ℝ) (nonneg : 0 ≤ h) : E (D (-h) U) = 0 := by
    rcases nonneg.eq_or_lt with atZero | positive
    · rw [← atZero, neg_zero, burnolMultiplicativeDilation_zero]
      exact unit_invisible observation half
    · have paid := DilationFromPowers.observed_inward_zero E c U (fun n => silent (n + 1))
        (2 * h) (by linarith)
      rwa [show -(2 * h) / 2 = -h by ring] at paid
  have paired := unit_read_zero_of_inward_silence c observation.mathlibZero U
    (unit_gap observation nontrivial half) inward
  rw [unit_read] at paired
  exact unit_nonzero observation nontrivial half (inner_self_eq_zero.mp paired)

/-- Every tail of original literal receipts contains a nonzero Pa innovation at an actual source write. -/
theorem literal_return_cofinal (cutoff : Nat) :
    ∃ ordinal ≥ cutoff, fee ordinal ≠ 0 ∧
      pa (ordinal + 1) - E (R (pa ordinal : BurnolL2)) = fee ordinal • V ∧
      pa (ordinal + 1) ≠ E (R (pa ordinal : BurnolL2)) := by
  obtain ⟨lag, live⟩ := actual_injected_unit_returns observation nontrivial half
  have feeLive : ∃ ordinal ≥ cutoff, fee ordinal ≠ 0 := by
    by_contra! silent
    have quiet := (NativeReturnImpulse.literal_tail_silence_iff observation nontrivial half depth cutoff).mp silent
    exact live ((NativeReturnImpulse.impulse_silence_iff_native observation nontrivial half).mp quiet lag)
  obtain ⟨ordinal, after, liveFee⟩ := feeLive
  have write := ReentryDifferenceClock.literal_write observation nontrivial half depth ordinal
  refine ⟨ordinal, after, liveFee, write, ?_⟩
  apply sub_ne_zero.mp
  rw [write]
  exact smul_ne_zero liveFee (vector_ne observation nontrivial half)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.CountedNativeReentry
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
