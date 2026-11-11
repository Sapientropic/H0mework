import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GenericSourceStepBAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.UnweightedCayleySource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CrossUnitKSource

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley

open Complex BurnolPhysicalState OriginalRieszSource
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFullAdjointSource
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalKCrossParameterRAdjointSource.UnweightedCayleySource
open UnitPowerJordanSource GenericSourceStepBAction
open scoped InnerProductSpace

open private actual_position_step position_read source_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GenericSourceStepBAction
open private inward_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator
open private actualAdjoint_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullAdjointSource.Source
open private source_left_inverse source_right_inverse from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
open private coordinate_eq from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CrossUnitKSource

local notation "q" => (1/4 : ℝ)
local notation "G" => locallyConstantFace burnolUnscaledCommonGapRadius
local notation "Rq" => burnolQuarterRestriction
local notation "P₀" => Constructor.zeroMean
local notation "M" => burnolAmbientCompletedMellinEvaluator
local notation "T" => sourceCayley
local notation "δ" => sourceDamping
local notation "d" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "g" => SingularCounting.centeredPower

private theorem right_quarter (c : BurnolCompletedMellinCoordinate) : 1/4 < (c.value/2).re := by
  rw [Complex.div_re]
  norm_num
  linarith [c.rightHalf]

private theorem below_half (c : BurnolCompletedMellinCoordinate) : (c.value/2).re < 1/2 := by
  rw [Complex.div_re]
  norm_num
  linarith [c.belowOne]

private theorem damping_read (c : BurnolCompletedMellinCoordinate) :
    (δ c : ℂ) = c.value/2 + star c.value/2 - 1/2 := by
  apply Complex.ext
  · simp [sourceDamping]
  · simp
    ring

/-- The full original forward Cayley action preserves the literal position gap. -/
theorem actual_gap_cayley (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) (gap : v ∈ G) :
    T c v ∈ G := by
  rw [sourceCayley_apply]
  exact (G).add_mem gap ((G).smul_mem _ (CombSource.Pricing.ambient_R_positionGap _ (right_quarter c) v gap))

private theorem cayley_even (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (even : reflectL2 v = v) : reflectL2 (T c v) = T c v := by
  rw [sourceCayley_apply, map_add, map_smul, even]
  exact congrArg (fun field : BurnolL2 => v + (δ c : ℂ) • field) (inward_even c v even)

/-- This factor comes from the full inward action on the fixed gap. -/
def gapMultiplier (c : BurnolCompletedMellinCoordinate) (w : ℂ) : ℂ :=
  (w - star c.value/2) / (c.value/2 + w - 1/2)

private theorem denominator_ne (c : BurnolCompletedMellinCoordinate) (w : ℂ)
    (right : 1/4 < w.re) : c.value/2 + w - 1/2 ≠ 0 := by
  have positive : 0 < (c.value/2 + w - 1/2).re := by
    simp only [Complex.sub_re, Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    linarith [c.rightHalf]
  exact fun gone => by rw [gone, Complex.zero_re] at positive; exact lt_irrefl _ positive

/-- The actual forward multiplier contracts every interior probe of the fixed strip. -/
theorem gapMultiplier_norm_lt_one (c : BurnolCompletedMellinCoordinate) (w : ℂ)
    (right : 1/4 < w.re) : ‖gapMultiplier c w‖ < 1 := by
  let num := w - star c.value/2
  let den := c.value/2+w-1/2
  have translated : den = num+(δ c : ℂ) := by
    dsimp only [den,num]
    rw [damping_read]
    ring
  have re : num.re = w.re - c.value.re/2 := by
    simp only [num, Complex.sub_re, Complex.div_ofNat_re, Complex.star_def, Complex.conj_re]
  have price : Complex.normSq den - Complex.normSq num = δ c * (2*w.re-1/2) := by
    rw [translated]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, add_zero, re, sourceDamping]
    ring
  have positive : 0 < δ c * (2*w.re-1/2) := mul_pos (sourceDamping_pos c) (by linarith)
  have strict : ‖num‖ < ‖den‖ := by
    apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [Complex.sq_norm, Complex.sq_norm]
    linarith only [price, positive]
  rw [gapMultiplier, norm_div, div_lt_one (norm_pos_iff.mpr (denominator_ne c w right))]
  exact strict

/-- The ambient evaluation sees the complete Cayley multiplier on every position-gap input. -/
theorem actual_gap_cayley_scalar (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) (gap : v ∈ G)
    (w : ℂ) (right : 1/4 < w.re) (below : w.re < 1/2) :
    M (burnolDivisionCompletedMellinCoordinate w right below) (T c v) =
      gapMultiplier c w * M (burnolDivisionCompletedMellinCoordinate w right below) v := by
  let read := M (burnolDivisionCompletedMellinCoordinate w right below)
  have original := CombSource.Pricing.ambient_R_scalar_action (c.value/2) (right_quarter c) v gap w right below
  change read (burnolDirectRightResolvent (c.value/2) v) =
    -(1/(c.value/2+w-1/2))*read v at original
  change read (T c v) = _
  rw [sourceCayley_apply, map_add, map_smul, original, smul_eq_mul]
  have factor : (1 : ℂ) + (δ c : ℂ) * (-(1/(c.value/2 + w - 1/2))) = gapMultiplier c w := by
    have numerator : (c.value/2+w-1/2) - (δ c : ℂ) = w-star c.value/2 := by
      rw [damping_read]
      ring
    rw [gapMultiplier, ← numerator, sub_div, div_self (denominator_ne c w right)]
    ring
  calc
    _ = ((1 : ℂ) + (δ c : ℂ) * (-(1/(c.value/2 + w - 1/2)))) * read v := by ring
    _ = _ := by rw [factor]

/-- Every literal forward step places the complete field in the conjugate observation kernel. -/
theorem actual_gap_cayley_conjugate_zero (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) (gap : v ∈ G) :
    M (d c) (T c v) = 0 := by
  let w := (d c).value/2
  have same : burnolDivisionCompletedMellinCoordinate w (right_quarter (d c)) (below_half (d c)) = d c := by
    apply coordinate_eq
    change 2*((d c).value/2)=(d c).value
    ring
  have actual := actual_gap_cayley_scalar c v gap w (right_quarter (d c)) (below_half (d c))
  rw [same] at actual
  simpa only [gapMultiplier, w, OriginalPrimitiveRankBalance.conjugateCoordinate, sub_self, zero_div, zero_mul] using actual

private theorem mean_read (v : BurnolL2) :
    burnolAmbientGapCoefficient burnolUnscaledCommonGapRadius v = burnolQuarterMeanCoefficient (Rq v) := by
  change (((‖intervalConstant q‖ : ℂ)^2)⁻¹) * inner ℂ (intervalConstant q) (Rq v) = _
  rw [← Complex.ofReal_pow, burnolQuarterMeanCoefficient]
  exact (div_eq_inv_mul _ _).symm

/-- The native outward amplitude reads the entire ambient conjugate price with the same mean. -/
theorem actual_currentAmplitude_ambient (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) :
    currentAmplitude c v = -2 * M (d c) v := by
  rw [currentAmplitude, burnolAmbientCompletedMellinEvaluator, burnolRadiusAmbientCompletedMellinEvaluator]
  change -2 * (sourceTail c v + burnolQuarterMeanCoefficient (Rq v) * (q:ℂ)^(1-star c.value)/(1-star c.value)) =
    -2 * ((q:ℂ)^(1-star c.value)/(1-star c.value) * burnolAmbientGapCoefficient burnolUnscaledCommonGapRadius v +
      sourceTail c v)
  rw [mean_read]
  ring

private theorem center_zero_iff (v : BurnolL2) : P₀ (Rq v) = 0 ↔ v ∈ G := by
  change P₀ (Rq v) = 0 ↔ Rq v ∈ intervalConstantLine q
  constructor
  · intro zero
    apply (burnolQuarterMeanZeroProjection_eq_zero_iff (Rq v)).1
    exact congrArg (fun x : BurnolQuarterMeanZeroCarrier => (x : BurnolQuarterIntervalL2)) zero
  · intro gap
    apply Subtype.ext
    exact (burnolQuarterMeanZeroProjection_eq_zero_iff (Rq v)).2 gap

private theorem actual_adjoint_source (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) :
    (T c).adjoint v = v + (δ c : ℂ) • sourceStep c v := by
  rw [sourceCayley_actual_adjoint, sourceAdjointCayley]
  have same : sourceAdjoint c v = sourceStep c v :=
    (actualAdjoint_read c v).symm.trans (sourceStep_actual c v)
  rw [same]

private theorem adjoint_even (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (even : reflectL2 v = v) : reflectL2 ((T c).adjoint v) = (T c).adjoint v := by
  rw [actual_adjoint_source, map_add, map_smul, even, source_even c v even]

/-- The true backward action generates the entire obstruction in the original centered quarter. -/
theorem actual_gap_cayley_adjoint_position (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (gap : v ∈ G) (even : reflectL2 v = v) :
    P₀ (Rq ((T c).adjoint v)) = (-2 * (δ c : ℂ) * M (d c) v) • g c := by
  have original := actual_position_step c v even
  rw [position_read _ (source_even c v even), position_read _ even, (center_zero_iff v).2 gap,
    map_zero, zero_add, actual_currentAmplitude_ambient] at original
  rw [actual_adjoint_source, map_add, map_smul, map_add, map_smul, (center_zero_iff v).2 gap,
    zero_add, original, smul_smul]
  congr 1
  ring

/-- The full original adjoint returns to the same gap exactly on the generated Mellin kernel. -/
theorem actual_gap_cayley_adjoint_iff (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (gap : v ∈ G) (even : reflectL2 v = v) :
    (T c).adjoint v ∈ G ↔ M (d c) v = 0 := by
  rw [← center_zero_iff, actual_gap_cayley_adjoint_position c v gap even]
  constructor
  · intro lost
    have damping : (δ c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sourceDamping_pos c).ne'
    have scalar := (smul_eq_zero.mp lost).resolve_right (centeredPower_ne_zero c)
    exact (mul_eq_zero.mp scalar).resolve_left (mul_ne_zero (by norm_num) damping)
  · intro zero
    rw [zero, mul_zero, zero_smul]

private theorem cayley_power_gap_even (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (gap : v ∈ G) (even : reflectL2 v = v) (n : Nat) :
    ((T c)^n) v ∈ G ∧ reflectL2 (((T c)^n) v) = ((T c)^n) v := by
  induction n with
  | zero => simpa only [pow_zero, one_apply_eq_self] using And.intro gap even
  | succ n prior =>
    rw [pow_succ', mul_apply_eq_comp]
    exact ⟨actual_gap_cayley c _ prior.1, cayley_even c _ prior.2⟩

/-- Each power's range is tested by the consecutive native adjoint reads on the same field. -/
theorem actual_gap_cayley_power_image (c : BurnolCompletedMellinCoordinate) (n : Nat) (v : BurnolL2)
    (gap : v ∈ G) (even : reflectL2 v = v) :
    (∃ prior : BurnolL2, prior ∈ G ∧ reflectL2 prior = prior ∧ ((T c)^n) prior = v) ↔
      ∀ i < n, M (d c) ((((T c).adjoint)^i) v) = 0 := by
  induction n generalizing v with
  | zero =>
    constructor
    · intro _ i impossible
      exact (Nat.not_lt_zero i impossible).elim
    · intro _
      exact ⟨v, gap, even, by rw [pow_zero, one_apply_eq_self]⟩
  | succ n ih =>
    constructor
    · rintro ⟨prior, before, symmetric, action⟩ i within
      let previous := ((T c)^n) prior
      have state := cayley_power_gap_even c prior before symmetric n
      have performed : T c previous = v := by simpa only [pow_succ', mul_apply_eq_comp] using action
      cases i with
      | zero =>
        rw [pow_zero, one_apply_eq_self, ← performed]
        exact actual_gap_cayley_conjugate_zero c previous state.1
      | succ i =>
        have returned : (T c).adjoint v = previous := by rw [← performed, source_left_inverse]
        rw [pow_succ, mul_apply_eq_comp, returned]
        exact (ih previous state.1 state.2).1 ⟨prior, before, symmetric, rfl⟩ i
          (Nat.lt_of_succ_lt_succ within)
    · intro all
      let previous := (T c).adjoint v
      have head : M (d c) v = 0 := by
        simpa only [pow_zero, one_apply_eq_self] using all 0 (Nat.zero_lt_succ n)
      have before := (actual_gap_cayley_adjoint_iff c v gap even).2 head
      have symmetric := adjoint_even c v even
      have lower (i : Nat) (within : i < n) : M (d c) ((((T c).adjoint)^i) previous) = 0 := by
        have native := all (i+1) (Nat.succ_lt_succ within)
        rwa [pow_succ, mul_apply_eq_comp] at native
      obtain ⟨prior, original, parity, performed⟩ := (ih previous before symmetric).2 lower
      refine ⟨prior, original, parity, ?_⟩
      rw [pow_succ', mul_apply_eq_comp, performed]
      exact source_right_inverse c v

/-- The same multiplier composes along the actual finite forward word. -/
theorem actual_gap_cayley_power_scalar (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (gap : v ∈ G) (even : reflectL2 v = v) (n : Nat)
    (w : ℂ) (right : 1/4 < w.re) (below : w.re < 1/2) :
    M (burnolDivisionCompletedMellinCoordinate w right below) (((T c)^n) v) =
      (gapMultiplier c w)^n * M (burnolDivisionCompletedMellinCoordinate w right below) v := by
  induction n with
  | zero => simp only [pow_zero, one_apply_eq_self, one_mul]
  | succ n previous =>
    rw [pow_succ' (T c), mul_apply_eq_comp,
      actual_gap_cayley_scalar c _ (cayley_power_gap_even c v gap even n).1,
      previous, ← mul_assoc, ← pow_succ']

end OriginalKFiniteOrderRelease.PositionGapCayley
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
