import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.Cayley
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.CountedNativeReentry

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.NextLiveWindow

open BurnolPhysicalState MeasureTheory Set Finset
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped BigOperators

open private anchor_right from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DelayedWordSeparation
open private shifted_right from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DelayedResidualProbe

local notation "R" => burnolDirectRightResolventCLM
local notation "S" => burnolDirectRightResolvent
local notation "δ" => sourceDamping
local notation "Read" => BurnolL2 →L[ℂ] ℂ

private theorem shift_decay (c : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0 < x)
    (v : BurnolL2) : ‖S (c.value / 2 + (x : ℂ)) v‖ ≤ ‖v‖ / x := by
  let z := c.value / 2 + (x : ℂ)
  have rate : z.re - 1 / 4 = δ c / 2 + x := by
    dsimp only [z, sourceDamping]
    rw [Complex.add_re, Complex.ofReal_re, Complex.div_re]
    norm_num
    ring
  have extra := half_pos (sourceDamping_pos c)
  have damped := add_pos extra positive
  change ‖S z v‖ ≤ _
  rw [burnolDirectRightResolvent, norm_neg]
  calc
    _ ≤ ∫ t : ℝ in Ioi 0, ‖burnolDirectRightResolventIntegrand z v t‖ :=
      norm_integral_le_integral_norm _
    _ = (δ c / 2 + x)⁻¹ * ‖v‖ := by
      simp only [burnolDirectRightResolventIntegrand, norm_smul,
        (burnolMultiplicativeDilation _).norm_map, norm_positiveMellinQuarterRightResolventWeight, rate]
      rw [integral_mul_const, integral_exp_mul_Ioi (neg_lt_zero.mpr damped) 0]
      simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]
    _ ≤ _ := by
      rw [div_eq_mul_inv ‖v‖ x, mul_comm ‖v‖]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ positive (by linarith)) (norm_nonneg v)

private def tolerance (read : Read) (after : BurnolL2) : ℝ := ‖read after‖ / 4

private def shift (read : Read) (before after : BurnolL2) : ℝ :=
  1 + ‖read‖ * ‖before‖ / tolerance read after

private def budget (c : BurnolCompletedMellinCoordinate) (read : Read) (before after : BurnolL2) : ℝ :=
  shift read before after * (‖read‖ * ((2 / δ c) * ‖after‖))

/-- The window length uses the paid current margin and the two actual consecutive source fields. -/
def fuel (c : BurnolCompletedMellinCoordinate) (read : Read) (before after : BurnolL2) : Nat :=
  ⌊budget c read before after /
    (tolerance read after * (δ c / shift read before after))⌋₊ + 1

private theorem geometric_budget (c : BurnolCompletedMellinCoordinate) (x B ε : ℝ)
    (positive : 0 < x) (tolerated : 0 < ε) :
    B * (discount c x) ^ (⌊B / (ε * (δ c / x))⌋₊ + 1) < ε := by
  let η := δ c / x
  let N := ⌊B / (ε * η)⌋₊ + 1
  have ηpos : 0 < η := div_pos (sourceDamping_pos c) positive
  have ratio : discount c x = (1 + η)⁻¹ := by
    have fraction : 1 + δ c / x = (δ c + x) / x := by
      apply (eq_div_iff positive.ne').mpr
      rw [add_mul, one_mul, div_mul_cancel₀ _ positive.ne', add_comm]
    unfold discount η
    rw [fraction, inv_div]
  have floor : B / (ε * η) < (N : ℝ) := by
    unfold N
    exact_mod_cast Nat.lt_floor_add_one (B / (ε * η))
  have above := (div_lt_iff₀ (mul_pos tolerated ηpos)).mp floor
  have grows : 1 + (N : ℝ) * η ≤ (1 + η) ^ N := one_add_mul_le_pow (by linarith [ηpos]) N
  have first : B < ε * (1 + (N : ℝ) * η) := by nlinarith
  have room := first.trans_le (mul_le_mul_of_nonneg_left grows tolerated.le)
  change B * (discount c x) ^ N < ε
  rw [ratio, inv_pow, ← div_eq_mul_inv]
  exact (div_lt_iff₀ (pow_pos (by linarith [ηpos] : 0 < 1 + η) _)).mpr room

private def probe (c : BurnolCompletedMellinCoordinate) (read : Read) (before after : BurnolL2) : ℂ :=
  -(shift read before after : ℂ) * read (finiteShift c (shift read before after)
    (fuel c read before after) after)

private theorem probe_near (c : BurnolCompletedMellinCoordinate) (read : Read)
    (before after : BurnolL2) (step : R c before = after) (live : read after ≠ 0) :
    ‖read after - probe c read before after‖ < ‖read after‖ / 2 := by
  let ε := tolerance read after
  let x := shift read before after
  let N := fuel c read before after
  let z := c.value / 2 + (x : ℂ)
  let value := -(x : ℂ) * read (S z after)
  have positive : 0 < ε := div_pos (norm_pos_iff.mpr live) (by norm_num)
  have xpos : 0 < x := by unfold x shift; positivity
  have source := burnolDirectRightResolvent_identity z (c.value / 2)
    (shifted_right c xpos.le) (anchor_right c) before
  change S z before - R c before = (z - c.value / 2) • S z (R c before) at source
  have move : z - c.value / 2 = (x : ℂ) := by unfold z; ring
  rw [move, step] at source
  have recovered : after - (-(x : ℂ)) • S z after = S z before := by
    rw [neg_smul, sub_neg_eq_add]
    exact ((sub_eq_iff_eq_add.mp source).trans (add_comm _ _)).symm
  have exactRead := congrArg read recovered
  rw [map_sub, map_smul, smul_eq_mul] at exactRead
  have first : ‖read after - value‖ < ε := by
    change ‖read after - (-(x : ℂ) * read (S z after))‖ < ε
    rw [exactRead]
    calc
      _ ≤ ‖read‖ * ‖S z before‖ := read.le_opNorm _
      _ ≤ ‖read‖ * (‖before‖ / x) :=
        mul_le_mul_of_nonneg_left (shift_decay c x xpos before) (norm_nonneg read)
      _ = (‖read‖ * ‖before‖) / x := by ring
      _ < ε := by
        apply (div_lt_iff₀ xpos).mpr
        have scaled : ε * x = ε + ‖read‖ * ‖before‖ := by
          change ε * (1 + ‖read‖ * ‖before‖ / ε) = _
          field_simp [positive.ne']
        linarith
  have second : ‖value - probe c read before after‖ < ε := by
    change ‖-(x : ℂ) * read (S z after) - -(x : ℂ) * read (finiteShift c x N after)‖ < ε
    rw [← mul_sub, ← map_sub, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos xpos]
    calc
      _ ≤ x * (‖read‖ * ‖S z after - finiteShift c x N after‖) :=
        mul_le_mul_of_nonneg_left (read.le_opNorm _) xpos.le
      _ ≤ x * (‖read‖ * (((2 / δ c) * ‖after‖) * (discount c x) ^ N)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (actual_shift_error c x xpos.le N after) (norm_nonneg read)) xpos.le
      _ = budget c read before after * (discount c x) ^ N := by unfold budget x; ring
      _ < ε := geometric_budget c x _ ε xpos positive
  have sum := norm_add_le (read after - value) (value - probe c read before after)
  rw [sub_add_sub_cancel] at sum
  change ‖read after - value‖ < ‖read after‖ / 4 at first
  change ‖value - probe c read before after‖ < ‖read after‖ / 4 at second
  linarith

private def coeff (c : BurnolCompletedMellinCoordinate) (read : Read) (before after : BurnolL2)
    (k j : Nat) : ℂ :=
  -(shift read before after : ℂ) * rightWeight c (shift read before after) k j

private def mass (c : BurnolCompletedMellinCoordinate) (read : Read) (before after : BurnolL2) : ℝ :=
  ∑ k ∈ range (fuel c read before after), ∑ j ∈ range (k + 1),
    ‖coeff c read before after k j‖

/-- The finite search threshold is positive whenever the paid current read is nonzero. -/
def visibleFloor (c : BurnolCompletedMellinCoordinate) (read : Read) (before after : BurnolL2) : ℝ :=
  ‖read after‖ / (2 * (mass c read before after + 1))

private theorem mass_nonneg (c : BurnolCompletedMellinCoordinate) (read : Read) (before after : BurnolL2) :
    0 ≤ mass c read before after := by
  unfold mass
  exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _

private theorem probe_as_word (c : BurnolCompletedMellinCoordinate) (read : Read)
    (before after : BurnolL2) :
    probe c read before after =
      ∑ k ∈ range (fuel c read before after), ∑ j ∈ range (k + 1),
        coeff c read before after k j * read ((R c ^ (j + 1)) after) := by
  simp only [probe, finite_shift_read, Finset.mul_sum, coeff, mul_assoc]

/-- A paid current observation and its actual predecessor generate a strict finite future witness. -/
theorem finite_future_test (c : BurnolCompletedMellinCoordinate) (read : Read) (before after : BurnolL2)
    (step : R c before = after) (live : read after ≠ 0) :
    0 < visibleFloor c read before after ∧
      ∃ lag : Nat, 0 < lag ∧ lag ≤ fuel c read before after ∧
        visibleFloor c read before after < ‖read ((R c ^ lag) after)‖ := by
  let b := mass c read before after
  let m := ‖read after‖
  let e := visibleFloor c read before after
  have bnonneg : 0 ≤ b := mass_nonneg c read before after
  have mpos : 0 < m := norm_pos_iff.mpr live
  have pos : 0 < 2 * (b + 1) := by positivity
  have epos : 0 < e := div_pos mpos pos
  refine ⟨epos, ?_⟩
  by_contra! quiet
  have upper : ‖probe c read before after‖ ≤ b * e := by
    rw [probe_as_word]
    calc
      _ ≤ ∑ k ∈ range (fuel c read before after), ∑ j ∈ range (k + 1),
          ‖coeff c read before after k j * read ((R c ^ (j + 1)) after)‖ :=
        (norm_sum_le _ _).trans (sum_le_sum fun _ _ => norm_sum_le _ _)
      _ ≤ ∑ k ∈ range (fuel c read before after), ∑ j ∈ range (k + 1),
          ‖coeff c read before after k j‖ * e := by
        apply sum_le_sum
        intro k hk
        apply sum_le_sum
        intro j hj
        rw [norm_mul]
        have klt := mem_range.mp hk
        have jlt := mem_range.mp hj
        exact mul_le_mul_of_nonneg_left (quiet (j + 1) (by omega) (by omega)) (norm_nonneg _)
      _ = _ := by simp only [b, mass, sum_mul]
  have strict : b * e < m / 2 := by
    change b * (m / (2 * (b + 1))) < m / 2
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ pos).mpr
    nlinarith
  have first := probe_near c read before after step live
  have total := norm_add_le (read after - probe c read before after) (probe c read before after)
  rw [sub_add_cancel] at total
  have small := upper.trans_lt strict
  change m ≤ _ at total
  change ‖read after - probe c read before after‖ < m / 2 at first
  linarith

open private betaRead from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.AdjointCofinalReturn
open private native_powers from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.ReentryDifferenceClock

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "β" => betaRead observation half
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "fee" => ReentryDifferenceClock.fee observation nontrivial half depth

/-- An already read original receipt computes a finite window for the next live literal return. -/
theorem actual_next_window (ordinal : Nat) (live : fee (ordinal + 1) ≠ 0) :
    let limit := fuel c β (raw ordinal) (raw (ordinal + 1))
    let floor := visibleFloor c β (raw ordinal) (raw (ordinal + 1))
    0 < floor ∧ ∃ lag : Nat, 0 < lag ∧ lag ≤ limit ∧ floor < ‖fee (ordinal + 1 + lag)‖ := by
  have step : R c (raw ordinal) = raw (ordinal + 1) := by
    rw [OriginalKCombFirstFullSourceDynamics.raw_successor, OriginalKCombCofinalRAction.original_R_direct]
    rfl
  have paid : β (raw (ordinal + 1)) ≠ 0 := by
    rw [← ReentryDifferenceClock.literal_fee observation nontrivial half depth (ordinal + 1)]
    exact live
  have window := finite_future_test c β (raw ordinal) (raw (ordinal + 1)) step paid
  refine ⟨window.1, window.2.elim ?_⟩
  intro lag witness
  refine ⟨lag, witness.1, witness.2.1, ?_⟩
  rw [ReentryDifferenceClock.literal_fee observation nontrivial half depth (ordinal + 1 + lag),
    native_powers observation nontrivial half depth (ordinal + 1) lag]
  exact witness.2.2

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.NextLiveWindow
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
