import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyEnergySource
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRSourceJointContact.OutsideHistory.FinitePowerWindow

open Complex CenteredGram.IntegralGraphJointAction
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped BigOperators

local notation "R" => burnolDirectRightResolventCLM
local notation "C" => sourceCayley
local notation "δ" => sourceDamping
local notation "End" => (BurnolL2 →L[ℂ] BurnolL2)

private def shift (c d : BurnolCompletedMellinCoordinate) : ℂ := d.value / 2 - c.value / 2

/-- The actual Cayley rescales a parameter shift into a strict scalar contraction. -/
def ratio (c d : BurnolCompletedMellinCoordinate) : ℂ :=
  shift c d / ((δ c : ℂ) + shift c d)

private theorem denominator_gap (c d : BurnolCompletedMellinCoordinate) :
    ‖(δ c : ℂ) + shift c d‖ ^ 2 - ‖shift c d‖ ^ 2 = δ c * δ d := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp [shift, sourceDamping, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.div_ofNat_re, Complex.div_ofNat_im]
  ring

private theorem denominator_lt (c d : BurnolCompletedMellinCoordinate) :
    ‖shift c d‖ < ‖(δ c : ℂ) + shift c d‖ := by
  have positive := mul_pos (sourceDamping_pos c) (sourceDamping_pos d)
  have gap := denominator_gap c d
  exact (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith)

private theorem denominator_ne_zero (c d : BurnolCompletedMellinCoordinate) :
    (δ c : ℂ) + shift c d ≠ 0 :=
  norm_pos_iff.mp ((norm_nonneg _).trans_lt (denominator_lt c d))

theorem ratio_norm_lt_one (c d : BurnolCompletedMellinCoordinate) : ‖ratio c d‖ < 1 := by
  rw [ratio, norm_div]
  exact (div_lt_one ((norm_nonneg _).trans_lt (denominator_lt c d))).mpr (denominator_lt c d)

private theorem right_quarter (c : BurnolCompletedMellinCoordinate) : 1 / 4 < (c.value / 2).re := by
  rw [Complex.div_re]
  norm_num
  linarith [c.rightHalf]

private theorem actual_step (c d : BurnolCompletedMellinCoordinate) :
    R d * (1 - ratio c d • C c) = (1 - ratio c d) • R c := by
  apply ContinuousLinearMap.ext
  intro v
  have paid : R d v - R c v = shift c d • R d (R c v) :=
    burnolDirectRightResolvent_identity (d.value / 2) (c.value / 2)
      (right_quarter d) (right_quarter c) v
  have balance : ratio c d * (δ c : ℂ) = (1 - ratio c d) * shift c d := by
    unfold ratio
    field_simp [denominator_ne_zero c d]
    ring
  change R d (v - ratio c d • (v + (δ c : ℂ) • R c v)) = _
  simp only [map_sub, map_smul, map_add, smul_add, smul_smul, balance,
    _root_.smul_apply]
  linear_combination (norm := module) (1 - ratio c d) • paid

/-- Every term of the truncated Cayley series expands into strictly positive original R powers. -/
def weight (c d : BurnolCompletedMellinCoordinate) (k j : ℕ) : ℂ :=
  (1 - ratio c d) * ratio c d ^ k * (k.choose j : ℂ) * (δ c : ℂ) ^ j

def finiteResolvent (c d : BurnolCompletedMellinCoordinate) (N : ℕ) : End :=
  ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (k + 1), weight c d k j • (R c) ^ (j + 1)

private theorem cayley_binomial (c : BurnolCompletedMellinCoordinate) (k : ℕ) :
    C c ^ k = ∑ j ∈ Finset.range (k + 1), ((k.choose j : ℂ) * (δ c : ℂ) ^ j) • (R c) ^ j := by
  have swapped : C c = (δ c : ℂ) • R c + 1 := add_comm _ _
  rw [swapped, (Commute.one_right ((δ c : ℂ) • R c)).add_pow' k]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun j l =>
    k.choose j • (((δ c : ℂ) • R c) ^ j * (1 : End) ^ l))]
  simp only [one_pow, mul_one, smul_pow, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]

private theorem finite_geometric (c d : BurnolCompletedMellinCoordinate) (N : ℕ) :
    finiteResolvent c d N = (1 - ratio c d) •
      (R c * ∑ k ∈ Finset.range N, (ratio c d • C c) ^ k) := by
  unfold finiteResolvent
  simp only [Finset.mul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [smul_pow, cayley_binomial, mul_smul_comm, Finset.mul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← pow_succ', smul_smul, smul_smul]
  congr 1
  unfold weight
  ring

/-- The original source action computes the exact error of every finite positive-power filter. -/
theorem actual_resolvent_remainder (c d : BurnolCompletedMellinCoordinate) (N : ℕ) :
    R d - finiteResolvent c d N = R d * (ratio c d • C c) ^ N := by
  let M := ratio c d • C c
  have exactStep := congrArg (fun T : End => T * ∑ k ∈ Finset.range N, M ^ k) (actual_step c d)
  change R d * (1 - M) * (∑ k ∈ Finset.range N, M ^ k) =
    ((1 - ratio c d) • R c) * (∑ k ∈ Finset.range N, M ^ k) at exactStep
  rw [mul_assoc, mul_neg_geom_sum, mul_sub, mul_one, smul_mul_assoc, ← finite_geometric] at exactStep
  change R d - finiteResolvent c d N = R d * M ^ N
  linear_combination (norm := module) exactStep

private theorem cayley_power_norm (c : BurnolCompletedMellinCoordinate) (N : ℕ) (v : BurnolL2) :
    ‖(C c ^ N) v‖ = ‖v‖ := by
  induction N with
  | zero => rfl
  | succ n before =>
    rw [pow_succ', mul_apply_eq_comp, sourceCayley_norm, before]

theorem actual_resolvent_remainder_bound (c d : BurnolCompletedMellinCoordinate) (N : ℕ) (v : BurnolL2) :
    ‖R d v - finiteResolvent c d N v‖ ≤ ‖R d‖ * ‖ratio c d‖ ^ N * ‖v‖ := by
  have read := congrArg (fun T : End => T v) (actual_resolvent_remainder c d N)
  change R d v - finiteResolvent c d N v = R d (((ratio c d • C c) ^ N) v) at read
  rw [read]
  have mapBound := (R d).le_opNorm (((ratio c d • C c) ^ N) v)
  simpa only [smul_pow, _root_.smul_apply, norm_smul, norm_pow, cayley_power_norm,
    mul_assoc] using mapBound

end OriginalRSourceJointContact.OutsideHistory.FinitePowerWindow
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
