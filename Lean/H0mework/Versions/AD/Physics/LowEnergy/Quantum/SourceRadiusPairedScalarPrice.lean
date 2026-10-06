import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceScalarEssentialBudget
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceRadiusPairedScalarPrice
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussDiagonalHistory GaussUnitaryHistory GaussRadialDomain GaussYukawaCoefficient GaussYukawaOperator
open SourceRelativePowerTail SourceMixedNativeReturn SourceScalarSignedInverseReturn
open FullYSourceCutoffVolterra FullYSourceCutoffSharp SourceRetardedIncrement SourceEscapeSeedTail
open SourceCutoffDilationWard SourceInverseNeutralSpinTail SourceScalarInverseEnergyBudget
open scoped ContDiff InnerProductSpace
abbrev Op := H →L[ℂ] H

private theorem commuting_positive_pair {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (A B : E →L[ℂ] E)
    (hA : 0 ≤ A) (hAB : Commute A B) (p q : E) :
    ‖inner ℂ p (B (A q))‖^2 ≤
      ‖B‖^2*(inner ℂ p (A p)).re*(inner ℂ q (A q)).re := by
  let S := CFC.sqrt A
  have hS : 0 ≤ S := CFC.sqrt_nonneg A
  have hs : ∀ x y,inner ℂ (S x) y=inner ℂ x (S y) :=
    ((ContinuousLinearMap.nonneg_iff_isPositive S).mp hS).isSymmetric
  have hss : S*S=A := CFC.sqrt_mul_sqrt_self A hA
  have hc : Commute S B := hAB.cfcₙ_nnreal NNReal.sqrt
  have he : inner ℂ p (B (A q))=inner ℂ (S p) (B (S q)) := by
    rw [hs,←hss]
    exact congrArg (inner ℂ p) (DFunLike.congr_fun hc.eq.symm (S q))
  have hn (x : E) : ‖S x‖^2=(inner ℂ x (A x)).re := by
    rw [←hss]
    change ‖S x‖^2=(inner ℂ x (S (S x))).re
    rw [←hs]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) (S x)).symm
  rw [he]
  have h := (norm_inner_le_norm (𝕜 := ℂ) (S p) (B (S q))).trans
    (mul_le_mul_of_nonneg_left (B.le_opNorm (S q)) (norm_nonneg _))
  have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
  simp only [mul_pow,hn] at hh
  exact hh.trans_eq (by ring)

/-- This is exactly r θ: a positive finite sum of powers of the original source complement. -/
def radiusBand (m ell : ℕ) : Op := ∑ j ∈ Finset.Ico (m+1) (ell+1),sourceComplement^j

/-- The two actual legs use a first radius moment, with no native-derivative energy added. -/
def radiusMoment (m ell : ℕ) (p : H) : ℝ := (inner ℂ p (radiusBand m ell p)).re

private theorem radius_band_positive (m ell : ℕ) : 0 ≤ radiusBand m ell := by
  unfold radiusBand
  exact Finset.sum_nonneg (fun j _ => CStarAlgebra.pow_nonneg source_complement_nonnegative j)

private theorem bounded_inverse : Commute GaussYukawaOperator.bounded inverseRadius := by
  apply ContinuousLinearMap.ext
  intro x
  refine GaussBoundedMultiplier.core_dense.induction_on
    (p := fun y : H => GaussYukawaOperator.bounded (inverseRadius y)=inverseRadius (GaussYukawaOperator.bounded y)) x
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  obtain ⟨f,rfl⟩ := coreEquiv.surjective a
  change GaussYukawaOperator.bounded (inverseRadius (embed f)) =
    inverseRadius (GaussYukawaOperator.bounded (embed f))
  rw [inverse_core,bounded_core,bounded_core,inverse_core]
  congr 1
  apply DFunLike.ext
  intro z
  exact map_smul (normalized z) (reciprocal z : ℂ) (f z)

private theorem complement_bounded : Commute sourceComplement GaussYukawaOperator.bounded :=
  (Commute.one_left _).sub_left bounded_inverse.symm

private theorem band_bounded (m ell : ℕ) : Commute (radiusBand m ell) GaussYukawaOperator.bounded := by
  unfold radiusBand
  exact Commute.sum_left _ _ _ (fun j _ => complement_bounded.pow_left j)

private theorem geometric_step {R : Type*} [Semiring R] (Q S B : R) :
    B+Q*(S*B)=(1+Q*S)*B := by
  rw [add_mul,one_mul,mul_assoc]

private theorem cutoff_sum (n : ℕ) : cutoff n=(∑ j ∈ Finset.range (n+1),sourceComplement^j)*GaussYukawaOperator.bounded := by
  induction n with
  | zero =>
    change GaussYukawaOperator.bounded = _
    rw [Finset.sum_range_one,pow_zero,one_mul]
  | succ n ih =>
    change GaussYukawaOperator.bounded+sourceComplement*cutoff n=_
    rw [ih]
    have hsum : (∑ j ∈ Finset.range (n+1+1),sourceComplement^j) =
        1+sourceComplement*(∑ j ∈ Finset.range (n+1),sourceComplement^j) := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero,Finset.mul_sum,←pow_succ']
      exact add_comm _ _
    exact (geometric_step sourceComplement _ GaussYukawaOperator.bounded).trans
      (congrArg (fun T : Op => T*GaussYukawaOperator.bounded) hsum.symm)

private theorem increment_band (m ell : ℕ) (hm : m ≤ ell) :
    increment m ell=radiusBand m ell*GaussYukawaOperator.bounded := by
  unfold increment
  rw [cutoff_sum,cutoff_sum,←sub_mul]
  have h := Finset.sum_range_add_sum_Ico (fun j => sourceComplement^j) (show m+1 ≤ ell+1 by omega)
  rw [←h,add_sub_cancel_left]
  rfl

private theorem actual_increment_band (sharp : Bool) (m ell : ℕ) (hm : m ≤ ell) :
    actualIncrement sharp m ell=(if sharp then GaussYukawaOperator.bounded.adjoint else GaussYukawaOperator.bounded)*radiusBand m ell := by
  cases sharp
  · exact (increment_band m ell hm).trans (band_bounded m ell).eq
  · change (cutoff ell).adjoint-(cutoff m).adjoint=_
    rw [←map_sub]
    change (increment m ell).adjoint=_
    rw [increment_band m ell hm]
    change star (radiusBand m ell*GaussYukawaOperator.bounded)=_
    rw [star_mul,(IsSelfAdjoint.of_nonneg (radius_band_positive m ell)).star_eq]
    rfl

private theorem band_sharp (m ell : ℕ) : Commute (radiusBand m ell) GaussYukawaOperator.bounded.adjoint := by
  have h := (band_bounded m ell).star_star
  rw [(IsSelfAdjoint.of_nonneg (radius_band_positive m ell)).star_eq] at h
  exact h

/-- Both independent source branches obey the paired first-radius price on the full Hilbert carrier. -/
theorem original_paired_radius_price (sharp : Bool) (m ell : ℕ) (hm : m ≤ ell) (p q : H) :
    ‖inner ℂ p (actualIncrement sharp m ell q)‖^2 ≤
      ‖GaussYukawaOperator.bounded‖^2*radiusMoment m ell p*radiusMoment m ell q := by
  rw [actual_increment_band sharp m ell hm]
  change ‖inner ℂ p ((if sharp then GaussYukawaOperator.bounded.adjoint else GaussYukawaOperator.bounded)
    (radiusBand m ell q))‖^2 ≤ _
  cases sharp
  · exact commuting_positive_pair _ _ (radius_band_positive m ell) (band_bounded m ell) p q
  · change ‖inner ℂ p (GaussYukawaOperator.bounded.adjoint (radiusBand m ell q))‖^2 ≤ _
    simpa only [radiusMoment,ContinuousLinearMap.adjoint.norm_map] using
      commuting_positive_pair _ _ (radius_band_positive m ell) (band_sharp m ell) p q

end LowEnergy.SourceRadiusPairedScalarPrice
