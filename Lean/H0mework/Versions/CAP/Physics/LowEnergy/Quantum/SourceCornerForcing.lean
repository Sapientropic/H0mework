import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceCornerWeight
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceEscapeSeedTail

/-! The literal native/sharp cutoff difference factors after its physical forcing weight. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourceCornerForcing
open GaussCoreHilbert GaussCoreDifferential GaussFockPair
open SourceSignedRadiusBalance SourceRelativePowerTail SourceEscapeSeedTail
open FullYSourceCutoffVolterra SourceRetardedIncrement SourceCornerWeight
open scoped ContDiff Topology

def sourceVertex (sharp : Bool) : H →L[ℂ] H :=
  if sharp then GaussYukawaOperator.bounded.adjoint else GaussYukawaOperator.bounded

def weighted : H →L[ℂ] H := multiplier * GaussRadialDomain.inverseRadius
def coefficientMap (sharp : Bool) : H →L[ℂ] H := multiplier * sourceVertex sharp

private theorem reciprocal_geometric {R : Type*} [Ring R] (S : R) (n : ℕ) :
    S * (∑ j ∈ Finset.range (n+1), (1-S)^j) = 1-(1-S)^(n+1) := by
  have hc : S*(1-S)=(1-S)*S := by simp only [mul_sub, sub_mul, mul_one, one_mul]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [geom_sum_succ, mul_add, mul_one, ←mul_assoc S (1-S), hc, mul_assoc, ih,
      mul_sub, mul_one, ←pow_succ']
    abel

private theorem inverse_radius_sum (n : ℕ) :
    GaussRadialDomain.inverseRadius * radiusCutoff n = 1 - sourceComplement ^ (n+1) :=
  reciprocal_geometric _ n

private theorem delta_algebra {R : Type*} [Ring R] (S B L M Q T : R)
    (hSB : S*B=B*S) (hL : S*L=1-T) (hM : S*M=1-Q) :
    S*(B*(L-M))=B*(Q-T) := by
  rw [←mul_assoc S B, hSB, mul_assoc, mul_sub, hL, hM]
  congr 1
  abel

private theorem inverse_vertex (sharp : Bool) :
    GaussRadialDomain.inverseRadius * sourceVertex sharp =
      sourceVertex sharp * GaussRadialDomain.inverseRadius := by
  cases sharp
  · exact bounded_inverse_commute.eq.symm
  · have hs : IsSelfAdjoint GaussRadialDomain.inverseRadius :=
      (show GaussRadialDomain.inverseRadius.toLinearMap.IsSymmetric from
        fun x y => GaussRadialDomain.inverse_pair x y).isSelfAdjoint
    have h := congrArg star bounded_inverse_commute.eq
    change GaussRadialDomain.inverseRadius * GaussYukawaOperator.bounded.adjoint =
      GaussYukawaOperator.bounded.adjoint * GaussRadialDomain.inverseRadius
    simpa only [star_mul, hs.star_eq] using! h

theorem actual_increment_factor (sharp : Bool) (m ell : ℕ) :
    GaussRadialDomain.inverseRadius * actualIncrement sharp m ell =
      sourceVertex sharp * relativeTail m ell := by
  have hd : actualIncrement sharp m ell =
      sourceVertex sharp * (radiusCutoff ell-radiusCutoff m) := by
    cases sharp
    · simp only [actualIncrement, Bool.false_eq_true, if_false, increment,
        sourceVertex, cutoff_radius_factor, mul_sub]
    · simp only [actualIncrement, if_true, sharpIncrement, sourceVertex,
        sharp_radius_factor, mul_sub]
  exact (congrArg (fun A => GaussRadialDomain.inverseRadius*A) hd).trans
    (delta_algebra _ _ _ _ _ _ (inverse_vertex sharp)
      (inverse_radius_sum ell) (inverse_radius_sum m))

theorem weighted_increment (sharp : Bool) (m ell : ℕ) :
    weighted * actualIncrement sharp m ell = coefficientMap sharp * relativeTail m ell := by
  exact (mul_assoc multiplier GaussRadialDomain.inverseRadius
    (actualIncrement sharp m ell)).trans
      ((congrArg (fun A => multiplier*A) (actual_increment_factor sharp m ell)).trans
        (mul_assoc multiplier (sourceVertex sharp) (relativeTail m ell)).symm)

theorem coefficient_map_norm (sharp : Bool) :
    ‖coefficientMap sharp‖ ≤ ‖GaussYukawaOperator.bounded‖/8 := by
  have hv : ‖sourceVertex sharp‖ = ‖GaussYukawaOperator.bounded‖ := by
    cases sharp <;> simp [sourceVertex]
  apply (norm_mul_le multiplier (sourceVertex sharp)).trans
  rw [hv]
  exact (mul_le_mul_of_nonneg_right multiplier_norm (norm_nonneg _)).trans_eq (by ring)

theorem weighted_increment_bound (sharp : Bool) (m ell : ℕ) (x : H) :
    ‖weighted (actualIncrement sharp m ell x)‖ ≤
      (‖GaussYukawaOperator.bounded‖/8) * ‖relativeTail m ell x‖ := by
  change ‖(weighted*actualIncrement sharp m ell) x‖ ≤ _
  rw [weighted_increment, mul_apply_eq_comp]
  exact ((coefficientMap sharp).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (coefficient_map_norm sharp) (norm_nonneg _))

end LowEnergy.SourceCornerForcing
