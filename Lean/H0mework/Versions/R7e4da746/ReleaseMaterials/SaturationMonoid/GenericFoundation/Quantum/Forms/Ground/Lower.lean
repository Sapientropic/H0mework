import H0mework.Realization.Perfectification.Quantum.Forms.Ground.Approximate

/-! CFC order on the same positive resolvent gives the energy lower bound
on every point of the inverse operator's actual domain. -/

set_option autoImplicit false

open scoped InnerProductSpace

namespace SaturationMonoid.Quantum.Forms.Approximate

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]

theorem resolvent_square_le (R : H →L[ℂ] H) (positive : R.IsPositive) : R * R ≤ ‖R‖ • R := by
  have nonnegative : 0 ≤ R := (ContinuousLinearMap.nonneg_iff_isPositive R).mpr positive
  have compare : cfc (fun x : ℝ => id x * id x) R ≤ cfc (fun x : ℝ => ‖R‖ * id x) R := by
    refine cfc_mono ?_ (continuous_id.mul continuous_id).continuousOn
      (continuous_const.mul continuous_id).continuousOn
    intro x hx
    exact mul_le_mul_of_nonneg_right
      ((Real.le_norm_self x).trans (spectrum.norm_le_norm_of_mem hx))
      (spectrum_nonneg_of_nonneg nonnegative hx)
  rw [cfc_mul id id R, cfc_const_mul ‖R‖ id R, cfc_id ℝ R positive.isSelfAdjoint] at compare
  exact compare

theorem resolvent_quadratic (R : H →L[ℂ] H) (positive : R.IsPositive) (x : H) :
    ‖R x‖ ^ 2 ≤ ‖R‖ * (inner ℂ (R x) x).re := by
  have bound := ((ContinuousLinearMap.le_def _ _).mp (resolvent_square_le R positive)).re_inner_nonneg_left x
  have symmetric : (inner ℂ (R (R x)) x).re = ‖R x‖ ^ 2 :=
    (congrArg Complex.re (positive.isSymmetric (R x) x)).trans (inner_self_eq_norm_sq (𝕜 := ℂ) (R x))
  have scaled : (inner ℂ ((‖R‖ • R) x) x).re = ‖R‖ * (inner ℂ (R x) x).re := by
    change (inner ℂ (‖R‖ • R x) x).re = _
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left]
    simp
  change 0 ≤ (inner ℂ (((‖R‖ • R) x) - R (R x)) x).re at bound
  rw [inner_sub_left, Complex.sub_re, scaled, symmetric] at bound
  exact sub_nonneg.mp bound

variable (R : H →L[ℂ] H) (injective : Function.Injective R) (positive : R.IsPositive)

include positive in
private theorem point_lower (x : H) : energy R * ‖R x‖ ^ 2 ≤
    (inner ℂ (Inverse.operator R injective (Inverse.point R injective x)) (R x)).re := by
  have bound := resolvent_quadratic R positive x
  have symmetry : (inner ℂ (R x) x).re = (inner ℂ x (R x)).re := inner_re_symm (𝕜 := ℂ) (R x) x
  have bound' := bound.trans_eq (congrArg (fun r : ℝ => ‖R‖ * r) symmetry)
  have divided : ‖R x‖ ^ 2 / ‖R‖ ≤ (inner ℂ x (R x)).re := by
    apply (div_le_iff₀ (norm_positive R injective)).mpr
    exact bound'.trans_eq (mul_comm _ _)
  calc
    _ = ‖R x‖ ^ 2 / ‖R‖ - ‖R x‖ ^ 2 := by unfold energy; ring
    _ ≤ (inner ℂ x (R x)).re - ‖R x‖ ^ 2 := sub_le_sub_right divided _
    _ = _ := by
      rw [Inverse.operator_point, inner_sub_left, Complex.sub_re]
      exact congrArg (fun r : ℝ => (inner ℂ x (R x)).re - r)
        (inner_self_eq_norm_sq (𝕜 := ℂ) (R x)).symm

include positive in
theorem inverse_lower (v : (Inverse.operator R injective).domain) :
    energy R * ‖v.val‖ ^ 2 ≤ (inner ℂ (Inverse.operator R injective v) v.val).re := by
  have original := point_lower R injective positive (Inverse.preimage R injective v)
  have same : R (Inverse.preimage R injective v) = v.val := Inverse.preimage_apply R injective v
  simpa only [same, Inverse.point_preimage] using original

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem graph_lower (A : H →ₗ.[ℂ] F) (closed : A.IsClosed) (dense : Dense (A.domain : Set H))
    (v : (Forms.hamiltonian A closed dense).domain) :
    energy (Graph.resolvent A closed) * ‖v.val‖ ^ 2 ≤
      (inner ℂ (Forms.hamiltonian A closed dense v) v.val).re :=
  inverse_lower (Graph.resolvent A closed) (Graph.resolvent_injective A closed dense)
    (Graph.resolvent_positive A closed) v

end
end SaturationMonoid.Quantum.Forms.Approximate
