import Mathlib.Tactic

/-! The original scale current generates a positive square before any range completion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourceKineticSquare
open scoped InnerProductSpace

section Algebra
variable {R : Type*} [Ring R] [Algebra ℂ R]

omit [Algebra ℂ R] in
private theorem commutator_product (D H U : R) :
    D*(H*U)-(H*U)*D=(D*H-H*D)*U+H*(D*U-U*D) := by noncomm_ring

theorem scale_current (H U D E : R) (c : ℝ)
    (scaleH : D*H-H*D=(2*Complex.I) • H-(8*Complex.I/3) • E)
    (scaleU : D*U-U*D=(-2*Complex.I) • U) (electric : E*U=U*E) :
    let Q := H*U+(2*Complex.I*(c : ℂ)) • D
    Q*D-D*Q=(8*Complex.I/3) • (U*E) := by
  dsimp only
  have h := commutator_product D H U
  rw [scaleH, scaleU, sub_mul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, electric] at h
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  have hn : (-2*Complex.I) • (H*U) = -((2*Complex.I) • (H*U)) := by
    rw [←neg_smul]
    congr 1
    ring
  rw [hn] at h
  have ht : D*(H*U)-(H*U)*D = -((8*Complex.I/3) • (U*E)) := by
    calc
      _ = (2*Complex.I) • (H*U)-(8*Complex.I/3) • (U*E)-
          (2*Complex.I) • (H*U) := by simpa only [sub_eq_add_neg] using h
      _ = _ := by abel
  calc
    _ = -(D*(H*U)-(H*U)*D) := by abel
    _ = _ := by rw [ht, neg_neg]

end Algebra

section Core
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem imaginary_norm (a b : E) (s : ℝ) :
    ‖a-((Complex.I*(s : ℂ)) • b)‖^2 =
      ‖a‖^2+s^2*‖b‖^2+2*s*(inner ℂ a b).im := by
  rw [norm_sub_sq (𝕜 := ℂ), norm_smul, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_right]
  norm_num [Complex.mul_re, Complex.mul_im]
  ring

theorem current_square {X : Type*} [AddCommGroup X] [Module ℂ X]
    (J : X →ₗ[ℂ] E) (Q D M : X →ₗ[ℂ] X)
    (qPair : ∀ x y, inner ℂ (J (Q x)) (J y)=inner ℂ (J x) (J (Q y)))
    (dPair : ∀ x y, inner ℂ (J (D x)) (J y)=inner ℂ (J x) (J (D y)))
    (current : Q*D-D*Q=(8*Complex.I/3) • M) (c : ℝ) (f : X) :
    ‖J (Q f-(2*Complex.I*(c : ℂ)) • D f)‖^2 =
      ‖J (Q f)‖^2+4*c^2*‖J (D f)‖^2+(16*c/3)*(inner ℂ (J f) (J (M f))).re := by
  have hp := congrArg (fun A : X →ₗ[ℂ] X => inner ℂ (J f) (J (A f))) current
  change inner ℂ (J f) (J (Q (D f)-D (Q f)))=
    inner ℂ (J f) (J ((8*Complex.I/3) • M f)) at hp
  rw [map_sub,map_smul,inner_smul_right] at hp
  rw [inner_sub_right, ←qPair f (D f), ←dPair f (Q f)] at hp
  have hi := congrArg Complex.im hp
  have him := inner_im_symm (𝕜 := ℂ) (J (Q f)) (J (D f))
  change (inner ℂ (J (Q f)) (J (D f))).im = -(inner ℂ (J (D f)) (J (Q f))).im at him
  norm_num [Complex.sub_im, Complex.mul_im, Complex.div_re, Complex.div_im] at hi
  have hcross : (inner ℂ (J (Q f)) (J (D f))).im=
      (4/3 : ℝ)*(inner ℂ (J f) (J (M f))).re := by linarith
  have hc : 2*Complex.I*(c : ℂ)=Complex.I*((2*c : ℝ) : ℂ) := by push_cast; ring
  rw [map_sub,map_smul,hc,imaginary_norm,hcross]
  ring

/-- An electric completed square and the scale current produce the kinetic cost. -/
theorem weighted_cost (Q D P W : E →ₗ[ℂ] E) (c : ℝ)
    (electricCost : E → ℝ) (remainderCost : E → ℝ)
    (scaleSquare : ∀ f, ‖P f‖^2=‖Q f‖^2+4*c^2*‖D f‖^2+electricCost f)
    (electricSquare : ∀ f, electricCost f=remainderCost f+(289/4 : ℝ)*‖W f‖^2)
    (nonnegative : ∀ f, 0 ≤ remainderCost f) (f : E) :
    ‖W f‖ ≤ (2/17 : ℝ)*‖P f‖ := by
  have hs := scaleSquare f
  rw [electricSquare f] at hs
  have hp : 0 ≤ 4*c^2*‖D f‖^2 := by positivity
  nlinarith [nonnegative f, norm_nonneg (P f), norm_nonneg (W f), sq_nonneg ‖Q f‖]

end Core
end LowEnergy.SourceKineticSquare
