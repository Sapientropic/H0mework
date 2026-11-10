import H0mework.Quantum.Generator.SelfAdjoint

/-! A norm derivative of actual unitary conjugation preserves the original
generator domain. Its commutator identity turns a generated energy lower
bound into the exact residual estimate used by the limiting vector state. -/

set_option autoImplicit false

open scoped InnerProductSpace

namespace SaturationMonoid.Quantum.Generator.Commutator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* (H ≃ₗᵢ[ℂ] H))

def conjugation (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  (U (Multiplicative.ofAdd t)).conjStarAlgEquiv A

theorem conjugation_zero (A : H →L[ℂ] H) : conjugation U A 0 = A := by
  unfold conjugation
  rw [show U (Multiplicative.ofAdd 0) = 1 from U.map_one]
  rfl

theorem conjugation_orbit (A : H →L[ℂ] H) (v : H) (t : ℝ) :
    conjugation U A t (orbit U v t) = orbit U (A v) t := by
  change U (Multiplicative.ofAdd t) (A ((U (Multiplicative.ofAdd t)).symm
    (U (Multiplicative.ofAdd t) v))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

variable (A D : H →L[ℂ] H) (derivative : HasDerivAt (conjugation U A) D 0)

include derivative

theorem action_hasDerivAt (v : domain U) :
    HasDerivAt (orbit U (A v.val)) (D v.val + A (generator U v)) 0 := by
  have realDerivative := (ContinuousLinearMap.restrictScalarsL ℂ H H ℝ ℝ).hasFDerivAt.comp_hasDerivAt 0 derivative
  have generated := realDerivative.clm_apply (hasDerivAt_zero U v)
  change HasDerivAt (fun t => conjugation U A t (orbit U v.val t))
    (D (orbit U v.val 0) + conjugation U A 0 (generator U v)) 0 at generated
  simpa only [conjugation_orbit, orbit_zero, conjugation_zero] using generated

theorem action_mem_domain (v : domain U) : A v.val ∈ domain U :=
  (action_hasDerivAt U A D derivative v).differentiableAt

def domainAction (v : domain U) : domain U := ⟨A v.val, action_mem_domain U A D derivative v⟩

theorem hamiltonian_action (v : domain U) :
    hamiltonian U (domainAction U A D derivative v) =
      A (hamiltonian U v) + Complex.I • D v.val := by
  change Complex.I • deriv (orbit U (A v.val)) 0 =
    A (Complex.I • generator U v) + Complex.I • D v.val
  rw [(action_hasDerivAt U A D derivative v).deriv, map_smul, smul_add, add_comm]

theorem energy_error (E0 : ℝ)
    (lower : ∀ w : domain U, E0 * ‖w.val‖ ^ 2 ≤ (inner ℂ (hamiltonian U w) w.val).re)
    (v : domain U) (unit : ‖v.val‖ = 1) :
    -(‖A‖ ^ 2 * ‖hamiltonian U v - (E0 : ℂ) • v.val‖) ≤
      (inner ℂ (Complex.I • D v.val) (A v.val)).re := by
  let r : H := hamiltonian U v - (E0 : ℂ) • v.val
  have errorBound : (inner ℂ (A r) (A v.val)).re ≤ ‖A‖ ^ 2 * ‖r‖ := by
    calc
      _ ≤ ‖inner ℂ (A r) (A v.val)‖ := Complex.re_le_norm _
      _ ≤ ‖A r‖ * ‖A v.val‖ := norm_inner_le_norm _ _
      _ ≤ (‖A‖ * ‖r‖) * (‖A‖ * ‖v.val‖) :=
        mul_le_mul (A.le_opNorm r) (A.le_opNorm v.val) (norm_nonneg _) (by positivity)
      _ = _ := by rw [unit]; ring
  have energyInner : (inner ℂ ((E0 : ℂ) • A v.val) (A v.val)).re = E0 * ‖A v.val‖ ^ 2 := by
    rw [inner_smul_left]
    simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact congrArg (fun s : ℝ => E0 * s) (inner_self_eq_norm_sq (𝕜 := ℂ) (A v.val))
  have decomposition : hamiltonian U (domainAction U A D derivative v) =
      A r + (E0 : ℂ) • A v.val + Complex.I • D v.val := by
    rw [hamiltonian_action]
    dsimp only [r]
    rw [map_sub, map_smul]
    abel
  have generated := lower (domainAction U A D derivative v)
  change E0 * ‖A v.val‖ ^ 2 ≤
    (inner ℂ (hamiltonian U (domainAction U A D derivative v)) (A v.val)).re at generated
  rw [decomposition, inner_add_left, inner_add_left, Complex.add_re, Complex.add_re, energyInner] at generated
  change -(‖A‖ ^ 2 * ‖r‖) ≤ _
  linarith

end
end SaturationMonoid.Quantum.Generator.Commutator
