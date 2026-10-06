import H0mework.Realization.Perfectification.Quantum.Forms.Ground.Spectral
import H0mework.Realization.Perfectification.Quantum.Forms.Energy

/-! Approximate norm eigenvectors of the generated resolvent are mapped
into its actual range. Normalization then gives approximate energy vectors
in the inverse-minus-identity operator's own domain. -/

set_option autoImplicit false

namespace SaturationMonoid.Quantum.Forms.Approximate

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
  (R : H →L[ℂ] H) (injective : Function.Injective R)

def energy : ℝ := ‖R‖⁻¹ - 1

omit [Nontrivial H] in
def normalizedPoint (x : H) : (Inverse.operator R injective).domain :=
  (‖R x‖ : ℂ)⁻¹ • Inverse.point R injective x

omit [CompleteSpace H] [Nontrivial H] in
private theorem normalizedPoint_norm (x : H) (nonzero : R x ≠ 0) :
    ‖(normalizedPoint R injective x).val‖ = 1 := norm_smul_inv_norm nonzero

omit [CompleteSpace H] in
private theorem normalized_residual (x : H) :
    ‖Inverse.operator R injective (normalizedPoint R injective x) -
      (energy R : ℂ) • (normalizedPoint R injective x).val‖ =
      ‖R x - (‖R‖ : ℂ) • x‖ / (‖R‖ * ‖R x‖) := by
  have normNonzero : (‖R‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_positive R injective).ne'
  have raw : Inverse.operator R injective (Inverse.point R injective x) - (energy R : ℂ) • R x =
      -((‖R‖ : ℂ)⁻¹ • (R x - (‖R‖ : ℂ) • x)) := by
    rw [Inverse.operator_point]
    simp only [energy, Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_one,
      sub_smul, one_smul, smul_sub, smul_smul, inv_mul_cancel₀ normNonzero]
    abel
  change ‖Inverse.operator R injective ((‖R x‖ : ℂ)⁻¹ • Inverse.point R injective x) -
      (energy R : ℂ) • ((‖R x‖ : ℂ)⁻¹ • R x)‖ = _
  rw [LinearPMap.map_smul, smul_comm (energy R : ℂ) (‖R x‖ : ℂ)⁻¹, ← smul_sub, raw]
  simp only [norm_smul, norm_neg, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg R), Real.norm_of_nonneg (norm_nonneg (R x)),
    div_eq_mul_inv, mul_inv]
  ring

theorem inverse_approximate (positive : R.IsPositive) (ε : ℝ) (epsilon : 0 < ε) :
    ∃ v : (Inverse.operator R injective).domain, ‖v.val‖ = 1 ∧
      ‖Inverse.operator R injective v - (energy R : ℂ) • v.val‖ < ε := by
  have normPositive := norm_positive R injective
  let δ := min (‖R‖ / 2) (ε * ‖R‖ ^ 2 / 4)
  have δpositive : 0 < δ := lt_min (by positivity) (by positivity)
  obtain ⟨x, unit, small⟩ := norm_approximate R positive δ δpositive
  have first : ‖R x - (‖R‖ : ℂ) • x‖ < ‖R‖ / 2 := small.trans_le (min_le_left _ _)
  have second : ‖R x - (‖R‖ : ℂ) • x‖ < ε * ‖R‖ ^ 2 / 4 := small.trans_le (min_le_right _ _)
  have distance := norm_sub_norm_le ((‖R‖ : ℂ) • x) (R x)
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg R), unit, mul_one,
    norm_sub_rev] at distance
  have rangeLower : ‖R‖ / 2 < ‖R x‖ := by linarith
  have rangePositive : 0 < ‖R x‖ := lt_trans (by positivity) rangeLower
  refine ⟨normalizedPoint R injective x, normalizedPoint_norm R injective x (norm_pos_iff.mp rangePositive), ?_⟩
  rw [normalized_residual, div_lt_iff₀ (mul_pos normPositive rangePositive)]
  have product := mul_lt_mul_of_pos_left rangeLower (mul_pos epsilon normPositive)
  nlinarith

omit [CompleteSpace H] in
include injective in
theorem energy_nonnegative (contractive : ‖R‖ ≤ 1) : 0 ≤ energy R := by
  exact sub_nonneg.mpr ((one_le_inv₀ (norm_positive R injective)).mpr contractive)

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem graph_approximate (A : H →ₗ.[ℂ] F) (closed : A.IsClosed) (dense : Dense (A.domain : Set H))
    (ε : ℝ) (epsilon : 0 < ε) :
    ∃ v : (Forms.hamiltonian A closed dense).domain, ‖v.val‖ = 1 ∧
      ‖Forms.hamiltonian A closed dense v - (energy (Graph.resolvent A closed) : ℂ) • v.val‖ < ε :=
  inverse_approximate (Graph.resolvent A closed) (Graph.resolvent_injective A closed dense)
    (Graph.resolvent_positive A closed) ε epsilon

theorem graph_energy_nonnegative (A : H →ₗ.[ℂ] F) (closed : A.IsClosed) (dense : Dense (A.domain : Set H)) :
    0 ≤ energy (Graph.resolvent A closed) :=
  energy_nonnegative (Graph.resolvent A closed) (Graph.resolvent_injective A closed dense)
    (Graph.resolvent_norm_le_one A closed)

end
end SaturationMonoid.Quantum.Forms.Approximate
