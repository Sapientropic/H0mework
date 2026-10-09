import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceScalarEssentialBudget
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceFourPoleEnergyClosed
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ScalarCausalFrequencyMoment
open MeasureTheory Filter SourceJointResidualEnergy SourceFourPoleEnergyClosed
open SourceResolventBandLimit
open scoped Topology

private theorem pole_den_ne (μ a ω : ℝ) (hμ : 0 < μ) :
    (a : ℂ) - line μ ω ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, line_im, Complex.zero_im,
    zero_sub, neg_eq_zero] at hi
  exact hμ.ne' hi

private theorem triple_partial_fraction (μ a b ω : ℝ) (hμ : 0 < μ) :
    star (pole μ a ω) ^ 2 * pole μ b ω =
      (-Complex.I / gap μ a b) *
        (star (pole μ a ω) * pole μ b ω - star (pole μ a ω) ^ 2) := by
  let A : ℂ := star ((a : ℂ) - line μ ω)
  let C : ℂ := (b : ℂ) - line μ ω
  have ha : A ≠ 0 := star_ne_zero.mpr (pole_den_ne μ a ω hμ)
  have hc : C ≠ 0 := pole_den_ne μ b ω hμ
  have hd : A - C = Complex.I * gap μ a b := by
    dsimp only [A, C]
    simp only [line, gap, Complex.star_def, map_sub, map_add, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    linear_combination (norm := ring) ((a : ℂ)-(b : ℂ))*Complex.I_mul_I
  have hn : A - C ≠ 0 := by rw [hd]; exact mul_ne_zero Complex.I_ne_zero (gap_ne μ a b hμ)
  have h : A⁻¹ ^ 2 * C⁻¹ = (A-C)⁻¹ * (A⁻¹*C⁻¹-A⁻¹ ^ 2) := by
    field_simp [ha, hc, hn]
  have hi : (Complex.I * gap μ a b)⁻¹ = -Complex.I / gap μ a b := by
    field_simp [Complex.I_ne_zero, gap_ne μ a b hμ]
    all_goals linear_combination (norm := ring) Complex.I_mul_I
  rw [hd, hi] at h
  simpa only [A, C, pole, star_inv₀] using h

private theorem conjugate_square_integrable (μ a : ℝ) (hμ : 0 < μ) :
    Integrable (fun ω : ℝ => star (pole μ a ω) ^ 2) := by
  have h := (RCLike.conjLIE (K := ℂ)).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
    (same_half_integrable μ a a hμ)
  exact h.congr (Eventually.of_forall (fun ω => by
    change star (pole μ a ω * pole μ a ω) = star (pole μ a ω) ^ 2
    rw [star_mul, pow_two]))

theorem actual_scalar_causal_triple_integrable (μ a b : ℝ) (hμ : 0 < μ) :
    Integrable (fun ω : ℝ => star (pole μ a ω) ^ 2 * pole μ b ω) := by
  have hp := two_pole_integrable μ a b hμ
  have hs := conjugate_square_integrable μ a hμ
  have h := (hp.sub hs).const_mul (-Complex.I / gap μ a b)
  exact h.congr (Eventually.of_forall (fun ω => by
    exact (triple_partial_fraction μ a b ω hμ).symm))

/-- The full ordered causal derivative kernel retains spectral collisions and
escape. Its sign will be paid by the positive source form, after summation. -/
theorem actual_scalar_causal_triple_integral (μ a b : ℝ) (hμ : 0 < μ) :
    (∫ ω : ℝ, star (pole μ a ω) ^ 2 * pole μ b ω) =
      (-2 * Real.pi : ℂ) * Complex.I / gap μ a b ^ 2 := by
  have hp := two_pole_integrable μ a b hμ
  have hs := conjugate_square_integrable μ a hμ
  have hzero : (∫ ω : ℝ, star (pole μ a ω) ^ 2) = 0 := by
    have h : (∫ ω : ℝ, star (polePair μ a a ω)) = star (∫ ω : ℝ, polePair μ a a ω) := integral_conj
    rw [same_half_integral μ a a hμ, star_zero] at h
    simpa only [polePair, star_mul, pow_two] using h
  simp_rw [triple_partial_fraction μ a b _ hμ]
  rw [integral_const_mul, integral_sub hp hs, hzero, sub_zero]
  change (-Complex.I / gap μ a b) * twoPole μ a b = _
  rw [two_pole_closed μ a b hμ]
  field_simp [gap_ne μ a b hμ]
end LowEnergy.ScalarCausalFrequencyMoment
