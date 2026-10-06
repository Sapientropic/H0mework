import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-! The scalar integral for every actual finite-compression spectral coordinate. -/
set_option autoImplicit false
noncomputable section
namespace LowEnergy.SourceResolventLorentzian
open MeasureTheory Real

def kernel (μ a t : ℝ) : ℝ := ((a-t)^2+μ^2)⁻¹

private theorem kernel_scale (μ a t : ℝ) (hμ : 0<μ) :
    kernel μ a t=(μ^2)⁻¹*(1+((t-a)/μ)^2)⁻¹ := by
  unfold kernel
  have h1 : 1+((t-a)/μ)^2≠0 := by positivity
  have h2 : (a-t)^2+μ^2≠0 := by positivity
  field_simp [hμ.ne',h1,h2]
  ring

theorem kernel_integrable (μ a : ℝ) (hμ : 0<μ) : Integrable (kernel μ a) := by
  have h := (integrable_inv_one_add_sq.comp_div hμ.ne').comp_sub_right a
  have hs := h.const_mul ((μ^2)⁻¹)
  apply hs.congr
  exact Filter.Eventually.of_forall (fun t => (kernel_scale μ a t hμ).symm)

theorem kernel_integral (μ a : ℝ) (hμ : 0<μ) :
    (∫ t, kernel μ a t)=Real.pi/μ := by
  simp_rw [kernel_scale μ a _ hμ]
  have hshift := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun x : ℝ => (1+(x/μ)^2)⁻¹) a
  rw [integral_const_mul,hshift,
    Measure.integral_comp_div (fun x : ℝ => (1+x^2)⁻¹) μ,
    integral_univ_inv_one_add_sq,abs_of_pos hμ]
  simp only [smul_eq_mul]
  field_simp

theorem inverse_norm_square (μ a t : ℝ) :
    ‖((a : ℂ)-((t : ℂ)+Complex.I*(μ : ℂ)))⁻¹‖^2=kernel μ a t := by
  rw [norm_inv,inv_pow,←Complex.normSq_eq_norm_sq]
  unfold kernel
  congr 1
  simp [Complex.normSq_apply,pow_two]

end LowEnergy.SourceResolventLorentzian
