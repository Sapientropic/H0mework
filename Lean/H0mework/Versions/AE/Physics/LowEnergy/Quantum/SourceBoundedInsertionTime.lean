import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceBoundedInsertionResponse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourceBoundedInsertionTime
open GaussCoreHilbert GaussDiagonalHistory GaussUnitaryHistory SourceBoundedInsertionResponse
open MeasureTheory Filter
open scoped Topology

/-- Angular-frequency inverse transform, with the explicit 1/(2π) convention. -/
def timeTransform (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ((2*Real.pi)⁻¹ : ℝ) • ∫ w : ℝ,Complex.exp ((-(w*t) : ℝ)*Complex.I)*f w

def response (F : Index) (μ : ℝ) (A : H →L[ℂ] H) (g k : H) : ℝ → ℂ :=
  timeTransform (amplitude F μ A g k)

def wholeResponse (μ : ℝ) (hμ : 0<μ) (A : H →L[ℂ] H) (g k : H) : ℝ → ℂ :=
  timeTransform (wholeAmplitude μ hμ A g k)

private theorem phase_integrable (f : ℝ → ℂ) (hf : Integrable f) (t : ℝ) :
    Integrable (fun w : ℝ => Complex.exp ((-(w*t) : ℝ)*Complex.I)*f w) := by
  have hc : Continuous (fun w : ℝ => Complex.exp ((-(w*t) : ℝ)*Complex.I)) := by fun_prop
  exact hf.norm.mono' (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (Eventually.of_forall (fun w => by rw [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]))

private theorem transform_error (f p : ℝ → ℂ) (hf : Integrable f) (hp : Integrable p) (t : ℝ) :
    ‖timeTransform f t-timeTransform p t‖ ≤ (2*Real.pi)⁻¹*(∫ w : ℝ,‖f w-p w‖) := by
  unfold timeTransform
  rw [←smul_sub,←integral_sub (phase_integrable f hf t) (phase_integrable p hp t),norm_smul,
    Real.norm_eq_abs,abs_of_pos (by positivity : 0<(2*Real.pi)⁻¹)]
  refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans_eq ?_) (by positivity)
  apply integral_congr_ae
  exact Eventually.of_forall (fun w => by
    dsimp only
    rw [←mul_sub,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul])

/-- A single full-frequency error controls every real time simultaneously. -/
theorem actual_time_error (F : Index) (μ : ℝ) (hμ : 0<μ) (A : H →L[ℂ] H)
    (g k : diagonal.domain) (t : ℝ) :
    ‖response F μ A (g : H) (k : H) t-wholeResponse μ hμ A (g : H) (k : H) t‖ ≤
      (2*Real.pi)⁻¹*(∫ w : ℝ,‖amplitude F μ A (g : H) (k : H) w-
        wholeAmplitude μ hμ A (g : H) (k : H) w‖) := by
  obtain ⟨hf,hp,_⟩ := actual_full_frequency_response μ hμ A g k
  exact transform_error _ _ (hf F) hp t

/-- The original sourceFilter generates convergence uniform on the whole time axis. -/
theorem actual_uniform_time_response (μ : ℝ) (hμ : 0<μ) (A : H →L[ℂ] H)
    (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∀ᶠ F : Index in (sourceFilter : Filter Index),∀ t : ℝ,
      ‖response F μ A (g : H) (k : H) t-wholeResponse μ hμ A (g : H) (k : H) t‖<ε := by
  intro ε hε
  have h := (actual_full_frequency_response μ hμ A g k).2.2.const_mul ((2*Real.pi)⁻¹)
  simp only [mul_zero] at h
  filter_upwards [(tendsto_order.mp h).2 ε hε] with F hF
  intro t
  exact (actual_time_error F μ hμ A g k t).trans_lt hF

end LowEnergy.SourceBoundedInsertionTime
