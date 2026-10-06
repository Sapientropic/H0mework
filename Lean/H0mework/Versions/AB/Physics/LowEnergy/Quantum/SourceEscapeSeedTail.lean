import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceSupportLeakage
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceCutoffSharpCore
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussAdjointHistory
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The original finite-support escape has source-generated spectral tails. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceEscapeSeedTail
open Filter GaussCoreHilbert GaussDiagonalHistory
open GaussUnitaryHistory (Index sourceFilter)
open FullYSourceResolventGraphSplice FullYSourceCutoffVolterra
open SourceRetardedIncrement
open scoped Topology InnerProductSpace

private theorem escape_norm_le (F : Index) (x : H) :
    ‖escapeProjection F x‖ ≤ ‖x‖ := by
  change ‖(1-(supportSpan F).starProjection) x‖ ≤ ‖x‖
  rw [←Submodule.starProjection_orthogonal']
  exact (supportSpan F)ᗮ.norm_starProjection_apply_le x

private theorem one_seed_return (A : H →L[ℂ] H)
    (stable : ∀ x : diagonal.domain, A (x : H) ∈ diagonal.domain)
    (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ z : ℂ, z.im ≠ 0 →
      escapeProjection F (A (finiteResolvent F z (g : H))) =
        z⁻¹ • escapeProjection F (A (finiteResolvent F z (diagonal g))) := by
  filter_upwards [GaussGradedCompression.eventually_exact g,
    source_eventually_mem_support ⟨A (g : H),stable g⟩] with F hF hA
  intro z hz
  have hzero : escapeProjection F (A (g : H)) = 0 := by
    change A (g : H)-(supportSpan F).starProjection (A (g : H))=0
    rw [Submodule.starProjection_eq_self_iff.mpr hA,sub_self]
  have hr := congrArg (fun T : H →L[ℂ] H => T (g : H))
    (resolvent_compression _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change finiteResolvent F z (GaussGradedCompression.compression F (g : H)) =
    (g : H)+z • finiteResolvent F z (g : H) at hr
  rw [hF] at hr
  have h := congrArg (fun v : H => escapeProjection F (A v)) hr
  simp only [map_add,map_smul,hzero,zero_add] at h
  have hz0 : z ≠ 0 := by intro he; exact hz (he ▸ rfl)
  simpa only [smul_smul,inv_mul_cancel₀ hz0,one_smul] using
    (congrArg (fun v : H => z⁻¹ • v) h).symm

private theorem iterated_seed_return (A : H →L[ℂ] H)
    (stable : ∀ x : diagonal.domain, A (x : H) ∈ diagonal.domain)
    (g : diagonal.domain) (p : ℕ) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ z : ℂ, z.im ≠ 0 →
      escapeProjection F (A (finiteResolvent F z (g : H))) =
        (z⁻¹)^p • escapeProjection F
          (A (finiteResolvent F z (GaussAdjointHistory.iterate p g : H))) := by
  induction p with
  | zero =>
    filter_upwards [] with F z hz
    simp [GaussAdjointHistory.iterate]
  | succ p ih =>
    filter_upwards [ih,one_seed_return A stable (GaussAdjointHistory.iterate p g)]
      with F hF hp
    intro z hz
    rw [hF z hz,hp z hz,GaussAdjointHistory.iterate_step,smul_smul,pow_succ]

def sharpIncrement (m n : ℕ) : H →L[ℂ] H := (cutoff n).adjoint-(cutoff m).adjoint

def actualIncrement (sharp : Bool) (m n : ℕ) : H →L[ℂ] H :=
  if sharp then sharpIncrement m n else increment m n

private theorem actual_increment_core (sharp : Bool) (m n : ℕ)
    (g : diagonal.domain) : actualIncrement sharp m n (g : H) ∈ diagonal.domain := by
  cases sharp
  · exact (incrementCore m n g).property
  · exact diagonal.domain.sub_mem
      (FullYSourceCutoffSharp.cutoff_sharp_core_mem n g)
      (FullYSourceCutoffSharp.cutoff_sharp_core_mem m g)

/-- The cofinal set is chosen before every spectral parameter. -/
theorem source_power_return (sharp : Bool) (m n p : ℕ) (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ z : ℂ, z.im ≠ 0 →
      escapeProjection F (actualIncrement sharp m n (finiteResolvent F z (g : H))) =
        (z⁻¹)^p • escapeProjection F
          (actualIncrement sharp m n
            (finiteResolvent F z (GaussAdjointHistory.iterate p g : H))) :=
  iterated_seed_return _ (actual_increment_core sharp m n) g p

/-- Positive escaped norm: every extra inverse power is paid by the original H₀ jet. -/
theorem source_escape_spectral_bound (sharp : Bool) (m n p : ℕ) (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ z : ℂ, z.im ≠ 0 →
      ‖z⁻¹ • escapeProjection F
        (actualIncrement sharp m n (finiteResolvent F z (g : H)))‖ ≤
      (‖z‖⁻¹)^(p+1) *
        (‖actualIncrement sharp m n‖*(1/|z.im|)*
          ‖(GaussAdjointHistory.iterate p g : H)‖) := by
  filter_upwards [source_power_return sharp m n p g] with F hF
  intro z hz
  rw [hF z hz,smul_smul,norm_smul,norm_mul,norm_pow,norm_inv]
  have hr : ‖finiteResolvent F z (GaussAdjointHistory.iterate p g : H)‖ ≤
      (1/|z.im|)*‖(GaussAdjointHistory.iterate p g : H)‖ :=
    ((finiteResolvent F z).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (finite_resolvent_norm F z hz) (norm_nonneg _))
  have ha := (escape_norm_le F
    (actualIncrement sharp m n
      (finiteResolvent F z (GaussAdjointHistory.iterate p g : H)))).trans
    ((actualIncrement sharp m n).le_opNorm
      (finiteResolvent F z (GaussAdjointHistory.iterate p g : H)))
  have hh := ha.trans (mul_le_mul_of_nonneg_left hr (norm_nonneg _))
  calc
    _ ≤ (‖z‖⁻¹*(‖z‖⁻¹)^p) *
        (‖actualIncrement sharp m n‖*((1/|z.im|)*
          ‖(GaussAdjointHistory.iterate p g : H)‖)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by rw [pow_succ]; ring

def vertical (negative : Bool) (l μ : ℝ) : ℂ :=
  (if negative then -(l : ℂ) else (l : ℂ)) + (μ : ℂ)*Complex.I

private theorem vertical_im (negative : Bool) (l μ : ℝ) :
    (vertical negative l μ).im = μ := by
  cases negative <;> simp [vertical]

private theorem frequency_le_norm (negative : Bool) (l μ : ℝ) (hl : 0 ≤ l) :
    l ≤ ‖vertical negative l μ‖ := by
  have h := Complex.abs_re_le_norm (vertical negative l μ)
  cases negative <;> simpa [vertical,abs_of_nonneg hl] using h

def escapeResponse (F : Index) (sharp : Bool) (m n : ℕ)
    (g : diagonal.domain) (z : ℂ) : H :=
  z⁻¹ • escapeProjection F
    (actualIncrement sharp m n (finiteResolvent F z (g : H)))

theorem source_frequency_bound (sharp : Bool) (m n p : ℕ) (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ (negative : Bool) (l μ : ℝ),
      0 < l → 0 < μ →
      ‖escapeResponse F sharp m n g (vertical negative l μ)‖ ≤
        l⁻¹^(p+1) *
          (‖actualIncrement sharp m n‖/μ*‖(GaussAdjointHistory.iterate p g : H)‖) := by
  filter_upwards [source_escape_spectral_bound sharp m n p g] with F hF
  intro negative l μ hl hμ
  have hz : (vertical negative l μ).im ≠ 0 := by rw [vertical_im]; exact hμ.ne'
  have h := hF (vertical negative l μ) hz
  have he : ‖vertical negative l μ‖⁻¹ ≤ l⁻¹ :=
    inv_anti₀ hl (frequency_le_norm negative l μ hl.le)
  have hp := pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) he (p+1)
  simp only [vertical_im,abs_of_pos hμ] at h
  have hc : ‖actualIncrement sharp m n‖*(1/μ)*
      ‖(GaussAdjointHistory.iterate p g : H)‖ =
      ‖actualIncrement sharp m n‖/μ*‖(GaussAdjointHistory.iterate p g : H)‖ := by ring
  rw [hc] at h
  exact h.trans (mul_le_mul_of_nonneg_right hp (by positivity))

open MeasureTheory Set

private theorem inverse_power_integral (p : ℕ) (Λ : ℝ) (hΛ : 0 < Λ) (C : ℝ) :
    (∫ l : ℝ in Ioi Λ, C^2 * l ^ (-((2*p+2 : ℕ) : ℝ))) =
      C^2 / (((2*p+1 : ℕ) : ℝ)*Λ^(2*p+1)) := by
  have he : -((2*p+2 : ℕ) : ℝ) < -1 := by
    have hp : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
    push_cast
    linarith
  rw [integral_const_mul,integral_Ioi_rpow_of_lt he hΛ]
  have hp : -((2*p+2 : ℕ) : ℝ)+1 = -((2*p+1 : ℕ) : ℝ) := by push_cast; ring
  rw [hp,Real.rpow_neg hΛ.le,Real.rpow_natCast]
  field_simp

private theorem half_tail_integral (f : ℝ → H) (p : ℕ) (Λ C : ℝ)
    (hΛ : 0 < Λ)
    (bound : ∀ l, Λ < l → ‖f l‖ ≤ l⁻¹^(p+1)*C) :
    (∫⁻ l in Ioi Λ, ENNReal.ofReal (‖f l‖^2)) ≤
      ENNReal.ofReal (C^2 / (((2*p+1 : ℕ) : ℝ)*Λ^(2*p+1))) := by
  have he : -((2*p+2 : ℕ) : ℝ) < -1 := by
    have hp : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
    push_cast
    linarith
  have hi := (integrableOn_Ioi_rpow_of_lt he hΛ).const_mul (C^2)
  have hn : 0 ≤ᵐ[volume.restrict (Ioi Λ)]
      (fun l : ℝ => C^2 * l ^ (-((2*p+2 : ℕ) : ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
    exact mul_nonneg (sq_nonneg C) (Real.rpow_nonneg (hΛ.trans hl).le _)
  rw [←inverse_power_integral p Λ hΛ C,
    ofReal_integral_eq_lintegral_ofReal hi hn]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
  apply ENNReal.ofReal_le_ofReal
  have hb := pow_le_pow_left₀ (norm_nonneg (f l)) (bound l hl) 2
  rw [Real.rpow_neg (hΛ.trans hl).le,Real.rpow_natCast]
  calc
    _ ≤ (l⁻¹^(p+1)*C)^2 := hb
    _ = C^2*(l^(2*p+2))⁻¹ := by
      rw [mul_pow,←pow_mul,←inv_pow]
      rw [show (p+1)*2=2*p+2 by omega,mul_comm]

/-- Each finite F is integrated first; one cofinal set covers both frequency tails. -/
theorem source_escape_high_frequency (sharp : Bool) (m n p : ℕ) (g : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ (negative : Bool) (Λ μ : ℝ),
      0 < Λ → 0 < μ →
      (∫⁻ l in Ioi Λ, ENNReal.ofReal
        (‖escapeResponse F sharp m n g (vertical negative l μ)‖^2)) ≤
      ENNReal.ofReal
        ((‖actualIncrement sharp m n‖/μ*‖(GaussAdjointHistory.iterate p g : H)‖)^2 /
          (((2*p+1 : ℕ) : ℝ)*Λ^(2*p+1))) := by
  filter_upwards [source_frequency_bound sharp m n p g] with F hF
  intro negative Λ μ hΛ hμ
  exact half_tail_integral _ p Λ _ hΛ
    (fun l hl => hF negative l μ (hΛ.trans hl) hμ)

#print axioms source_power_return
#print axioms source_escape_spectral_bound
#print axioms source_escape_high_frequency
end LowEnergy.SourceEscapeSeedTail
