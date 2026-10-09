import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiSecondPressure
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualVectorJointTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ActualMixedCovarianceTail
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPositiveBulkWard SourceClockPhiSecondPressure SourceRelativePowerTail
open SourceResolventBandLimit ActualVectorJointCost FullYSourceResolventGraphSplice
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

def relativeGenerator : End := Phi-Gauge

def window (m ell : ℕ) (F : Index) (z : ℂ) : QuantumTest →ₗ[ℂ] H :=
  ((relativeTail m ell).comp (finiteResolvent F z)).toLinearMap.comp embed

/-- The original mixed polarized source variation acts on the same θR covariance. -/
def mixedCovariance (m ell : ℕ) (F : Index) (z : ℂ) (g : QuantumTest) : ℝ :=
  (secondPair (fun A B => inner ℂ (window m ell F z (A g))
    (window m ell F z (B g))) 1 1).re

private theorem polarized_source (W : QuantumTest →ₗ[ℂ] H) (g : QuantumTest) :
    (secondPair (fun A B => inner ℂ (W (A g)) (W (B g))) 1 1).re=
      -2*((inner ℂ (W (relativeGenerator g)) (W g)).re+
        (inner ℂ (W (relativeGenerator (Gauge g))) (W g)).re+
        (inner ℂ (W (Gauge g)) (W (relativeGenerator g))).re) := by
  simp only [secondPair,pairDelta,LinearMap.sub_apply,LinearMap.coe_mk,AddHom.coe_mk,
    Pi.sub_apply,Module.End.mul_apply,Module.End.one_apply,relativeGenerator,map_sub,
    inner_sub_left,inner_sub_right,Complex.sub_re,Complex.neg_re]
  have swap (u v:H) : (inner ℂ u v).re=(inner ℂ v u).re := by
    simpa only [Complex.star_def,Complex.conj_re] using
      congrArg Complex.re (inner_conj_symm (𝕜:=ℂ) v u)
  simp only [swap (W g) (W (Phi g)),
    swap (W g) (W (Gauge g)),
    swap (W g) (W (Phi (Gauge g))),
    swap (W g) (W (Gauge (Gauge g))),
    swap (W (Phi g)) (W (Gauge g))]
  ring

/-- All six ordered mixed legs reduce to four fixed source jets before estimating. -/
theorem actual_mixed_covariance_source (m ell : ℕ) (F : Index) (z : ℂ) (g : QuantumTest) :
    mixedCovariance m ell F z g=
      -2*((inner ℂ (window m ell F z (relativeGenerator g)) (window m ell F z g)).re+
        (inner ℂ (window m ell F z (relativeGenerator (Gauge g))) (window m ell F z g)).re+
        (inner ℂ (window m ell F z (Gauge g)) (window m ell F z (relativeGenerator g))).re) :=
  polarized_source _ _

private theorem real_pair_price (u v : H) :
    2*|(inner ℂ u v).re| ≤ ‖u‖^2+‖v‖^2 := by
  have h: |(inner ℂ u v).re| ≤ ‖u‖*‖v‖ :=
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  nlinarith only [h,sq_nonneg (‖u‖-‖v‖)]

/-- This is a whole covariance bound, not separate positivity of either ordered cross leg. -/
theorem actual_mixed_covariance_price (m ell : ℕ) (F : Index) (z : ℂ) (g : QuantumTest) :
    |mixedCovariance m ell F z g| ≤
      2*(‖window m ell F z g‖^2+‖window m ell F z (relativeGenerator g)‖^2+
        ‖window m ell F z (relativeGenerator (Gauge g))‖^2+‖window m ell F z (Gauge g)‖^2) := by
  rw [actual_mixed_covariance_source,abs_mul]
  norm_num only [abs_neg,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have h1:=real_pair_price (window m ell F z (relativeGenerator g)) (window m ell F z g)
  have h2:=real_pair_price (window m ell F z (relativeGenerator (Gauge g))) (window m ell F z g)
  have h3:=real_pair_price (window m ell F z (Gauge g)) (window m ell F z (relativeGenerator g))
  have ht:=abs_add_le ((inner ℂ (window m ell F z (relativeGenerator g)) (window m ell F z g)).re+
    (inner ℂ (window m ell F z (relativeGenerator (Gauge g))) (window m ell F z g)).re)
    (inner ℂ (window m ell F z (Gauge g)) (window m ell F z (relativeGenerator g))).re
  have hu:=abs_add_le (inner ℂ (window m ell F z (relativeGenerator g)) (window m ell F z g)).re
    (inner ℂ (window m ell F z (relativeGenerator (Gauge g))) (window m ell F z g)).re
  nlinarith only [h1,h2,h3,ht,hu,sq_nonneg ‖window m ell F z (relativeGenerator (Gauge g))‖,
    sq_nonneg ‖window m ell F z (Gauge g)‖]

private theorem frequency_continuous (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (F : Index) :
    Continuous (fun w : ℝ => finiteResolvent F (causalFrequency advanced μ w)) := by
  have he (w : ℝ) : causalFrequency advanced μ w=
      SourceLocalizedInverseFormPayment.actualFrequency advanced μ w := by
    cases advanced
    · rfl
    · apply Complex.ext <;> simp [causalFrequency,SourceLocalizedInverseFormPayment.actualFrequency,
        SourceResolventBandLimit.line]
  simp_rw [he]
  exact (paid_clock_tail% frequency_continuous) advanced μ hμ F

private theorem four_integral (f₀ f₁ f₂ f₃ : ℝ → ℝ)
    (h₀ : ∀ w,0 ≤ f₀ w) (h₁ : ∀ w,0 ≤ f₁ w) (h₂ : ∀ w,0 ≤ f₂ w) (_h₃ : ∀ w,0 ≤ f₃ w)
    (_m₀ : Measurable f₀) (m₁ : Measurable f₁) (m₂ : Measurable f₂) (m₃ : Measurable f₃) :
    (∫⁻w,ENNReal.ofReal (2*(f₀ w+f₁ w+f₂ w+f₃ w)))=
      ENNReal.ofReal 2*((∫⁻w,ENNReal.ofReal (f₀ w))+(∫⁻w,ENNReal.ofReal (f₁ w))+
        (∫⁻w,ENNReal.ofReal (f₂ w))+(∫⁻w,ENNReal.ofReal (f₃ w))) := by
  simp_rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
    ENNReal.ofReal_add (add_nonneg (add_nonneg (h₀ _) (h₁ _)) (h₂ _)) (_h₃ _),
    ENNReal.ofReal_add (add_nonneg (h₀ _) (h₁ _)) (h₂ _),ENNReal.ofReal_add (h₀ _) (h₁ _)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_add_right _ (show Measurable (fun w : ℝ => ENNReal.ofReal (f₃ w)) from ENNReal.measurable_ofReal.comp m₃),
    lintegral_add_right _ (show Measurable (fun w : ℝ => ENNReal.ofReal (f₂ w)) from ENNReal.measurable_ofReal.comp m₂),
    lintegral_add_right _ (show Measurable (fun w : ℝ => ENNReal.ofReal (f₁ w)) from ENNReal.measurable_ofReal.comp m₁)]

/-- All frequency, both causal signs, and the four genuine fixed source jets use one
cutoff and the original source filter. The whole mixed covariance absolute tail is paid. -/
theorem actual_mixed_covariance_causal_tail (μ : ℝ) (hμ : 0 < μ) (g : QuantumTest) :
    ∀ε : ℝ,0 < ε → ∃N : ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀advanced : Bool,
        (∫⁻w : ℝ,ENNReal.ofReal |mixedCovariance m ell F (causalFrequency advanced μ w) g|) ≤
          ENNReal.ofReal ε := by
  intro ε hε
  let δ:=ε/8
  have hd : 0 < δ := by dsimp [δ];positivity
  obtain ⟨N₀,h₀⟩:=actual_bounded_theta_causal_tail μ hμ (1:H →L[ℂ] H) (embed g) δ hd
  obtain ⟨N₁,h₁⟩:=actual_bounded_theta_causal_tail μ hμ (1:H →L[ℂ] H) (embed (relativeGenerator g)) δ hd
  obtain ⟨N₂,h₂⟩:=actual_bounded_theta_causal_tail μ hμ (1:H →L[ℂ] H) (embed (relativeGenerator (Gauge g))) δ hd
  obtain ⟨N₃,h₃⟩:=actual_bounded_theta_causal_tail μ hμ (1:H →L[ℂ] H) (embed (Gauge g)) δ hd
  refine ⟨max (max N₀ N₁) (max N₂ N₃),fun m hm ell hml => ?_⟩
  filter_upwards [h₀ m (by omega) ell hml,h₁ m (by omega) ell hml,
    h₂ m (by omega) ell hml,h₃ m (by omega) ell hml] with F hF₀ hF₁ hF₂ hF₃
  intro advanced
  have hc (f : QuantumTest) : Measurable (fun w : ℝ => ‖window m ell F (causalFrequency advanced μ w) f‖^2) := by
    exact (((relativeTail m ell).continuous.comp
      ((frequency_continuous advanced μ hμ F).clm_apply continuous_const)).norm.pow 2).measurable
  have hb := lintegral_mono (μ:=volume) (fun w : ℝ => ENNReal.ofReal_le_ofReal
    (actual_mixed_covariance_price m ell F (causalFrequency advanced μ w) g))
  rw [four_integral _ _ _ _ (fun _=>sq_nonneg _) (fun _=>sq_nonneg _)
    (fun _=>sq_nonneg _) (fun _=>sq_nonneg _) (hc _) (hc _) (hc _) (hc _)] at hb
  have he (f:QuantumTest)(w:ℝ) : window m ell F (causalFrequency advanced μ w) f=
    relativeTail m ell (finiteResolvent F (causalFrequency advanced μ w) (embed f)) := rfl
  simp only [he] at hb
  have hs₀:=hF₀ advanced
  have hs₁:=hF₁ advanced
  have hs₂:=hF₂ advanced
  have hs₃:=hF₃ advanced
  simp only [one_apply_eq_self] at hs₀ hs₁ hs₂ hs₃
  apply hb.trans
  calc
    _ ≤ ENNReal.ofReal 2*(ENNReal.ofReal δ+ENNReal.ofReal δ+ENNReal.ofReal δ+ENNReal.ofReal δ) := by
      gcongr
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_add hd.le hd.le,←ENNReal.ofReal_add (by positivity : 0 ≤ δ+δ) hd.le,
        ←ENNReal.ofReal_add (by positivity : 0 ≤ δ+δ+δ) hd.le,←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      dsimp [δ]
      ring

end LowEnergy.ActualMixedCovarianceTail
