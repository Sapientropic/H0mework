import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedWardMomentTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ActualMixedCovariancePairTail
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard SourceScalarVirialBulk
open SourceScalarGaugeScale SourceClockPhiSecondBulk SourceClockPhiSecondPressure SourceResolventBandLimit
open FullYSourceResolventGraphSplice ActualMixedCovarianceTail ActualMixedWindowGram
open ActualVectorJointCost MeasureTheory Filter Lean Meta Elab Term
open scoped InnerProductSpace ENNReal

elab "paid_covariance_window%" field:ident : term => do
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedWardMomentTail 0)
    "LowEnergy") "ActualMixedWardMomentTail"
  let name := Name.str ns field.getId.eraseMacroScopes.toString
  unless (←getEnv).contains name do throwError "Missing paid actual complex window tail"
  mkConstWithFreshMVarLevels name

private theorem six_pair_source (W : QuantumTest →ₗ[ℂ] H) (f h : QuantumTest) :
    secondPair (fun A B => inner ℂ (W (A f)) (W (B h))) 1 1=
      -inner ℂ (W (relativeGenerator f)) (W h)-inner ℂ (W f) (W (relativeGenerator h))-
      inner ℂ (W (relativeGenerator (Gauge f))) (W h)-
      inner ℂ (W (relativeGenerator f)) (W (Gauge h))-
      inner ℂ (W (Gauge f)) (W (relativeGenerator h))-
      inner ℂ (W f) (W (relativeGenerator (Gauge h))) := by
  simp only [secondPair,pairDelta,LinearMap.sub_apply,LinearMap.coe_mk,AddHom.coe_mk,
    Pi.sub_apply,Module.End.mul_apply,Module.End.one_apply,relativeGenerator,map_sub,
    inner_sub_left,inner_sub_right]
  ring

/-- Six actual fixed-input pairs, including both ordered mixed jets, precede all moving parameters. -/
theorem actual_covariance_six_pair_source (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (f h : QuantumTest) :
    sourcePair f (secondJet (coreCovariance m ell F z hz) h)=
      -inner ℂ (window m ell F z (relativeGenerator f)) (window m ell F z h)-
      inner ℂ (window m ell F z f) (window m ell F z (relativeGenerator h))-
      inner ℂ (window m ell F z (relativeGenerator (Gauge f))) (window m ell F z h)-
      inner ℂ (window m ell F z (relativeGenerator f)) (window m ell F z (Gauge h))-
      inner ℂ (window m ell F z (Gauge f)) (window m ell F z (relativeGenerator h))-
      inner ℂ (window m ell F z f) (window m ell F z (relativeGenerator (Gauge h))) := by
  have hs := congrArg (fun P : PairMatrix => P 1 1)
    ((paid_second_pressure% second_pair_source) f h (coreCovariance m ell F z hz))
  change sourcePair f (secondJet (coreCovariance m ell F z hz) h)=
    secondPair (fun A B => sourcePair (A f) (coreCovariance m ell F z hz (B h))) 1 1 at hs
  simp_rw [actual_core_covariance_pair] at hs
  exact hs.trans (six_pair_source _ f h)

private theorem causal_nonreal (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
    (causalFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa [causalFrequency,line_im] using hμ.ne'

private theorem six_norm (a b c d e f : ℂ) :
    ‖-a-b-c-d-e-f‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖+‖e‖+‖f‖ := by
  have h₁ := norm_sub_le (-a) b
  have h₂ := norm_sub_le (-a-b) c
  have h₃ := norm_sub_le (-a-b-c) d
  have h₄ := norm_sub_le (-a-b-c-d) e
  have h₅ := norm_sub_le (-a-b-c-d-e) f
  rw [norm_neg] at h₁
  linarith

/-- The complex norm of the full returned covariance pair has one common N for both causes. -/
theorem actual_covariance_pair_causal_tail (μ : ℝ) (hμ : 0 < μ) (f h : QuantumTest) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ advanced : Bool,
        (∫⁻ w : ℝ,ENNReal.ofReal ‖sourcePair f
          (secondJet (coreCovariance m ell F (causalFrequency advanced μ w)
            (causal_nonreal advanced μ hμ w)) h)‖) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N₀,h₀⟩ := (paid_covariance_window% window_pair_tail) μ hμ (relativeGenerator f) h (ε/6) (by positivity)
  obtain ⟨N₁,h₁⟩ := (paid_covariance_window% window_pair_tail) μ hμ f (relativeGenerator h) (ε/6) (by positivity)
  obtain ⟨N₂,h₂⟩ := (paid_covariance_window% window_pair_tail) μ hμ (relativeGenerator (Gauge f)) h (ε/6) (by positivity)
  obtain ⟨N₃,h₃⟩ := (paid_covariance_window% window_pair_tail) μ hμ (relativeGenerator f) (Gauge h) (ε/6) (by positivity)
  obtain ⟨N₄,h₄⟩ := (paid_covariance_window% window_pair_tail) μ hμ (Gauge f) (relativeGenerator h) (ε/6) (by positivity)
  obtain ⟨N₅,h₅⟩ := (paid_covariance_window% window_pair_tail) μ hμ f (relativeGenerator (Gauge h)) (ε/6) (by positivity)
  refine ⟨max (max (max N₀ N₁) (max N₂ N₃)) (max N₄ N₅),fun m hm ell hell => ?_⟩
  filter_upwards [h₀ m (by omega) ell hell,h₁ m (by omega) ell hell,h₂ m (by omega) ell hell,
    h₃ m (by omega) ell hell,h₄ m (by omega) ell hell,h₅ m (by omega) ell hell]
    with F hF₀ hF₁ hF₂ hF₃ hF₄ hF₅
  intro advanced
  let p (a b : QuantumTest) (w : ℝ) := inner ℂ
    (window m ell F (causalFrequency advanced μ w) a) (window m ell F (causalFrequency advanced μ w) b)
  have hp (a b : QuantumTest) : Measurable (fun w : ℝ => ENNReal.ofReal ‖p a b w‖) :=
    ENNReal.measurable_ofReal.comp (((paid_covariance_window% window_continuous)
      advanced μ hμ m ell F a).inner (𝕜:=ℂ)
        ((paid_covariance_window% window_continuous) advanced μ hμ m ell F b)).norm.measurable
  have hi := lintegral_mono (μ:=volume) (fun w : ℝ => ENNReal.ofReal_le_ofReal
    (six_norm (p (relativeGenerator f) h w) (p f (relativeGenerator h) w)
      (p (relativeGenerator (Gauge f)) h w) (p (relativeGenerator f) (Gauge h) w)
      (p (Gauge f) (relativeGenerator h) w) (p f (relativeGenerator (Gauge h)) w)))
  simp_rw [actual_covariance_six_pair_source]
  apply le_trans hi
  simp_rw [ENNReal.ofReal_add
    (add_nonneg (add_nonneg (add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _),
    ENNReal.ofReal_add (add_nonneg (add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _),
    ENNReal.ofReal_add (add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _),
    ENNReal.ofReal_add (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _),
    ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  rw [lintegral_add_right _ (hp _ _),lintegral_add_right _ (hp _ _),lintegral_add_right _ (hp _ _),
    lintegral_add_right _ (hp _ _),lintegral_add_right _ (hp _ _)]
  have hh₀ := hF₀ advanced
  have hh₁ := hF₁ advanced
  have hh₂ := hF₂ advanced
  have hh₃ := hF₃ advanced
  have hh₄ := hF₄ advanced
  have hh₅ := hF₅ advanced
  change (∫⁻ w,ENNReal.ofReal ‖p (relativeGenerator f) h w‖) ≤ ENNReal.ofReal (ε/6) at hh₀
  change (∫⁻ w,ENNReal.ofReal ‖p f (relativeGenerator h) w‖) ≤ ENNReal.ofReal (ε/6) at hh₁
  change (∫⁻ w,ENNReal.ofReal ‖p (relativeGenerator (Gauge f)) h w‖) ≤ ENNReal.ofReal (ε/6) at hh₂
  change (∫⁻ w,ENNReal.ofReal ‖p (relativeGenerator f) (Gauge h) w‖) ≤ ENNReal.ofReal (ε/6) at hh₃
  change (∫⁻ w,ENNReal.ofReal ‖p (Gauge f) (relativeGenerator h) w‖) ≤ ENNReal.ofReal (ε/6) at hh₄
  change (∫⁻ w,ENNReal.ofReal ‖p f (relativeGenerator (Gauge h)) w‖) ≤ ENNReal.ofReal (ε/6) at hh₅
  calc
    _ ≤ ENNReal.ofReal (ε/6)+ENNReal.ofReal (ε/6)+ENNReal.ofReal (ε/6)+
        ENNReal.ofReal (ε/6)+ENNReal.ofReal (ε/6)+ENNReal.ofReal (ε/6) :=
      add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hh₀ hh₁) hh₂) hh₃) hh₄) hh₅
    _=ENNReal.ofReal ε := by
      have hδ : 0 ≤ ε/6 := by positivity
      rw [←ENNReal.ofReal_add hδ hδ,
        ←ENNReal.ofReal_add (by positivity) hδ,←ENNReal.ofReal_add (by positivity) hδ,
        ←ENNReal.ofReal_add (by positivity) hδ,←ENNReal.ofReal_add (by positivity) hδ]
      congr 1
      ring

end LowEnergy.ActualMixedCovariancePairTail
