import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedContactTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ActualMixedWardTail
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourceScalarVirialBulk SourceScalarGaugeScale SourceClockPhiSecondBulk GaussCoframeForm
open SourceResolventBandLimit FullYSourceResolventGraphSplice ActualMixedCovarianceTail ActualMixedWindowGram
open SourceScalarAffineCutoffTail ActualAffineCutoffCausalTail SourceNativeCutoffContact ActualMixedContactReturn
open ActualVectorJointCost SourceRelativePowerTail MeasureTheory Filter
open Lean Meta Elab Term
open scoped InnerProductSpace ENNReal
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

elab "paid_mixed_contact%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedContactReturn 0) "LowEnergy") "ActualMixedContactReturn"
  let name:=Name.str ns field.getId.toString
  unless (←getEnv).contains name do throwError "Missing actual mixed contact proof"
  mkConstWithFreshMVarLevels name

private theorem gauge_mul (A B:End) : deltaGauge (A*B)=deltaGauge A*B+A*deltaGauge B := by
  simp only [deltaGauge,LinearMap.coe_mk,AddHom.coe_mk]
  noncomm_ring
private theorem phi_mul (A B:End) : deltaPhi (A*B)=deltaPhi A*B+A*deltaPhi B := by
  simp only [deltaPhi,LinearMap.coe_mk,AddHom.coe_mk]
  noncomm_ring

private theorem window_gauge (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0) :
    deltaGauge (coreWindow m ell F z hz)=thetaAction m ell*deltaGauge (resolventCore F z hz) := by
  rw [coreWindow,gauge_mul,actual_gauge_cutoff_zero,zero_mul,zero_add]
private theorem window_phi (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0) :
    deltaPhi (coreWindow m ell F z hz)=affineCutoff m ell*resolventCore F z hz+
      thetaAction m ell*deltaPhi (resolventCore F z hz) := phi_mul _ _
private theorem window_difference (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0) :
    deltaPhi (coreWindow m ell F z hz)-deltaGauge (coreWindow m ell F z hz)=
      affineCutoff m ell*resolventCore F z hz+
      thetaAction m ell*(deltaPhi (resolventCore F z hz)-deltaGauge (resolventCore F z hz)) := by
  simp only [window_phi,window_gauge,mul_sub]
  abel

private theorem contact_transpose (m ell:ℕ)(q p:QuantumTest) :
    sourcePair (affineCutoff m ell q) (thetaAction m ell p)=
      sourcePair (thetaAction m ell q) (affineCutoff m ell p) := by
  have hc:thetaAction m ell (affineCutoff m ell p)=affineCutoff m ell (thetaAction m ell p) :=
    LinearMap.congr_fun ((paid_mixed_contact% actual_theta_affine_commute) m ell).eq p
  rw [←(paid_mixed_contact% affine_pair) m ell,←hc,(paid_mixed_contact% theta_pair) m ell]

private theorem norm_difference (a u v:H) :
    ‖a+u‖^2-‖a+v‖^2=‖u‖^2-‖v‖^2+2*(inner ℂ a (u-v)).re := by
  have h1:=norm_add_sq (𝕜:=ℂ) a u
  have h2:=norm_add_sq (𝕜:=ℂ) a v
  change ‖a+u‖^2=‖a‖^2+2*(inner ℂ a u).re+‖u‖^2 at h1
  change ‖a+v‖^2=‖a‖^2+2*(inner ℂ a v).re+‖v‖^2 at h2
  rw [inner_sub_right,Complex.sub_re]
  linarith only [h1,h2]

/-- The complete mixed Ward current keeps all moving resolvent derivatives together. -/
def wardCurrent (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest) : ℝ :=
  let R:=resolventCore F z hz
  ‖embed (thetaAction m ell (deltaGauge R g))‖^2+
    ‖embed (thetaAction m ell ((deltaPhi R-deltaGauge R) g))‖^2-
    ‖embed (thetaAction m ell (deltaPhi R g))‖^2+
    2*(sourcePair (coreWindow m ell F z hz g) (thetaAction m ell (secondJet R g))).re

/-- The whole moving Ward current is exactly the already generated covariance
boundary minus one fixed-source affine cross, with all source coefficients retained. -/
theorem actual_ward_source_return (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest) :
    wardCurrent m ell F z hz g=mixedCovariance m ell F z g-
      contactRead m ell F z hz g ((2:ℂ) • g+(4:ℂ) • Gauge g) := by
  have hW:=actual_window_gram m ell F z hz g
  dsimp only at hW
  rw [window_difference,window_gauge,window_phi,actual_core_covariance_source] at hW
  simp only [LinearMap.add_apply,Module.End.mul_apply,map_add] at hW
  have hn:=norm_difference
    (embed (affineCutoff m ell (resolventCore F z hz g)))
    (embed (thetaAction m ell (deltaPhi (resolventCore F z hz) g)))
    (embed (thetaAction m ell ((deltaPhi (resolventCore F z hz)-deltaGauge (resolventCore F z hz)) g)))
  have he:embed (thetaAction m ell (deltaPhi (resolventCore F z hz) g))-
    embed (thetaAction m ell ((deltaPhi (resolventCore F z hz)-deltaGauge (resolventCore F z hz)) g))=
    embed (thetaAction m ell (deltaGauge (resolventCore F z hz) g)) := by
    simp only [LinearMap.sub_apply,map_sub]
    abel
  rw [he] at hn
  have hc:=congrArg Complex.re (contact_transpose m ell (resolventCore F z hz g)
    (deltaGauge (resolventCore F z hz) g))
  have hm:=actual_moving_contact_return m ell F z hz g
  change (sourcePair (coreWindow m ell F z hz g)
    (affineCutoff m ell (deltaGauge (resolventCore F z hz) g))).re=
      -contactRead m ell F z hz g (Gauge g) at hm
  have hs:=actual_window_shape_return m ell F z hz g
  have hadd:contactRead m ell F z hz g (g+Gauge g)=
    contactRead m ell F z hz g g+contactRead m ell F z hz g (Gauge g) := by
    simp only [contactRead,map_add,sourcePair,inner_add_right,Complex.add_re]
  have hscale:contactRead m ell F z hz g ((2:ℂ) • g+(4:ℂ) • Gauge g)=
    2*contactRead m ell F z hz g g+4*contactRead m ell F z hz g (Gauge g) := by
    simp only [contactRead,map_add,map_smul,sourcePair,inner_add_right,inner_smul_right,
      Complex.add_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
  rw [hadd] at hs
  rw [hscale]
  unfold wardCurrent
  change (sourcePair (affineCutoff m ell (resolventCore F z hz g))
    (thetaAction m ell (deltaGauge (resolventCore F z hz) g))).re=
      (sourcePair (coreWindow m ell F z hz g)
        (affineCutoff m ell (deltaGauge (resolventCore F z hz) g))).re at hc
  change _= _ at hn
  simp only [sourcePair] at hc hm hs hW ⊢
  linarith only [hW,hn,hc,hm,hs]

private theorem covariance_continuous (advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)(g:QuantumTest) :
    Continuous (fun w:ℝ=>mixedCovariance m ell F (causalFrequency advanced μ w) g) := by
  have hc (f:QuantumTest):Continuous (fun w:ℝ=>window m ell F (causalFrequency advanced μ w) f) :=
    (relativeTail m ell).continuous.comp
      (((paid_mixed_tail% frequency_continuous) advanced μ hμ F).clm_apply continuous_const)
  have hp (f k:QuantumTest):Continuous (fun w:ℝ=>
      (inner ℂ (window m ell F (causalFrequency advanced μ w) f)
        (window m ell F (causalFrequency advanced μ w) k)).re) :=
    Complex.continuous_re.comp ((hc f).inner (𝕜:=ℂ) (hc k))
  have h:=(((hp (relativeGenerator g) g).add
    (hp (relativeGenerator (Gauge g)) g)).add
    (hp (Gauge g) (relativeGenerator g))).const_mul (-2)
  convert h using 1
  funext w
  exact actual_mixed_covariance_source m ell F (causalFrequency advanced μ w) g

private theorem causal_nonreal (advanced:Bool)(μ:ℝ)(hμ:0 < μ)(w:ℝ) :
    (causalFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa [causalFrequency,line_im] using hμ.ne'

/-- The original mixed Ward combination has a whole absolute frequency tail: all
moving terms remain coherent, and only actual fixed-source prices are consumed. -/
theorem actual_ward_causal_tail (μ:ℝ)(hμ:0 < μ)(g:QuantumTest) :
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        (∫⁻w:ℝ,ENNReal.ofReal |wardCurrent m ell F (causalFrequency advanced μ w)
          (causal_nonreal advanced μ hμ w) g|) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N₀,h₀⟩:=actual_mixed_covariance_causal_tail μ hμ g (ε/2) (by positivity)
  obtain ⟨N₁,h₁⟩:=actual_contact_pair_causal_tail μ hμ g ((2:ℂ) • g+(4:ℂ) • Gauge g) (ε/2) (by positivity)
  refine ⟨max N₀ N₁,fun m hm ell hml=>?_⟩
  filter_upwards [h₀ m ((le_max_left _ _).trans hm) ell hml,
    h₁ m ((le_max_right _ _).trans hm) ell hml] with F hF₀ hF₁
  intro advanced
  have hp:=lintegral_mono (μ:=volume) (fun w:ℝ=>ENNReal.ofReal_le_ofReal
    (show |wardCurrent m ell F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g| ≤
      |mixedCovariance m ell F (causalFrequency advanced μ w) g|+
      |contactRead m ell F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g
        ((2:ℂ) • g+(4:ℂ) • Gauge g)| from by
          rw [actual_ward_source_return]
          simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (mixedCovariance m ell F (causalFrequency advanced μ w) g)
            (-contactRead m ell F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g
              ((2:ℂ) • g+(4:ℂ) • Gauge g))))
  simp_rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)] at hp
  have hmeas:Measurable (fun w:ℝ=>ENNReal.ofReal |mixedCovariance m ell F (causalFrequency advanced μ w) g|) :=
    ENNReal.measurable_ofReal.comp (covariance_continuous advanced μ hμ m ell F g).abs.measurable
  rw [lintegral_add_left hmeas] at hp
  apply hp.trans ((add_le_add (hF₀ advanced) (hF₁ advanced)).trans_eq ?_)
  rw [←ENNReal.ofReal_add (by positivity : 0 ≤ ε/2) (by positivity : 0 ≤ ε/2)]
  congr 1
  ring

end LowEnergy.ActualMixedWardTail
