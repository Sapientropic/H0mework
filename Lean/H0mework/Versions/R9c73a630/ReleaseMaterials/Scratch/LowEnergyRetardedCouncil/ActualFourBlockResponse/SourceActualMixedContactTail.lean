import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedContactReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ActualMixedContactReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourceScalarVirialBulk SourceScalarGaugeScale SourceClockPhiSecondBulk
open SourceResolventBandLimit FullYSourceResolventGraphSplice ActualMixedCovarianceTail ActualMixedWindowGram
open SourceScalarAffineCutoffTail ActualAffineCutoffCausalTail SourceNativeCutoffContact
open ActualVectorJointCost SourceRelativePowerTail MeasureTheory Filter
open Lean Meta Elab Term
open scoped InnerProductSpace ENNReal

elab "paid_mixed_tail%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedCovarianceTail 0) "LowEnergy") "ActualMixedCovarianceTail"
  let name:=Name.str ns field.getId.toString
  unless (←getEnv).contains name do throwError "Missing actual mixed covariance payer"
  mkConstWithFreshMVarLevels name

private theorem causal_nonreal(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(w:ℝ) :
    (causalFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa [causalFrequency,line_im] using hμ.ne'

def contactRead(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest) : ℝ :=
  (sourcePair (coreWindow m ell F z hz f) (affineCutoff m ell (resolventCore F z hz h))).re

private theorem cross_price(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest) :
    |contactRead m ell F z hz f h| ≤ ‖window m ell F z f‖^2+
      ‖embed (affineCutoff m ell (resolventCore F z hz h))‖^2 := by
  have he:embed (coreWindow m ell F z hz f)=window m ell F z f :=
    (paid_mixed_core% window_core) m ell F z hz f
  have hp:= (Complex.abs_re_le_norm (sourcePair (coreWindow m ell F z hz f)
    (affineCutoff m ell (resolventCore F z hz h)))).trans
    (norm_inner_le_norm (embed (coreWindow m ell F z hz f))
      (embed (affineCutoff m ell (resolventCore F z hz h))))
  rw [he] at hp
  change |contactRead m ell F z hz f h| ≤ _ at hp
  nlinarith only [hp,sq_nonneg (‖window m ell F z f‖-‖embed (affineCutoff m ell (resolventCore F z hz h))‖),
    sq_nonneg ‖window m ell F z f‖,sq_nonneg ‖embed (affineCutoff m ell (resolventCore F z hz h))‖]

/-- Both input jets are fixed original source vectors; θ and the full affine contact
pay the complete cross pairing on one source-filter event and both causal lines. -/
theorem actual_contact_pair_causal_tail(μ:ℝ)(hμ:0 < μ)(f h:QuantumTest) :
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        (∫⁻w:ℝ,ENNReal.ofReal |contactRead m ell F (causalFrequency advanced μ w)
          (causal_nonreal advanced μ hμ w) f h|) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N₀,h₀⟩:=actual_bounded_theta_causal_tail μ hμ (1:H →L[ℂ] H) (embed f) (ε/2) (by positivity)
  obtain ⟨N₁,h₁⟩:=actual_affine_core_causal_tail μ hμ (coreEquiv h) (ε/2) (by positivity)
  refine ⟨max N₀ N₁,fun m hm ell hml=>?_⟩
  filter_upwards [h₀ m ((le_max_left _ _).trans hm) ell hml,
    h₁ m ((le_max_right _ _).trans hm) ell hml] with F hF₀ hF₁
  intro advanced
  have hp:=lintegral_mono (μ:=volume) (fun w:ℝ=>ENNReal.ofReal_le_ofReal
    (cross_price m ell F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) f h))
  have hm₀:Measurable (fun w:ℝ=>ENNReal.ofReal (‖window m ell F (causalFrequency advanced μ w) f‖^2)) :=
    ENNReal.measurable_ofReal.comp
      ((((relativeTail m ell).continuous.comp
        (((paid_mixed_tail% frequency_continuous) advanced μ hμ F).clm_apply continuous_const)).norm.pow 2).measurable)
  simp_rw [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)] at hp
  rw [lintegral_add_left hm₀] at hp
  have ha:=hF₀ advanced
  have hb:=hF₁ advanced
  change (∫⁻w:ℝ,ENNReal.ofReal (‖embed (affineCutoff m ell
    (resolventCore F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) h))‖^2)) ≤ _ at hb
  have ha':(∫⁻w:ℝ,ENNReal.ofReal (‖window m ell F (causalFrequency advanced μ w) f‖^2)) ≤ ENNReal.ofReal (ε/2) := by
    simpa only [window,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,ContinuousLinearMap.comp_apply,one_apply_eq_self] using ha
  apply hp.trans ((add_le_add ha' hb).trans_eq ?_)
  rw [←ENNReal.ofReal_add (by positivity : 0 ≤ ε/2) (by positivity : 0 ≤ ε/2)]
  congr 1
  ring

/-- The whole cutoff-shape part of the mixed return is one fixed-source affine cross
with g+Gauge g. The moving Gauge R g contribution has cancelled in the real pairing. -/
theorem actual_window_shape_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest) :
    (sourcePair (coreWindow m ell F z hz g) (secondJet (coreWindow m ell F z hz) g)).re-
      (sourcePair (coreWindow m ell F z hz g)
        (thetaAction m ell (secondJet (resolventCore F z hz) g))).re=
      contactRead m ell F z hz g (g+Gauge g) := by
  rw [actual_window_mixed_return]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,Module.End.mul_apply,sourcePair,
    map_add,map_sub,inner_add_right,inner_sub_right,Complex.add_re,Complex.sub_re,contactRead]
  have h:=actual_moving_contact_return m ell F z hz g
  simp only [sourcePair] at h
  rw [h]
  ring

/-- The actual mixed-return shape error has an absolute all-frequency common tail. -/
theorem actual_window_shape_causal_tail(μ:ℝ)(hμ:0 < μ)(g:QuantumTest) :
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        (∫⁻w:ℝ,ENNReal.ofReal |(sourcePair
          (coreWindow m ell F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g)
          (secondJet (coreWindow m ell F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w)) g)).re-
          (sourcePair (coreWindow m ell F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g)
            (thetaAction m ell (secondJet (resolventCore F (causalFrequency advanced μ w)
              (causal_nonreal advanced μ hμ w)) g))).re|) ≤ ENNReal.ofReal ε := by
  simpa only [actual_window_shape_return] using actual_contact_pair_causal_tail μ hμ g (g+Gauge g)

end LowEnergy.ActualMixedContactReturn
