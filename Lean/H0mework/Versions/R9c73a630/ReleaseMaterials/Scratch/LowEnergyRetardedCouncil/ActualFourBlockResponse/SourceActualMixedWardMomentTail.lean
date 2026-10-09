import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedWardPolarization
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedFrequencyJet
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedWardFrequencyReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ActualMixedWardMomentTail
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourceScalarVirialBulk SourceScalarGaugeScale SourceClockPhiSecondBulk
open SourceResolventBandLimit FullYSourceResolventGraphSplice ActualVectorJointCost SourceRelativePowerTail
open ActualMixedCovarianceTail ActualMixedWindowGram ActualMixedContactReturn ActualMixedWardPolarization
open SourceScalarAffineCutoffTail ActualAffineCutoffCausalTail
open SourceNativeCutoffContact MeasureTheory Filter
open ActualMixedWardTail ActualMixedWardFrequencyReturn
open SourceMixedNativeReturn (sourceRead source_read_resolvent)
open Lean Meta Elab Term
open scoped InnerProductSpace ENNReal Matrix
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] compressionCore resolventCore diagonalAction secondJet deltaPhi deltaGauge

private theorem compression_embed (F:Index)(f:QuantumTest):
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem fixed_compression (f:QuantumTest):
    ∀ᶠF in (sourceFilter:Filter Index),compressionCore F f=diagonalAction f := by
  filter_upwards [GaussGradedCompression.eventually_exact (coreEquiv f)] with F hF
  apply embed_injective
  rw [compression_embed]
  have he:(coreEquiv f:H)=embed f := rfl
  have hd:diagonal (coreEquiv f)=embed (diagonalAction f) := by
    change embed (diagonalAction (coreEquiv.symm (coreEquiv f)))=embed (diagonalAction f)
    rw [coreEquiv.symm_apply_apply]
  simpa only [he,hd] using hF

private theorem gauge_apply (A:End)(f:QuantumTest):
    deltaGauge A f=Gauge (A f)-A (Gauge f) := by
  rw [←SourceGaugeScaleTransport.generator_commutator]
  rfl

private theorem relative_apply (A:End)(f:QuantumTest):
    (deltaPhi A-deltaGauge A) f=relativeGenerator (A f)-A (relativeGenerator f) := by
  rw [←SourceScalarAffineScaleTransport.generator_commutator,←SourceGaugeScaleTransport.generator_commutator]
  simp only [LinearMap.sub_apply,Module.End.mul_apply,relativeGenerator,map_sub]
  abel

private theorem second_apply (A:End)(f:QuantumTest):
    secondJet A f=relativeGenerator (A f)-A (relativeGenerator f)-
      (Gauge (relativeGenerator (A f))-Gauge (A (relativeGenerator f))-
        relativeGenerator (A (Gauge f))+A (relativeGenerator (Gauge f))) := by
  unfold secondJet
  change ((deltaPhi A-deltaGauge A)-deltaGauge (deltaPhi A-deltaGauge A)) f=_
  change (deltaPhi A-deltaGauge A) f-deltaGauge (deltaPhi A-deltaGauge A) f=_
  rw [gauge_apply (deltaPhi A-deltaGauge A) f]
  simp only [relative_apply,map_sub]
  abel

private theorem fixed_source_jets (g:QuantumTest):
    ∀ᶠF in (sourceFilter:Filter Index),
      compressionCore F g=diagonalAction g ∧
      deltaGauge (compressionCore F) g=deltaGauge diagonalAction g ∧
      (deltaPhi (compressionCore F)-deltaGauge (compressionCore F)) g=
        (deltaPhi diagonalAction-deltaGauge diagonalAction) g ∧
      secondJet (compressionCore F) g=secondJet diagonalAction g := by
  filter_upwards [fixed_compression g,fixed_compression (Gauge g),
    fixed_compression (relativeGenerator g),fixed_compression (relativeGenerator (Gauge g))]
    with F hg hG hK hKG
  refine ⟨hg,?_,?_,?_⟩
  · simp only [gauge_apply,hg,hG]
  · simp only [relative_apply,hg,hK]
  · simp only [second_apply,hg,hK,hG,hKG]

private theorem causal_nonreal (advanced:Bool)(μ:ℝ)(hμ:0 < μ)(w:ℝ):
    (causalFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa [causalFrequency,line_im] using hμ.ne'

private theorem window_continuous (advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)(f:QuantumTest):
    Continuous (fun w:ℝ=>window m ell F (causalFrequency advanced μ w) f) :=
  (relativeTail m ell).continuous.comp
    (((paid_mixed_tail% frequency_continuous) advanced μ hμ F).clm_apply continuous_const)

private theorem window_energy_measurable (advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)(f:QuantumTest):
    Measurable (fun w:ℝ=>ENNReal.ofReal (‖window m ell F (causalFrequency advanced μ w) f‖^2)) := by
  have hc:Continuous (fun w:ℝ=>‖window m ell F (causalFrequency advanced μ w) f‖^2) := by
    exact ((window_continuous advanced μ hμ m ell F f).norm.pow 2).congr (fun _=>rfl)
  exact ENNReal.measurable_ofReal.comp hc.measurable

private def windowPair (m ell:ℕ)(F:Index)(z:ℂ)(f h:QuantumTest):ℂ :=
  inner ℂ (window m ell F z f) (window m ell F z h)

private theorem pair_price (u v:H):‖inner ℂ u v‖ ≤ ‖u‖^2+‖v‖^2 := by
  have h:‖inner ℂ u v‖ ≤ ‖u‖*‖v‖ := norm_inner_le_norm u v
  nlinarith only [h,sq_nonneg (‖u‖-‖v‖),sq_nonneg ‖u‖,sq_nonneg ‖v‖]

private theorem window_pair_tail (μ:ℝ)(hμ:0 < μ)(f h:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        (∫⁻w:ℝ,ENNReal.ofReal ‖windowPair m ell F (causalFrequency advanced μ w) f h‖)≤
          ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N₀,h₀⟩:=actual_bounded_theta_causal_tail μ hμ (1:H →L[ℂ] H) (embed f) (ε/2) (by positivity)
  obtain ⟨N₁,h₁⟩:=actual_bounded_theta_causal_tail μ hμ (1:H →L[ℂ] H) (embed h) (ε/2) (by positivity)
  refine ⟨max N₀ N₁,fun m hm ell hml=>?_⟩
  filter_upwards [h₀ m (by omega) ell hml,h₁ m (by omega) ell hml] with F hF₀ hF₁
  intro advanced
  have hp:=lintegral_mono (μ:=volume) (fun w:ℝ=>ENNReal.ofReal_le_ofReal
    (pair_price (window m ell F (causalFrequency advanced μ w) f)
      (window m ell F (causalFrequency advanced μ w) h)))
  simp_rw [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)] at hp
  rw [lintegral_add_left (window_energy_measurable advanced μ hμ m ell F f)] at hp
  have hf:(∫⁻w:ℝ,ENNReal.ofReal (‖window m ell F (causalFrequency advanced μ w) f‖^2))≤ENNReal.ofReal (ε/2) := by
    simpa only [window,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,ContinuousLinearMap.comp_apply,one_apply_eq_self] using hF₀ advanced
  have hh:(∫⁻w:ℝ,ENNReal.ofReal (‖window m ell F (causalFrequency advanced μ w) h‖^2))≤ENNReal.ofReal (ε/2) := by
    simpa only [window,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,ContinuousLinearMap.comp_apply,one_apply_eq_self] using hF₁ advanced
  apply hp.trans ((add_le_add hf hh).trans_eq ?_)
  rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

private def contactPair (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest):ℂ :=
  sourcePair (coreWindow m ell F z hz f) (affineCutoff m ell (resolventCore F z hz h))

private theorem contact_pair_tail (μ:ℝ)(hμ:0 < μ)(f h:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        (∫⁻w:ℝ,ENNReal.ofReal ‖contactPair m ell F (causalFrequency advanced μ w)
          (causal_nonreal advanced μ hμ w) f h‖)≤ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N₀,h₀⟩:=actual_bounded_theta_causal_tail μ hμ (1:H →L[ℂ] H) (embed f) (ε/2) (by positivity)
  obtain ⟨N₁,h₁⟩:=actual_affine_core_causal_tail μ hμ (coreEquiv h) (ε/2) (by positivity)
  refine ⟨max N₀ N₁,fun m hm ell hml=>?_⟩
  filter_upwards [h₀ m (by omega) ell hml,h₁ m (by omega) ell hml] with F hF₀ hF₁
  intro advanced
  have hp:=lintegral_mono (μ:=volume) (fun w:ℝ=>ENNReal.ofReal_le_ofReal
    (pair_price (embed (coreWindow m ell F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) f))
      (embed (affineCutoff m ell (resolventCore F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) h)))))
  have hw (w:ℝ):embed (coreWindow m ell F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) f)=
      window m ell F (causalFrequency advanced μ w) f := by
    exact (paid_mixed_core% window_core) m ell F _ _ f
  simp only [contactPair,sourcePair,hw]
  simp_rw [hw,ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)] at hp
  rw [lintegral_add_left (window_energy_measurable advanced μ hμ m ell F f)] at hp
  have hf:(∫⁻w:ℝ,ENNReal.ofReal (‖window m ell F (causalFrequency advanced μ w) f‖^2))≤ENNReal.ofReal (ε/2) := by
    simpa only [window,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,ContinuousLinearMap.comp_apply,one_apply_eq_self] using hF₀ advanced
  have hh:=hF₁ advanced
  have he (w:ℝ):causalCore F (coreEquiv h) advanced μ hμ w=
      resolventCore F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) h := by
    unfold causalCore resolventCore state
    rfl
  simp_rw [he] at hh
  apply hp.trans ((add_le_add hf hh).trans_eq ?_)
  rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring


elab "paid_moment_ward%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedWardPolarization 0) "LowEnergy") "ActualMixedWardPolarization"
  let name:=Name.str ns field.getId.eraseMacroScopes.toString
  unless (←getEnv).contains name do throwError "Missing actual complex Ward continuity"
  mkConstWithFreshMVarLevels name

private theorem ward_pair_continuous (advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)(g h:QuantumTest):
    Continuous (fun w:ℝ=>wardPair m ell F (causalFrequency advanced μ w)
      (causal_nonreal advanced μ hμ w) g h) := by
  have hj (f:QuantumTest):Continuous (fun w:ℝ=>(wardCurrent m ell F (causalFrequency advanced μ w)
      (causal_nonreal advanced μ hμ w) f:ℂ)) :=
    Complex.continuous_ofReal.comp ((paid_moment_ward% ward_continuous) advanced μ hμ m ell F f)
  have hc:=(((hj (g+h)).sub (hj (g-h))).sub
    (((hj (g+Complex.I • h)).sub (hj (g-Complex.I • h))).const_mul Complex.I)).div_const 4
  refine hc.congr (fun w=>?_)
  exact (actual_pair_polarization m ell F _ _ g h).symm

private theorem contact_pair_continuous (advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)(f h:QuantumTest):
    Continuous (fun w:ℝ=>contactPair m ell F (causalFrequency advanced μ w)
      (causal_nonreal advanced μ hμ w) f h) := by
  have hw:Continuous (fun w:ℝ=>embed (coreWindow m ell F (causalFrequency advanced μ w)
      (causal_nonreal advanced μ hμ w) f)) :=
    (window_continuous advanced μ hμ m ell F f).congr
      (fun w=>((paid_mixed_core% window_core) m ell F _ _ f).symm)
  have ha:Continuous (fun w:ℝ=>embed (affineCutoff m ell (resolventCore F
      (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) h))) := by
    have hc:Continuous (fun w:ℝ=>sourceRead F (coreEquiv h) (affineCutoff m ell)
        (finiteResolvent F (causalFrequency advanced μ w) (embed h))) :=
      (sourceRead F (coreEquiv h) (affineCutoff m ell)).continuous.comp
        (((paid_mixed_tail% frequency_continuous) advanced μ hμ F).clm_apply continuous_const)
    refine hc.congr (fun w=>?_)
    have he:(coreEquiv h:H)=embed h := rfl
    simpa only [resolventCore,LinearMap.coe_mk,AddHom.coe_mk,state,he] using
      source_read_resolvent F (coreEquiv h) (affineCutoff m ell) _ (causal_nonreal advanced μ hμ w)
  exact hw.inner (𝕜:=ℂ) ha

private def momentTerm (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):Fin 8 → ℂ :=
  let G0:=deltaGauge diagonalAction g
  let K0:=(deltaPhi diagonalAction-deltaGauge diagonalAction) g
  ![wardPair m ell F z hz g (diagonalAction g),
    windowPair m ell F z g (secondJet diagonalAction g),
    windowPair m ell F z (Gauge g) K0,
    windowPair m ell F z g (Gauge K0),
    windowPair m ell F z (relativeGenerator g) G0,
    windowPair m ell F z g (relativeGenerator G0),
    contactPair m ell F z hz g G0,
    star (contactPair m ell F z hz G0 g)]

private theorem term_continuous (advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)(g:QuantumTest)(i:Fin 8):
    Continuous (fun w:ℝ=>momentTerm m ell F (causalFrequency advanced μ w)
      (causal_nonreal advanced μ hμ w) g i) := by
  have hw (a b:QuantumTest):Continuous (fun w:ℝ=>windowPair m ell F (causalFrequency advanced μ w) a b) :=
    (window_continuous advanced μ hμ m ell F a).inner (𝕜:=ℂ)
      (window_continuous advanced μ hμ m ell F b)
  fin_cases i
  · exact ward_pair_continuous advanced μ hμ m ell F g (diagonalAction g)
  · exact hw _ _
  · exact hw _ _
  · exact hw _ _
  · exact hw _ _
  · exact hw _ _
  · exact contact_pair_continuous advanced μ hμ m ell F g (deltaGauge diagonalAction g)
  · exact (contact_pair_continuous advanced μ hμ m ell F (deltaGauge diagonalAction g) g).star

private theorem term_tail (μ:ℝ)(hμ:0 < μ)(g:QuantumTest)(i:Fin 8):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        (∫⁻w:ℝ,ENNReal.ofReal ‖momentTerm m ell F (causalFrequency advanced μ w)
          (causal_nonreal advanced μ hμ w) g i‖)≤ENNReal.ofReal ε := by
  fin_cases i
  · exact actual_pair_causal_tail μ hμ g (diagonalAction g)
  · exact window_pair_tail μ hμ g (secondJet diagonalAction g)
  · exact window_pair_tail μ hμ (Gauge g) ((deltaPhi diagonalAction-deltaGauge diagonalAction) g)
  · exact window_pair_tail μ hμ g (Gauge ((deltaPhi diagonalAction-deltaGauge diagonalAction) g))
  · exact window_pair_tail μ hμ (relativeGenerator g) (deltaGauge diagonalAction g)
  · exact window_pair_tail μ hμ g (relativeGenerator (deltaGauge diagonalAction g))
  · exact contact_pair_tail μ hμ g (deltaGauge diagonalAction g)
  · intro ε hε
    obtain ⟨N,hN⟩:=contact_pair_tail μ hμ (deltaGauge diagonalAction g) g ε hε
    refine ⟨N,fun m hm ell hml=>?_⟩
    filter_upwards [hN m hm ell hml] with F hF
    intro advanced
    change (∫⁻w:ℝ,ENNReal.ofReal ‖star (contactPair m ell F (causalFrequency advanced μ w)
      (causal_nonreal advanced μ hμ w) (deltaGauge diagonalAction g) g)‖)≤ENNReal.ofReal ε
    simpa only [norm_star] using hF advanced

private theorem fixed_word_tail (μ:ℝ)(hμ:0 < μ)(g:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        (∫⁻w:ℝ,ENNReal.ofReal ‖∑i:Fin 8,momentTerm m ell F (causalFrequency advanced μ w)
          (causal_nonreal advanced μ hμ w) g i‖)≤ENNReal.ofReal ε := by
  intro ε hε
  let δ:=ε/8
  have hd:0 < δ := by dsimp [δ];positivity
  choose N hN using (fun i:Fin 8=>term_tail μ hμ g i δ hd)
  refine ⟨Finset.univ.sup N,fun m hm ell hml=>?_⟩
  have hevent:∀ᶠF in (sourceFilter:Filter Index),∀i:Fin 8,∀advanced:Bool,
      (∫⁻w:ℝ,ENNReal.ofReal ‖momentTerm m ell F (causalFrequency advanced μ w)
        (causal_nonreal advanced μ hμ w) g i‖)≤ENNReal.ofReal δ := by
    apply Filter.eventually_all.mpr
    intro i
    exact hN i m ((Finset.le_sup (Finset.mem_univ i)).trans hm) ell hml
  filter_upwards [hevent] with F hF
  intro advanced
  have hp:=lintegral_mono (μ:=volume) (fun w:ℝ=>ENNReal.ofReal_le_ofReal
    (norm_sum_le Finset.univ (fun i:Fin 8=>momentTerm m ell F (causalFrequency advanced μ w)
      (causal_nonreal advanced μ hμ w) g i)))
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun _ _=>norm_nonneg _)] at hp
  have hmeas (i:Fin 8):Measurable (fun w:ℝ=>ENNReal.ofReal ‖momentTerm m ell F
      (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g i‖) :=
    ENNReal.measurable_ofReal.comp (term_continuous advanced μ hμ m ell F g i).norm.measurable
  rw [lintegral_finsetSum Finset.univ (fun i _=>hmeas i)] at hp
  apply hp.trans ((Finset.sum_le_sum (fun i _=>hF i advanced)).trans_eq ?_)
  rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _=>hd.le)]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  congr 1
  dsimp [δ]
  ring


private def endpoint (advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):ℂ :=
  sourcePair (thetaAction m ell (secondJet (resolventCore F (causalFrequency advanced μ w)
    (causal_nonreal advanced μ hμ w)) g)) (thetaAction m ell g)

private theorem fixed_word_return (g:QuantumTest):
    ∀ᶠF in (sourceFilter:Filter Index),∀m ell:ℕ,∀z:ℂ,∀hz:z.im≠0,
      z*(wardCurrent m ell F z hz g:ℂ)=
        (∑i:Fin 8,momentTerm m ell F z hz g i)-
          sourcePair (thetaAction m ell (secondJet (resolventCore F z hz) g)) (thetaAction m ell g) := by
  filter_upwards [fixed_source_jets g] with F hF m ell z hz
  obtain ⟨hg,hG,hK,hS⟩:=hF
  have h:=actual_whole_frequency_return m ell F z hz g
  dsimp only at h
  rw [hg,hG,hK,hS] at h
  rw [h]
  have hw (f:QuantumTest):window m ell F z f=embed (thetaAction m ell (resolventCore F z hz f)) :=
    ((paid_mixed_core% window_core) m ell F z hz f).symm
  have hs (u v:H):star (inner ℂ u v)=inner ℂ v u := inner_conj_symm (𝕜:=ℂ) v u
  simp [momentTerm,Fin.sum_univ_succ,windowPair,contactPair,sourcePair,coreWindow,
    Module.End.mul_apply,relativeGenerator,hw,hs]
  ring

/-- A finite original source jet family pays the complex first frequency moment.
The complete endpoint is integrated only after its common-pole cancellation. -/
theorem actual_complex_frequency_moment_tail (μ:ℝ)(hμ:0 < μ)(g:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        let f:=fun w:ℝ=>causalFrequency advanced μ w*
          (wardCurrent m ell F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g:ℂ)
        Integrable f ∧ ‖∫w:ℝ,f w‖≤ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=fixed_word_tail μ hμ g ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml,fixed_word_return g] with F hF hReturn
  intro advanced
  dsimp only
  let v:=fun w:ℝ=>∑i:Fin 8,momentTerm m ell F (causalFrequency advanced μ w)
    (causal_nonreal advanced μ hμ w) g i
  have hv:Integrable v := by
    refine ⟨(continuous_finsetSum Finset.univ (fun i _=>term_continuous advanced μ hμ m ell F g i)).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_norm]
    exact lt_of_le_of_lt (hF advanced) ENNReal.ofReal_lt_top
  have he:=actual_whole_endpoint_integral advanced μ hμ m ell F g
  change Integrable (endpoint advanced μ hμ m ell F g) ∧
    (∫w:ℝ,endpoint advanced μ hμ m ell F g w)=0 at he
  have hword: (fun w:ℝ=>causalFrequency advanced μ w*
      (wardCurrent m ell F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g:ℂ))=
      fun w:ℝ=>v w-endpoint advanced μ hμ m ell F g w := by
    funext w
    exact hReturn m ell _ _
  rw [hword]
  refine ⟨hv.sub he.1,?_⟩
  rw [integral_sub hv he.1,he.2,sub_zero]
  apply (norm_integral_le_lintegral_norm v).trans
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hF advanced)).trans_eq (ENNReal.toReal_ofReal hε.le)

/-- The signed real moment shares the same source event and both causal signs.
This retains the whole Ward combination before integration. -/
theorem actual_signed_frequency_moment_tail (μ:ℝ)(hμ:0 < μ)(g:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        let f:=fun w:ℝ=>w*wardCurrent m ell F (causalFrequency advanced μ w)
          (causal_nonreal advanced μ hμ w) g
        Integrable f ∧ |∫w:ℝ,f w|≤ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=actual_complex_frequency_moment_tail μ hμ g ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  obtain ⟨hi,hp⟩:=hF advanced
  dsimp only at hi hp ⊢
  have hr (w:ℝ):(causalFrequency advanced μ w*
      (wardCurrent m ell F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g:ℂ)).re=
      w*wardCurrent m ell F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g := by
    cases advanced <;> simp [causalFrequency,SourceResolventBandLimit.line,Complex.mul_re]
  have hir:Integrable (fun w:ℝ=>(causalFrequency advanced μ w*
      (wardCurrent m ell F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g:ℂ)).re) := by
    simpa only [RCLike.re_to_complex] using hi.re
  simp_rw [hr] at hir
  refine ⟨hir,?_⟩
  have he:=integral_re hi
  simp only [RCLike.re_to_complex] at he
  simp_rw [hr] at he
  rw [he]
  exact (Complex.abs_re_le_norm _).trans hp

end LowEnergy.ActualMixedWardMomentTail
