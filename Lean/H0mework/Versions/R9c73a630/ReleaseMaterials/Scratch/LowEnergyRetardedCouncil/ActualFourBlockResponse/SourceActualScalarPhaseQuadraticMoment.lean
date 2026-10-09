import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualScalarPhaseFrequencyReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualScalarPhaseQuadraticMoment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourcePhysicalKineticSquare SourceNativeCutoffContact SourceResolventBandLimit
open FullYSourceResolventGraphSplice ActualVectorJointCost ActualMixedCovarianceTail ActualMixedWindowGram
open ActualScalarPhaseJet ActualScalarPhaseFrequencyReturn ActualSylvesterCore ActualSylvesterChannels
open SourceJointResidualEnergy SourceRetardedGraph MeasureTheory Filter Lean Meta Elab Term
open scoped InnerProductSpace BigOperators ENNReal Matrix
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] compressionCore resolventCore diagonalAction phaseGenerator phaseJet phaseSecond
attribute [local irreducible] phasePair coreWindow sourcePair

elab "paid_quadratic_phase%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualScalarPhaseFrequencyReturn 0) "LowEnergy") "ActualScalarPhaseFrequencyReturn"
  let name:=Name.str ns field.getId.eraseMacroScopes.toString
  unless (←getEnv).contains name do throwError "Missing frozen actual phase source proof"
  mkConstWithFreshMVarLevels name
elab "paid_quadratic_compression%" : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualScalarCompressionJet 0) "LowEnergy") "ActualScalarCompressionJet") "compression_spectral")

private theorem pair_add_left(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_sub_left(f g h:QuantumTest):sourcePair (f-g) h=sourcePair f h-sourcePair g h := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_smul_left(c:ℂ)(f h:QuantumTest):sourcePair (c • f) h=star c*sourcePair f h := by
  simp only [sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
private theorem phase_pair_left(f h:QuantumTest):sourcePair (phaseGenerator f) h= -sourcePair f (phaseGenerator h) := by
  have hp:=(paid_quadratic_phase% phase_skew) f h
  linear_combination (norm:=ring) hp

/-- The whole phase polarization returns to a fixed original source jet family. -/
theorem actual_phase_pair_fixed_jets(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g h:QuantumTest):
    let W:=coreWindow m ell F z hz
    phasePair m ell F z hz g h=
      sourcePair (W (phaseGenerator (phaseGenerator g))) (W h)+
      (2:ℂ)*sourcePair (W (phaseGenerator g)) (W (phaseGenerator h))+
      sourcePair (W g) (W (phaseGenerator (phaseGenerator h))) := by
  dsimp only
  let W:=coreWindow m ell F z hz
  have hc(q:QuantumTest):thetaAction m ell (phaseGenerator q)=phaseGenerator (thetaAction m ell q) := by
    have h:=LinearMap.congr_fun ((paid_quadratic_phase% theta_phase_commute) m ell) q
    exact h.symm
  have hx(q:QuantumTest):thetaAction m ell (phaseJet (resolventCore F z hz) q)=
      phaseGenerator (W q)-W (phaseGenerator q) := by
    rw [(paid_quadratic_phase% phase_apply)]
    simp only [map_sub,hc]
    simp only [W,coreWindow,Module.End.mul_apply]
  have hs(q:QuantumTest):thetaAction m ell (phaseSecond (resolventCore F z hz) q)=
      phaseGenerator (phaseGenerator (W q))-(2:ℂ) • phaseGenerator (W (phaseGenerator q))+
      W (phaseGenerator (phaseGenerator q)) := by
    rw [(paid_quadratic_phase% phase_second_apply)]
    simp only [map_add,map_sub,map_smul,hc]
    simp only [W,coreWindow,Module.End.mul_apply]
  simp only [phasePair]
  rw [hx,hx,hs,hs]
  change (2:ℂ)*sourcePair (phaseGenerator (W g)-W (phaseGenerator g))
      (phaseGenerator (W h)-W (phaseGenerator h))+
    sourcePair (W g) (phaseGenerator (phaseGenerator (W h))-(2:ℂ) • phaseGenerator (W (phaseGenerator h))+
      W (phaseGenerator (phaseGenerator h)))+
    sourcePair (phaseGenerator (phaseGenerator (W g))-(2:ℂ) • phaseGenerator (W (phaseGenerator g))+
      W (phaseGenerator (phaseGenerator g))) (W h)=_
  simp only [pair_add_left,pair_sub_left,pair_smul_left,(paid_phase_frequency% pair_add_right),
    (paid_phase_frequency% pair_sub_right),(paid_phase_frequency% pair_smul_right),
    star_ofNat,phase_pair_left]
  dsimp only [W]
  ring

private theorem core_compression_spectral(F:Index):
    compressionCore F=∑i:SpectralIndex F,(channelValue F (some i):ℂ) • channelCore F (some i) := by
  classical
  apply LinearMap.ext
  intro q
  apply embed_injective
  rw [(paid_phase_inverse% compression_embed)]
  have h:=congrArg (fun T:H →L[ℂ] H=>T (embed q)) ((paid_quadratic_compression%) F)
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,actual_channel_core,
    channel_some,sum_apply,smul_apply,InnerProductSpace.rankOne_apply] at h ⊢
  exact h

private theorem star_return_frequency(a:ℝ)(z:ℂ)(hz:z.im≠0):
    z*star (((a:ℂ)-z)⁻¹+z⁻¹)=
      ((a:ℂ)+z-star z)*star (((a:ℂ)-z)⁻¹+z⁻¹)+(a:ℂ)*(-((star z)⁻¹)) := by
  have hs:star z≠0 := by
    intro h
    apply hz
    have he:=(congrArg Complex.im h)
    simpa only [Complex.star_def,Complex.conj_im,Complex.zero_im,neg_eq_zero] using he
  have ha:(a:ℂ)-star z≠0 := by
    intro h
    apply hz
    have he:=congrArg Complex.im h
    simpa only [Complex.sub_im,Complex.ofReal_im,Complex.star_def,Complex.conj_im,
      Complex.zero_im,zero_sub,neg_neg] using he
  have hr:star (a:ℂ)=(a:ℂ) := Complex.conj_ofReal a
  simp only [star_add,star_inv₀,star_sub,hr]
  field_simp [hs,ha]
  ring

private def causeGap(advanced:Bool)(μ:ℝ):ℂ := if advanced then -(2:ℂ)*(μ:ℂ)*Complex.I else (2:ℂ)*(μ:ℂ)*Complex.I
private theorem cause_gap(advanced:Bool)(μ w:ℝ):
    causalFrequency advanced μ w-star (causalFrequency advanced μ w)=causeGap advanced μ := by
  cases advanced <;> simp [causalFrequency,causeGap,SourceResolventBandLimit.line] <;> ring

/-- The original zero spectral channel on the same causal line. -/
def escapePole(advanced:Bool)(μ w:ℝ):ℂ := -(causalFrequency advanced μ w)⁻¹

theorem actual_phase_escape_pole(advanced:Bool)(μ w:ℝ):
    escapePole advanced μ w=pole (if advanced then -μ else μ) 0 w := by
  cases advanced
  · change -(line μ w)⁻¹=((0:ℂ)-line μ w)⁻¹
    rw [zero_sub,inv_neg]
  · change -(line (-μ) w)⁻¹=((0:ℂ)-line (-μ) w)⁻¹
    rw [zero_sub,inv_neg]


private theorem jet_spectral(J:End →ₗ[ℂ] End)(hJ:J 1=0)(F:Index)(z:ℂ)(hz:z.im≠0):
    J (resolventCore F z hz)=∑i:SpectralIndex F,
      (((channelValue F (some i):ℂ)-z)⁻¹+z⁻¹) • J (channelCore F (some i)) := by
  rw [(paid_phase_frequency% core_resolvent_spectral),map_add,map_smul,map_sum,hJ,smul_zero,zero_add]
  simp only [map_smul]

private theorem jet_endpoint_spectral(J:End →ₗ[ℂ] End)(hJ:J 1=0)
    (advanced:Bool)(μ:ℝ)(hμ:0<μ)(m ell:ℕ)(F:Index)(g h:QuantumTest)(w:ℝ):
    sourcePair (thetaAction m ell (J (resolventCore F (causalFrequency advanced μ w)
      ((paid_phase_frequency% causal_nonreal) advanced μ hμ w)) g)) (thetaAction m ell h)=
      ∑i:SpectralIndex F,star ((paid_phase_frequency% poleReturn) advanced μ (channelValue F (some i)) w)*
        sourcePair (thetaAction m ell (J (channelCore F (some i)) g)) (thetaAction m ell h) := by
  rw [jet_spectral J hJ]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,sourcePair,
    sum_inner,inner_smul_left,starRingEnd_apply]
  rfl

private theorem jet_endpoint_integral(J:End →ₗ[ℂ] End)(hJ:J 1=0)
    (advanced:Bool)(μ:ℝ)(hμ:0<μ)(m ell:ℕ)(F:Index)(g h:QuantumTest):
    let f:=fun w:ℝ=>sourcePair (thetaAction m ell (J (resolventCore F (causalFrequency advanced μ w)
      ((paid_phase_frequency% causal_nonreal) advanced μ hμ w)) g)) (thetaAction m ell h)
    Integrable f ∧ (∫w:ℝ,f w)=0 := by
  classical
  dsimp only
  let c(i:SpectralIndex F):ℂ:=sourcePair
    (thetaAction m ell (J (channelCore F (some i)) g)) (thetaAction m ell h)
  have hi(i:SpectralIndex F):Integrable (fun w:ℝ=>
      star ((paid_phase_frequency% poleReturn) advanced μ (channelValue F (some i)) w)*c i) :=
    ((paid_phase_frequency% causal_star_return_integrable) advanced μ _ hμ).mul_const _
  simp_rw [jet_endpoint_spectral J hJ advanced μ hμ m ell F g h]
  constructor
  · exact integrable_finsetSum _ (fun i _=>hi i)
  · rw [integral_finsetSum Finset.univ (fun i _=>hi i)]
    simp only [integral_mul_const,(paid_phase_frequency% causal_star_return_integral) advanced μ _ hμ,
      zero_mul,Finset.sum_const_zero]

private theorem jet_compression_charge(J:End →ₗ[ℂ] End)(m ell:ℕ)(F:Index)(g h:QuantumTest):
    sourcePair (thetaAction m ell (J (compressionCore F) g)) (thetaAction m ell h)=
      ∑i:SpectralIndex F,(channelValue F (some i):ℂ)*sourcePair
        (thetaAction m ell (J (channelCore F (some i)) g)) (thetaAction m ell h) := by
  have hr(a:ℝ):star (a:ℂ)=(a:ℂ) := Complex.conj_ofReal a
  rw [core_compression_spectral,map_sum]
  simp only [map_smul,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,sourcePair,
    sum_inner,inner_smul_left,starRingEnd_apply,hr]

/-- The frequency contact is renormalized on the complete source spectral family,
so every summand is a pole difference before its integral is taken. -/
private theorem weighted_jet_endpoint_integral(J:End →ₗ[ℂ] End)(hJ:J 1=0)
    (advanced:Bool)(μ:ℝ)(hμ:0<μ)(m ell:ℕ)(F:Index)(g h:QuantumTest):
    let A:=sourcePair (thetaAction m ell (J (compressionCore F) g)) (thetaAction m ell h)
    let f:=fun w:ℝ=>causalFrequency advanced μ w*
      sourcePair (thetaAction m ell (J (resolventCore F (causalFrequency advanced μ w)
        ((paid_phase_frequency% causal_nonreal) advanced μ hμ w)) g)) (thetaAction m ell h)-
      A*star (escapePole advanced μ w)
    Integrable f ∧ (∫w:ℝ,f w)=0 := by
  classical
  dsimp only
  let c(i:SpectralIndex F):ℂ:=sourcePair
    (thetaAction m ell (J (channelCore F (some i)) g)) (thetaAction m ell h)
  have he(w:ℝ):causalFrequency advanced μ w*
      sourcePair (thetaAction m ell (J (resolventCore F (causalFrequency advanced μ w)
        ((paid_phase_frequency% causal_nonreal) advanced μ hμ w)) g)) (thetaAction m ell h)-
      sourcePair (thetaAction m ell (J (compressionCore F) g)) (thetaAction m ell h)*star (escapePole advanced μ w)=
      ∑i:SpectralIndex F,((channelValue F (some i):ℂ)+causeGap advanced μ)*
        star ((paid_phase_frequency% poleReturn) advanced μ (channelValue F (some i)) w)*c i := by
    rw [jet_endpoint_spectral J hJ advanced μ hμ m ell F g h w,jet_compression_charge]
    simp only [Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hk:=star_return_frequency (channelValue F (some i)) (causalFrequency advanced μ w)
      ((paid_phase_frequency% causal_nonreal) advanced μ hμ w)
    rw [add_sub_assoc,cause_gap] at hk
    have hescape:star (escapePole advanced μ w)= -((star (causalFrequency advanced μ w))⁻¹) := by
      simp only [escapePole,star_neg,star_inv₀]
    rw [←hescape] at hk
    change causalFrequency advanced μ w*star ((paid_phase_frequency% poleReturn) advanced μ (channelValue F (some i)) w)=
      ((channelValue F (some i):ℂ)+causeGap advanced μ)*star ((paid_phase_frequency% poleReturn) advanced μ (channelValue F (some i)) w)+
      (channelValue F (some i):ℂ)*star (escapePole advanced μ w) at hk
    linear_combination (norm:=ring) hk*c i
  have hi(i:SpectralIndex F):Integrable (fun w:ℝ=>
      ((channelValue F (some i):ℂ)+causeGap advanced μ)*
        star ((paid_phase_frequency% poleReturn) advanced μ (channelValue F (some i)) w)*c i) :=
    (((paid_phase_frequency% causal_star_return_integrable) advanced μ _ hμ).const_mul _).mul_const _
  simp_rw [he]
  constructor
  · exact integrable_finsetSum _ (fun i _=>hi i)
  · rw [integral_finsetSum Finset.univ (fun i _=>hi i)]
    simp only [integral_mul_const,integral_const_mul,
      (paid_phase_frequency% causal_star_return_integral) advanced μ _ hμ,mul_zero,zero_mul,Finset.sum_const_zero]

private theorem bare_endpoint_integral(advanced:Bool)(μ:ℝ)(hμ:0<μ)(m ell:ℕ)(F:Index)(g h:QuantumTest):
    let A:=sourcePair (thetaAction m ell g) (thetaAction m ell h)
    let f:=fun w:ℝ=>sourcePair (coreWindow m ell F (causalFrequency advanced μ w)
      ((paid_phase_frequency% causal_nonreal) advanced μ hμ w) g) (thetaAction m ell h)-
      A*star (escapePole advanced μ w)
    Integrable f ∧ (∫w:ℝ,f w)=0 := by
  classical
  dsimp only
  let c(i:SpectralIndex F):ℂ:=sourcePair
    (thetaAction m ell (channelCore F (some i) g)) (thetaAction m ell h)
  have he(w:ℝ):sourcePair (coreWindow m ell F (causalFrequency advanced μ w)
      ((paid_phase_frequency% causal_nonreal) advanced μ hμ w) g) (thetaAction m ell h)-
      sourcePair (thetaAction m ell g) (thetaAction m ell h)*star (escapePole advanced μ w)=
      ∑i:SpectralIndex F,star ((paid_phase_frequency% poleReturn) advanced μ (channelValue F (some i)) w)*c i := by
    simp only [coreWindow,Module.End.mul_apply]
    rw [(paid_phase_frequency% core_resolvent_spectral)]
    simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,LinearMap.sum_apply,
      map_add,map_smul,map_sum,sourcePair,inner_add_left,inner_smul_left,sum_inner,
      starRingEnd_apply,escapePole]
    dsimp only [c,sourcePair]
    have hp(i:SpectralIndex F):(paid_phase_frequency% poleReturn) advanced μ (channelValue F (some i)) w=
      (((channelValue F (some i):ℂ)-causalFrequency advanced μ w)⁻¹+(causalFrequency advanced μ w)⁻¹) := rfl
    simp only [hp]
    ring_nf
    apply Finset.sum_congr rfl
    intro i _
    simp only [sourcePair,star_add,star_inv₀]
    ring
  have hi(i:SpectralIndex F):Integrable (fun w:ℝ=>
      star ((paid_phase_frequency% poleReturn) advanced μ (channelValue F (some i)) w)*c i) :=
    ((paid_phase_frequency% causal_star_return_integrable) advanced μ _ hμ).mul_const _
  simp_rw [he]
  constructor
  · exact integrable_finsetSum _ (fun i _=>hi i)
  · rw [integral_finsetSum Finset.univ (fun i _=>hi i)]
    simp only [integral_mul_const,(paid_phase_frequency% causal_star_return_integral) advanced μ _ hμ,
      zero_mul,Finset.sum_const_zero]

private def sourceLeft(g:QuantumTest):Fin 6 → QuantumTest :=
  ![phaseGenerator (phaseGenerator g),phaseGenerator g,g,g,phaseGenerator g,g]
private def sourceRight(g:QuantumTest):Fin 6 → QuantumTest :=
  let h:=(diagonalAction*diagonalAction) g
  ![h,(2:ℂ) • phaseGenerator h,phaseGenerator (phaseGenerator h),
    phaseSecond (diagonalAction*diagonalAction) g,(-2:ℂ) • phaseJet (diagonalAction*diagonalAction) g,
    (-2:ℂ) • phaseGenerator (phaseJet (diagonalAction*diagonalAction) g)]
private def qp(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g h:QuantumTest):ℂ :=
  sourcePair (coreWindow m ell F z hz g) (coreWindow m ell F z hz h)
private def sourceWord(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):ℂ :=
  ∑i:Fin 6,qp m ell F z hz (sourceLeft g i) (sourceRight g i)

private theorem source_word_reduced(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    sourceWord m ell F z hz g=
      phasePair m ell F z hz g ((diagonalAction*diagonalAction) g)+
      sourcePair (coreWindow m ell F z hz g)
        (coreWindow m ell F z hz (phaseSecond (diagonalAction*diagonalAction) g))-
      (2:ℂ)*sourcePair (coreWindow m ell F z hz (phaseGenerator g))
        (coreWindow m ell F z hz (phaseJet (diagonalAction*diagonalAction) g))-
      (2:ℂ)*sourcePair (coreWindow m ell F z hz g)
        (coreWindow m ell F z hz (phaseGenerator (phaseJet (diagonalAction*diagonalAction) g))) := by
  rw [actual_phase_pair_fixed_jets]
  simp only [sourceWord,sourceLeft,sourceRight,qp,Fin.sum_univ_succ,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.sum_univ_zero,map_smul,(paid_phase_frequency% pair_smul_right)]
  ring

private theorem qp_hilbert(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g h:QuantumTest):
    qp m ell F z hz g h=inner ℂ (window m ell F z g) (window m ell F z h) := by
  simp only [qp,coreWindow,Module.End.mul_apply,sourcePair,(paid_mixed_core% window_core)]

private theorem qp_continuous(advanced:Bool)(μ:ℝ)(hμ:0<μ)(m ell:ℕ)(F:Index)(g h:QuantumTest):
    Continuous (fun w:ℝ=>qp m ell F (causalFrequency advanced μ w)
      ((paid_phase_frequency% causal_nonreal) advanced μ hμ w) g h) := by
  simp_rw [qp_hilbert]
  exact ((paid_phase_moment% window_continuous) advanced μ hμ m ell F g).inner (𝕜:=ℂ)
    ((paid_phase_moment% window_continuous) advanced μ hμ m ell F h)

private theorem qp_tail(μ:ℝ)(hμ:0<μ)(g h:QuantumTest):
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        (∫⁻w:ℝ,ENNReal.ofReal ‖qp m ell F (causalFrequency advanced μ w)
          ((paid_phase_frequency% causal_nonreal) advanced μ hμ w) g h‖)≤ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=(paid_phase_moment% window_pair_tail) μ hμ g h ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  simp_rw [qp_hilbert]
  exact hF advanced

private theorem source_word_tail(μ:ℝ)(hμ:0<μ)(g:QuantumTest):
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        (∫⁻w:ℝ,ENNReal.ofReal ‖sourceWord m ell F (causalFrequency advanced μ w)
          ((paid_phase_frequency% causal_nonreal) advanced μ hμ w) g‖)≤ENNReal.ofReal ε := by
  intro ε hε
  let δ:=ε/6
  have hd:0<δ := by dsimp [δ];positivity
  choose N hN using (fun i:Fin 6=>qp_tail μ hμ (sourceLeft g i) (sourceRight g i) δ hd)
  refine ⟨Finset.univ.sup N,fun m hm ell hml=>?_⟩
  have hevent:∀ᶠF in (sourceFilter:Filter Index),∀i:Fin 6,∀advanced:Bool,
      (∫⁻w:ℝ,ENNReal.ofReal ‖qp m ell F (causalFrequency advanced μ w)
        ((paid_phase_frequency% causal_nonreal) advanced μ hμ w) (sourceLeft g i) (sourceRight g i)‖)≤ENNReal.ofReal δ := by
    apply Filter.eventually_all.mpr
    intro i
    exact hN i m ((Finset.le_sup (Finset.mem_univ i)).trans hm) ell hml
  filter_upwards [hevent] with F hF
  intro advanced
  have hp:=lintegral_mono (μ:=volume) (fun w:ℝ=>ENNReal.ofReal_le_ofReal
    (norm_sum_le Finset.univ (fun i:Fin 6=>qp m ell F (causalFrequency advanced μ w)
      ((paid_phase_frequency% causal_nonreal) advanced μ hμ w) (sourceLeft g i) (sourceRight g i))))
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun _ _=>norm_nonneg _)] at hp
  have hmeas(i:Fin 6):Measurable (fun w:ℝ=>ENNReal.ofReal ‖qp m ell F (causalFrequency advanced μ w)
      ((paid_phase_frequency% causal_nonreal) advanced μ hμ w) (sourceLeft g i) (sourceRight g i)‖) :=
    ENNReal.measurable_ofReal.comp (qp_continuous advanced μ hμ m ell F _ _).norm.measurable
  rw [lintegral_finsetSum Finset.univ (fun i _=>hmeas i)] at hp
  apply hp.trans ((Finset.sum_le_sum (fun i _=>hF i advanced)).trans_eq ?_)
  rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _=>hd.le)]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  congr 1
  dsimp [δ]
  ring

private theorem inverse_theta(m ell:ℕ)(f:QuantumTest):
    inverseVolumeAction (thetaAction m ell f)=thetaAction m ell (inverseVolumeAction f) := by
  apply DFunLike.ext
  intro z
  change (SourcePhysicalKineticSquare.reciprocalVolume z:ℂ) • ((theta m ell z:ℂ) • f z)=
    (theta m ell z:ℂ) • ((SourcePhysicalKineticSquare.reciprocalVolume z:ℂ) • f z)
  exact smul_comm _ _ _

/-- This charge is an original fixed seed, independent of F, omega and cause. -/
def sourceCharge(m ell:ℕ)(g:QuantumTest):ℂ :=
  (-2*(phaseCoefficient:ℂ))*sourcePair (thetaAction m ell g) (inverseVolumeAction (thetaAction m ell g))

private theorem source_charge_identity(m ell:ℕ)(g:QuantumTest):
    sourceCharge m ell g=
      sourcePair (thetaAction m ell (phaseSecond diagonalAction g)) (thetaAction m ell g)+
      sourcePair (thetaAction m ell g) (thetaAction m ell (phaseSecond diagonalAction g)) := by
  have h2:phaseSecond diagonalAction=-(phaseCoefficient:ℂ) • inverseVolumeAction := by
    simpa only [phaseCoefficient,Complex.ofReal_mul,Complex.ofReal_pow,neg_mul] using actual_source_inverse_volume_phase_jet
  have hu(f h:QuantumTest):sourcePair f (inverseVolumeAction h)=sourcePair (inverseVolumeAction f) h :=
    GaussNativeForm.multiply_pair _ _ _ _
  have hr:star (phaseCoefficient:ℂ)=(phaseCoefficient:ℂ) := Complex.conj_ofReal _
  rw [h2]
  simp only [LinearMap.smul_apply,map_smul,pair_smul_left,(paid_phase_frequency% pair_smul_right),
    star_neg,hr,←inverse_theta]
  rw [←hu]
  unfold sourceCharge
  ring

private def contactWord(advanced:Bool)(μ:ℝ)(hμ:0<μ)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):ℂ :=
  let z:=causalFrequency advanced μ w
  let R:=resolventCore F z ((paid_phase_frequency% causal_nonreal) advanced μ hμ w)
  (2:ℂ)*sourcePair (thetaAction m ell (phaseJet R g)) (thetaAction m ell (phaseJet diagonalAction g))+
    sourcePair (thetaAction m ell (phaseSecond R g)) (thetaAction m ell (diagonalAction g))+
    (sourcePair (coreWindow m ell F z ((paid_phase_frequency% causal_nonreal) advanced μ hμ w) g)
      (thetaAction m ell (phaseSecond diagonalAction g))-
      sourcePair (thetaAction m ell g) (thetaAction m ell (phaseSecond diagonalAction g))*star (escapePole advanced μ w))+
    (z*sourcePair (thetaAction m ell (phaseSecond R g)) (thetaAction m ell g)-
      sourcePair (thetaAction m ell (phaseSecond diagonalAction g)) (thetaAction m ell g)*star (escapePole advanced μ w))

private theorem contact_word_integral(g:QuantumTest):
    ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,∀μ:ℝ,∀hμ:0<μ,∀m ell:ℕ,
      Integrable (contactWord advanced μ hμ m ell F g) ∧
      (∫w:ℝ,contactWord advanced μ hμ m ell F g w)=0 := by
  filter_upwards [(paid_quadratic_phase% fixed_source_jets) g] with F hF advanced μ hμ m ell
  obtain ⟨_,_,h2⟩:=hF
  have h1:=jet_endpoint_integral phaseJet (paid_quadratic_phase% phase_one) advanced μ hμ m ell F g (phaseJet diagonalAction g)
  have hs:=actual_phase_whole_endpoint_pair_integral advanced μ hμ m ell F g (diagonalAction g)
  have hb:=bare_endpoint_integral advanced μ hμ m ell F g (phaseSecond diagonalAction g)
  have hz:=weighted_jet_endpoint_integral phaseSecond (paid_quadratic_phase% phase_second_one) advanced μ hμ m ell F g g
  dsimp only at h1 hs hb hz
  rw [h2] at hz
  change Integrable (fun w:ℝ=>(2:ℂ)*_+_+_+_) ∧ _
  constructor
  · exact (((h1.1.const_mul (2:ℂ)).add hs.1).add hb.1).add hz.1
  · simp only [contactWord]
    have ha1:=integral_add (h1.1.const_mul (2:ℂ)) hs.1
    have ha2:=integral_add ((h1.1.const_mul (2:ℂ)).add hs.1) hb.1
    have ha3:=integral_add (((h1.1.const_mul (2:ℂ)).add hs.1).add hb.1) hz.1
    simp only [Pi.add_apply] at ha1 ha2 ha3
    rw [ha3,ha2,ha1,integral_const_mul,h1.2,hs.2,hb.2,hz.2]
    ring


/-- The natural compensation uses star of the same cause's escape pole. -/
def compensatedQuadratic(advanced:Bool)(μ:ℝ)(hμ:0<μ)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):ℂ :=
  let z:=causalFrequency advanced μ w
  z^2*phasePair m ell F z ((paid_phase_frequency% causal_nonreal) advanced μ hμ w) g g+
    sourceCharge m ell g*star (escapePole advanced μ w)

private theorem fixed_word_return(g:QuantumTest):
    ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,∀μ:ℝ,∀hμ:0<μ,∀m ell:ℕ,∀w:ℝ,
      compensatedQuadratic advanced μ hμ m ell F g w=
        sourceWord m ell F (causalFrequency advanced μ w)
          ((paid_phase_frequency% causal_nonreal) advanced μ hμ w) g-
        contactWord advanced μ hμ m ell F g w := by
  filter_upwards [actual_source_phase_square_frequency_return g] with F hF advanced μ hμ m ell w
  have h:=hF m ell (causalFrequency advanced μ w) ((paid_phase_frequency% causal_nonreal) advanced μ hμ w)
  dsimp only at h
  have hU:sourcePair (coreWindow m ell F (causalFrequency advanced μ w)
      ((paid_phase_frequency% causal_nonreal) advanced μ hμ w) g)
      (thetaAction m ell (phaseSecond diagonalAction g))=
      -(phaseCoefficient:ℂ)*sourcePair (coreWindow m ell F (causalFrequency advanced μ w)
        ((paid_phase_frequency% causal_nonreal) advanced μ hμ w) g)
        (thetaAction m ell (inverseVolumeAction g)) := by
    have h2:phaseSecond diagonalAction=-(phaseCoefficient:ℂ) • inverseVolumeAction := by
      simpa only [phaseCoefficient,Complex.ofReal_mul,Complex.ofReal_pow,neg_mul] using actual_source_inverse_volume_phase_jet
    rw [h2]
    simp only [LinearMap.smul_apply,map_smul,(paid_phase_frequency% pair_smul_right)]
  rw [source_word_reduced]
  simp only [compensatedQuadratic,contactWord,source_charge_identity,coreWindow,Module.End.mul_apply] at h hU ⊢
  linear_combination (norm:=ring) h+hU

/-- The original finite source jet family pays the full complex compensated
quadratic moment. N is chosen before F, cutoff, frequency and both causes. -/
theorem actual_complex_compensated_quadratic_moment_tail(μ:ℝ)(hμ:0<μ)(g:QuantumTest):
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (compensatedQuadratic advanced μ hμ m ell F g) ∧
        ‖∫w:ℝ,compensatedQuadratic advanced μ hμ m ell F g w‖≤ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=source_word_tail μ hμ g ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml,fixed_word_return g,contact_word_integral g] with F hF hReturn hContact
  intro advanced
  let v:=fun w:ℝ=>sourceWord m ell F (causalFrequency advanced μ w)
    ((paid_phase_frequency% causal_nonreal) advanced μ hμ w) g
  have hv:Integrable v := by
    refine ⟨(continuous_finsetSum Finset.univ (fun i _=>qp_continuous advanced μ hμ m ell F
      (sourceLeft g i) (sourceRight g i))).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_norm]
    exact lt_of_le_of_lt (hF advanced) ENNReal.ofReal_lt_top
  have hc:=hContact advanced μ hμ m ell
  have hword:compensatedQuadratic advanced μ hμ m ell F g=
      fun w:ℝ=>v w-contactWord advanced μ hμ m ell F g w := by
    funext w
    exact hReturn advanced μ hμ m ell w
  rw [hword]
  refine ⟨hv.sub hc.1,?_⟩
  rw [integral_sub hv hc.1,hc.2,sub_zero]
  apply (norm_integral_le_lintegral_norm v).trans
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hF advanced)).trans_eq (ENNReal.toReal_ofReal hε.le)

/-- The signed price is the same compensated source event, with both causal signs. -/
theorem actual_signed_compensated_quadratic_moment_tail(μ:ℝ)(hμ:0<μ)(g:QuantumTest):
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (fun w:ℝ=>(compensatedQuadratic advanced μ hμ m ell F g w).re) ∧
        |∫w:ℝ,(compensatedQuadratic advanced μ hμ m ell F g w).re|≤ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=actual_complex_compensated_quadratic_moment_tail μ hμ g ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  have h:=hF advanced
  refine ⟨h.1.re,?_⟩
  have he:=integral_re h.1
  simp only [RCLike.re_to_complex] at he
  rw [he]
  exact (Complex.abs_re_le_norm _).trans h.2

private theorem source_mu_positive:0<sourceMu := lt_of_lt_of_le (by norm_num) source_mu_large

/-- The consumer uses the original source damping, with no new normalization. -/
theorem actual_source_signed_quadratic_moment_tail(g:QuantumTest):
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (fun w:ℝ=>(compensatedQuadratic advanced sourceMu source_mu_positive m ell F g w).re) ∧
        |∫w:ℝ,(compensatedQuadratic advanced sourceMu source_mu_positive m ell F g w).re|≤ε :=
  actual_signed_compensated_quadratic_moment_tail sourceMu source_mu_positive g

end LowEnergy.ActualScalarPhaseQuadraticMoment
