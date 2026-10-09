import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualLocalizedNativeWorkReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualCausalBulkTime
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualCausalBulkBudget
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedCoframeTailPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiScalarCausalFrequencyKernel
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiRadialCausalFrequency
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiReverseFrequencyDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualBalancedFixedContactPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open GaussNativeEnergy GaussNativeForm SourceQuantumScalarChart SourceRetardedGraph
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourceScalarAffineCutoffTail
open SourceScalarVirialBulk SourceScalarGaugeScale SourceCoframeVolumeCurrent SourceHamiltonianScaleJet
open SourceNativeCutoffContact ActualMixedCovarianceTail ActualMixedWindowGram ActualVectorJointCost
open ActualSecondPressureMagneticPayment ActualBalancedForceRetardedPayment ActualLocalizedNativeWorkReturn
open ActualScalarPhaseFrequencyReturn ActualShiftedQuadraticWardPayment ActualAffineCutoffCausalTail
open ActualMixedWardMomentTail ActualCausalBulkTime SourceBulkTwoTime SourceBulkParseval
open ScalarCausalFrequencyMoment ReverseNativeFrequencyWard ActualVectorBulkSourcePrice
open SourceInverseNoetherChannelGap
open SourceJointResidualEnergy SourceFourPoleEnergyClosed SourceResolventBandLimit
open SourceLocalizedInverseFormPayment ReverseScalarGaugeWard Lean Meta Elab Term MeasureTheory Filter
open scoped Topology InnerProductSpace BigOperators ENNReal
private abbrev End:=QuantumTest →ₗ[ℂ] QuantumTest
private abbrev inputCore(f:QuantumTest):diagonal.domain:=coreEquiv f
attribute [local irreducible] sourcePair compressionCore resolventCore coreWindow nonmagneticSecondField

def balancedGenerator:End := (3:ℂ) • Phi-(12:ℂ) • Gauge-(6:ℂ) • Coframe

elab "paid_fixed_contact%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedWardMomentTail 0) "LowEnergy") "ActualMixedWardMomentTail"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)
elab "paid_fixed_coframe%" : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedCoframeTailPayment 0) "LowEnergy") "ActualMixedCoframeTailPayment"
  mkConstWithFreshMVarLevels (Name.str ns "actual_coframe_theta_zero")
elab "paid_fixed_inverse%" : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualShiftedQuadraticWardPayment 0) "LowEnergy") "ActualShiftedQuadraticWardPayment"
  mkConstWithFreshMVarLevels (Name.str ns "inverse_input")

private theorem pair_add_left(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_sub_left(f g h:QuantumTest):sourcePair (f-g) h=sourcePair f h-sourcePair g h := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_real_left(r:ℝ)(f h:QuantumTest):sourcePair ((r:ℂ) • f) h=(r:ℂ)*sourcePair f h := by
  simp only [sourcePair,map_smul,inner_smul_left]
  rw [show starRingEnd ℂ (r:ℂ)=(r:ℂ) from Complex.conj_ofReal r]

/-- The generator decomposition retains all three genuine source directions. -/
theorem actual_balanced_force_source(F:Index):
    balancedCompressionForce F=balancedGenerator*compressionCore F-compressionCore F*balancedGenerator-
      (18:ℂ) • compressionCore F := by
  rw [actual_balanced_compression_source]
  unfold balancedGenerator
  simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm]
  rw [←SourceScalarAffineScaleTransport.generator_commutator,
    ←SourceGaugeScaleTransport.generator_commutator,←SourceGaugeCoframeJets.K_commutator]
  module

private theorem generator_pair(f h:QuantumTest):
    sourcePair f (balancedGenerator h)= -sourcePair (balancedGenerator f) h := by
  unfold balancedGenerator
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,pair_sub_left,
    (paid_phase_frequency% pair_sub_right),(paid_phase_frequency% pair_smul_right)]
  rw [show (3:ℂ)=((3:ℝ):ℂ) by norm_num,show (12:ℂ)=((12:ℝ):ℂ) by norm_num,
    show (6:ℂ)=((6:ℝ):ℂ) by norm_num,pair_real_left,pair_real_left,pair_real_left]
  rw [(paid_shifted_response% phi_pair),(paid_shifted_response% gauge_pair),
    (paid_shifted_response% coframe_pair)]
  ring

theorem actual_balanced_generator_cutoff(m ell:ℕ):
    balancedGenerator*thetaAction m ell-thetaAction m ell*balancedGenerator=
      (3:ℂ) • affineCutoff m ell := by
  calc
    _=(3:ℂ) • (Phi*thetaAction m ell-thetaAction m ell*Phi)-
      (12:ℂ) • (Gauge*thetaAction m ell-thetaAction m ell*Gauge)-
      (6:ℂ) • (Coframe*thetaAction m ell-thetaAction m ell*Coframe) := by
        unfold balancedGenerator
        simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm]
        module
    _= _ := by
      rw [SourceScalarAffineScaleTransport.generator_commutator,
        SourceGaugeScaleTransport.generator_commutator,SourceGaugeCoframeJets.K_commutator,
        actual_gauge_cutoff_zero,paid_fixed_coframe%]
      change _=(3:ℂ) • deltaPhi (thetaAction m ell)
      module

def generatorContact(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest):ℂ :=
  let R:=resolventCore F z hz
  let Z:=R*(balancedGenerator*compressionCore F-compressionCore F*balancedGenerator)*R
  sourcePair (thetaAction m ell (Z f)) (coreWindow m ell F z hz h)+
    sourcePair (coreWindow m ell F z hz f) (thetaAction m ell (Z h))

def compressionContact(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest):ℂ :=
  let R:=resolventCore F z hz
  let Z:=R*compressionCore F*R
  sourcePair (thetaAction m ell (Z f)) (coreWindow m ell F z hz h)+
    sourcePair (coreWindow m ell F z hz f) (thetaAction m ell (Z h))

/-- BF's two fixed contacts stay together, including the full frequency part. -/
theorem actual_fixed_balanced_contact_source(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    fixedBalancedContact m ell F z hz g=
      generatorContact m ell F z hz g (nonmagneticSecondField g)-
        (18:ℂ)*compressionContact m ell F z hz g (nonmagneticSecondField g) := by
  unfold fixedBalancedContact generatorContact compressionContact
  dsimp only
  rw [actual_balanced_force_source]
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,Module.End.mul_apply,
    LinearMap.sub_apply,LinearMap.smul_apply,map_sub,map_smul,pair_sub_left,
    (paid_phase_frequency% pair_sub_right),(paid_phase_frequency% pair_smul_right)]
  rw [show (18:ℂ)=((18:ℝ):ℂ) by norm_num,pair_real_left]
  ring

private theorem generator_window(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest):
    thetaAction m ell ((resolventCore F z hz*
      (balancedGenerator*compressionCore F-compressionCore F*balancedGenerator)*resolventCore F z hz) f)=
      coreWindow m ell F z hz (balancedGenerator f)-balancedGenerator (coreWindow m ell F z hz f)+
        (3:ℂ) • affineCutoff m ell (resolventCore F z hz f) := by
  have h:=paid_fixed_inverse% balancedGenerator F z hz
  have ht:=actual_balanced_generator_cutoff m ell
  have he:=congrArg (fun A:End=>thetaAction m ell*A) h
  have hc:=congrArg (fun A:End=>A*resolventCore F z hz) ht
  simp only [coreWindow] at *
  have hv:=LinearMap.congr_fun he f
  have hcv:=LinearMap.congr_fun hc f
  simp only [Module.End.mul_apply,LinearMap.add_apply,LinearMap.sub_apply,
    LinearMap.smul_apply,map_add,map_sub] at hv hcv ⊢
  linear_combination (norm:=module) hv+hcv

/-- Both moving generator reads cancel by the original skew source, leaving
fixed inputs and the real affine cutoff contact in its original positions. -/
theorem actual_generator_fixed_contact(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest):
    generatorContact m ell F z hz f h=
      sourcePair (coreWindow m ell F z hz (balancedGenerator f)) (coreWindow m ell F z hz h)+
      sourcePair (coreWindow m ell F z hz f) (coreWindow m ell F z hz (balancedGenerator h))+
      (3:ℂ)*sourcePair (affineCutoff m ell (resolventCore F z hz f)) (coreWindow m ell F z hz h)+
      (3:ℂ)*sourcePair (coreWindow m ell F z hz f) (affineCutoff m ell (resolventCore F z hz h)) := by
  unfold generatorContact
  dsimp only
  rw [generator_window,generator_window]
  simp only [pair_add_left,pair_sub_left,(paid_phase_frequency% pair_add_right),
    (paid_phase_frequency% pair_sub_right),(paid_phase_frequency% pair_smul_right)]
  rw [show (3:ℂ)=((3:ℝ):ℂ) by norm_num,pair_real_left,generator_pair]
  ring


elab "paid_fixed_bulk%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualCausalBulkTime 0) "LowEnergy") "ActualCausalBulkTime"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)
elab "paid_fixed_channel%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiReverseFrequencyDerivative 0) "LowEnergy") "ReverseNativeFrequencyWard"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)

private theorem right_triple_integrable(μ a b:ℝ)(hμ:0 < μ):
    Integrable (fun w:ℝ=>star (pole μ a w)*(pole μ b w)^2) := by
  have h:=(RCLike.conjLIE (K:=ℂ)).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
    (actual_scalar_causal_triple_integrable μ b a hμ)
  exact h.congr (Eventually.of_forall (fun w=>by
    change star (star (pole μ b w)^2*pole μ a w)=_
    simp only [star_mul,star_pow,star_star,mul_comm]))
private theorem right_triple_integral(μ a b:ℝ)(hμ:0 < μ):
    (∫w:ℝ,star (pole μ a w)*(pole μ b w)^2)=
      (2*Real.pi:ℂ)*Complex.I*(gap μ a b)⁻¹^2 := by
  have he:(∫w:ℝ,star (pole μ a w)*(pole μ b w)^2)=
      star (∫w:ℝ,star (pole μ b w)^2*pole μ a w) := by
    change _=(starRingEnd ℂ) (∫w:ℝ,star (pole μ b w)^2*pole μ a w)
    rw [←integral_conj]
    apply integral_congr_ae
    exact Eventually.of_forall (fun w=>by
      simp only [starRingEnd_apply,star_mul,star_pow,star_star,mul_comm])
  rw [he,actual_scalar_causal_triple_integral μ b a hμ]
  have hg:star (gap μ b a)=gap μ a b := by
    simp only [gap,star_add,star_mul,star_sub,star_ofNat,Complex.star_def,Complex.conj_ofReal,Complex.conj_I]
    ring
  simp only [star_div₀,star_mul,star_pow]
  rw [hg]
  simp only [Complex.star_def,map_neg,map_ofNat,Complex.conj_ofReal,Complex.conj_I]
  simp only [div_eq_mul_inv,inv_pow]
  ring

private def compressionKernel(μ a b w:ℝ):ℂ :=
  (a:ℂ)*(star (pole μ a w)^2*pole μ b w)+(b:ℂ)*(star (pole μ a w)*(pole μ b w)^2)
private theorem compression_kernel_integrable(μ a b:ℝ)(hμ:0 < μ):Integrable (compressionKernel μ a b) :=
  ((actual_scalar_causal_triple_integrable μ a b hμ).const_mul (a:ℂ)).add
    ((right_triple_integrable μ a b hμ).const_mul (b:ℂ))
private theorem compression_kernel_integral(μ a b:ℝ)(hμ:0 < μ):
    (∫w:ℝ,compressionKernel μ a b w)=
      (2*Real.pi:ℂ)*((gap μ a b)⁻¹-(2*μ:ℂ)*(gap μ a b)⁻¹^2) := by
  have hL:Integrable (fun w:ℝ=>(a:ℂ)*(star (pole μ a w)^2*pole μ b w)):=
    (actual_scalar_causal_triple_integrable μ a b hμ).const_mul _
  have hR:Integrable (fun w:ℝ=>(b:ℂ)*(star (pole μ a w)*(pole μ b w)^2)):=
    (right_triple_integrable μ a b hμ).const_mul _
  change (∫w:ℝ,(a:ℂ)*(star (pole μ a w)^2*pole μ b w)+
    (b:ℂ)*(star (pole μ a w)*(pole μ b w)^2))=_
  rw [integral_add hL hR,integral_const_mul,integral_const_mul,
    actual_scalar_causal_triple_integral μ a b hμ,right_triple_integral μ a b hμ]
  field_simp [gap_ne μ a b hμ]
  simp only [gap]
  ring

private def channelVector(m ell:ℕ)(F:Index)(f:QuantumTest)(i:Channel F):QuantumTest :=
  thetaAction m ell (channelTest F (inputCore f) i)
private def channelPair(m ell:ℕ)(F:Index)(f h:QuantumTest)(i j:Channel F):ℂ :=
  sourcePair (channelVector m ell F f i) (channelVector m ell F h j)
private def causalValue(advanced:Bool)(F:Index)(i:Channel F):ℝ :=
  ActualCausalBulkTime.direction advanced*channelValue F i
private def compressionFrequency(advanced:Bool)(m ell:ℕ)(F:Index)(μ:ℝ)(f h:QuantumTest)(w:ℝ):ℂ :=
  ∑i,∑j,compressionKernel μ (causalValue advanced F i)
    (causalValue advanced F j) w*channelPair m ell F f h i j
private theorem channel_compression(F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest):
    (resolventCore F z hz*compressionCore F*resolventCore F z hz) f=
      ∑i:Channel F,((channelValue F i:ℂ)*(((channelValue F i:ℂ)-z)⁻¹)^2) •
        channelTest F (inputCore f) i := by
  simp only [Module.End.mul_apply]
  rw [(paid_fixed_channel% core_channels) F z hz f]
  simp only [map_sum,map_smul,actual_channel_eigen,
    paid_fixed_channel% resolvent_channel,smul_smul,pow_two]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring
private theorem finite_pair {ι:Type*}[Fintype ι](c d:ι → QuantumTest)(a b:ι → ℂ):
    sourcePair (∑i,a i • c i) (∑j,b j • d j)=
      ∑i,∑j,star (a i)*b j*sourcePair (c i) (d j) := by
  simp only [sourcePair,map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,
    inner_smul_right,starRingEnd_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  ring
private theorem reflected_pair_scalar(μ a b w:ℝ)(p:ℂ):
    star ((a:ℂ)*(((a:ℂ)-line (-μ) w)⁻¹)^2)*(((b:ℂ)-line (-μ) w)⁻¹)*p+
      star (((a:ℂ)-line (-μ) w)⁻¹)*((b:ℂ)*(((b:ℂ)-line (-μ) w)⁻¹)^2)*p=
        compressionKernel μ (-a) (-b) (-w)*p := by
  have hi:((a:ℂ)-line (-μ) w)⁻¹= -pole μ (-a) (-w):=(paid_fixed_bulk% pole_reflect) μ a w
  have hj:((b:ℂ)-line (-μ) w)⁻¹= -pole μ (-b) (-w):=(paid_fixed_bulk% pole_reflect) μ b w
  rw [hi,hj]
  simp only [compressionKernel,star_mul,star_pow,star_neg,Complex.star_def,Complex.conj_ofReal]
  push_cast
  ring
private theorem compression_frequency_return(advanced:Bool)(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0 < μ)
    (f h:QuantumTest)(w:ℝ):
    compressionContact m ell F (causalFrequency advanced μ w)
      ((paid_fixed_contact% causal_nonreal) advanced μ hμ w) f h=
      compressionFrequency advanced m ell F μ f h (ActualCausalBulkTime.direction advanced*w) := by
  unfold compressionContact
  dsimp only
  rw [channel_compression,channel_compression]
  simp only [coreWindow,Module.End.mul_apply,
    paid_fixed_channel% core_channels,map_sum,map_smul]
  rw [finite_pair,finite_pair]
  unfold compressionFrequency
  simp only [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  cases advanced
  · simp only [compressionKernel,channelPair,channelVector,
      causalValue,ActualCausalBulkTime.direction,Bool.false_eq_true,ite_false,one_mul,
      causalFrequency,pole,star_mul,star_pow,Complex.star_def,Complex.conj_ofReal]
    ring
  · simpa only [causalValue,ActualCausalBulkTime.direction,ite_true,neg_one_mul,
      causalFrequency,channelPair,channelVector] using
      reflected_pair_scalar μ (channelValue F i) (channelValue F j) w
        (sourcePair (thetaAction m ell (channelTest F (inputCore f) i))
          (thetaAction m ell (channelTest F (inputCore h) j)))


private theorem complex_integral_bound(v:ℝ → ℂ)(hv:Continuous v)(b:ℝ)(hb:0 ≤ b)
    (hp:(∫⁻w:ℝ,ENNReal.ofReal ‖v w‖) ≤ ENNReal.ofReal b):
    Integrable v ∧ ‖∫w:ℝ,v w‖ ≤ b := by
  have hf:HasFiniteIntegral v := by
    rw [hasFiniteIntegral_iff_norm]
    exact lt_of_le_of_lt hp ENNReal.ofReal_lt_top
  have hi:Integrable v:=⟨hv.aestronglyMeasurable,hf⟩
  have he:=ofReal_integral_eq_lintegral_ofReal hi.norm
    (Eventually.of_forall (fun _=>norm_nonneg _))
  have hb':(∫w:ℝ,‖v w‖) ≤ b:=by
    rw [←he] at hp
    exact (ENNReal.ofReal_le_ofReal_iff hb).mp hp
  exact ⟨hi,(norm_integral_le_integral_norm v).trans hb'⟩
private theorem window_pair_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest):
    sourcePair (coreWindow m ell F z hz f) (coreWindow m ell F z hz h)=
      (paid_fixed_contact% windowPair) m ell F z f h := by
  unfold sourcePair
  change inner ℂ (embed (coreWindow m ell F z hz f)) (embed (coreWindow m ell F z hz h))=
    inner ℂ (window m ell F z f) (window m ell F z h)
  simp only [coreWindow,Module.End.mul_apply]
  rw [(paid_mixed_core% window_core) m ell F z hz f,(paid_mixed_core% window_core) m ell F z hz h]
private theorem window_pair_continuous(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)(f h:QuantumTest):
    Continuous (fun w:ℝ=>(paid_fixed_contact% windowPair) m ell F (causalFrequency advanced μ w) f h) :=
  ((paid_fixed_contact% window_continuous) advanced μ hμ m ell F f).inner (𝕜:=ℂ)
    ((paid_fixed_contact% window_continuous) advanced μ hμ m ell F h)

/-- The actual skew generator pays its two fixed-source contacts and both
ordered affine terms with one cutoff index before either causal line. -/
theorem actual_generator_fixed_contact_tail(μ:ℝ)(hμ:0 < μ)(f h:QuantumTest):
    ∀ ε:ℝ,0 < ε → ∃ N:ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index),∀ advanced:Bool,
        Integrable (fun w:ℝ=>generatorContact m ell F (causalFrequency advanced μ w)
          ((paid_fixed_contact% causal_nonreal) advanced μ hμ w) f h) ∧
        ‖∫w:ℝ,generatorContact m ell F (causalFrequency advanced μ w)
          ((paid_fixed_contact% causal_nonreal) advanced μ hμ w) f h‖ ≤ ε := by
  intro ε hε
  obtain ⟨N₁,h₁⟩:=(paid_fixed_contact% window_pair_tail) μ hμ (balancedGenerator f) h (ε/8) (by positivity)
  obtain ⟨N₂,h₂⟩:=(paid_fixed_contact% window_pair_tail) μ hμ f (balancedGenerator h) (ε/8) (by positivity)
  obtain ⟨N₃,h₃⟩:=(paid_fixed_contact% contact_pair_tail) μ hμ h f (ε/8) (by positivity)
  obtain ⟨N₄,h₄⟩:=(paid_fixed_contact% contact_pair_tail) μ hμ f h (ε/8) (by positivity)
  refine ⟨max (max N₁ N₂) (max N₃ N₄),fun m hm ell hml=>?_⟩
  filter_upwards [h₁ m (by omega) ell hml,h₂ m (by omega) ell hml,
    h₃ m (by omega) ell hml,h₄ m (by omega) ell hml] with F hF₁ hF₂ hF₃ hF₄
  intro advanced
  obtain ⟨hi₁,hp₁⟩:=complex_integral_bound _ (window_pair_continuous advanced μ hμ m ell F _ _)
    (ε/8) (by positivity) (hF₁ advanced)
  obtain ⟨hi₂,hp₂⟩:=complex_integral_bound _ (window_pair_continuous advanced μ hμ m ell F _ _)
    (ε/8) (by positivity) (hF₂ advanced)
  obtain ⟨hi₃,hp₃⟩:=complex_integral_bound _
    ((paid_fixed_contact% contact_pair_continuous) advanced μ hμ m ell F h f)
    (ε/8) (by positivity) (hF₃ advanced)
  obtain ⟨hi₄,hp₄⟩:=complex_integral_bound _
    ((paid_fixed_contact% contact_pair_continuous) advanced μ hμ m ell F f h)
    (ε/8) (by positivity) (hF₄ advanced)
  let v₁:ℝ → ℂ:=fun w=>(paid_fixed_contact% windowPair) m ell F (causalFrequency advanced μ w) (balancedGenerator f) h
  let v₂:ℝ → ℂ:=fun w=>(paid_fixed_contact% windowPair) m ell F (causalFrequency advanced μ w) f (balancedGenerator h)
  let v₃:ℝ → ℂ:=fun w=>star ((paid_fixed_contact% contactPair) m ell F (causalFrequency advanced μ w)
    ((paid_fixed_contact% causal_nonreal) advanced μ hμ w) h f)
  let v₄:ℝ → ℂ:=fun w=>(paid_fixed_contact% contactPair) m ell F (causalFrequency advanced μ w)
    ((paid_fixed_contact% causal_nonreal) advanced μ hμ w) f h
  have hi₃':Integrable v₃:=
    (RCLike.conjLIE (K:=ℂ)).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hi₃
  have hp₃':‖∫w:ℝ,v₃ w‖ ≤ ε/8:=by
    have hs:(∫w:ℝ,v₃ w)=star (∫w:ℝ,(paid_fixed_contact% contactPair) m ell F
      (causalFrequency advanced μ w) ((paid_fixed_contact% causal_nonreal) advanced μ hμ w) h f):=by
      simpa only [v₃,starRingEnd_apply] using (integral_conj (f:=fun w:ℝ=>(paid_fixed_contact% contactPair)
        m ell F (causalFrequency advanced μ w) ((paid_fixed_contact% causal_nonreal) advanced μ hμ w) h f))
    rw [hs,norm_star]
    exact hp₃
  have he(w:ℝ):generatorContact m ell F (causalFrequency advanced μ w)
      ((paid_fixed_contact% causal_nonreal) advanced μ hμ w) f h=
        v₁ w+v₂ w+(3:ℂ)*v₃ w+(3:ℂ)*v₄ w := by
    rw [actual_generator_fixed_contact,window_pair_return,window_pair_return]
    dsimp only [v₁,v₂,v₃,v₄]
    change _= _+_+(3:ℂ)*star (sourcePair (coreWindow m ell F _ _ h) (affineCutoff m ell (resolventCore F _ _ f)))+_
    have hc:star (sourcePair (coreWindow m ell F (causalFrequency advanced μ w) ((paid_fixed_contact% causal_nonreal) advanced μ hμ w) h)
        (affineCutoff m ell (resolventCore F (causalFrequency advanced μ w) ((paid_fixed_contact% causal_nonreal) advanced μ hμ w) f)))=
      sourcePair (affineCutoff m ell (resolventCore F (causalFrequency advanced μ w) ((paid_fixed_contact% causal_nonreal) advanced μ hμ w) f))
        (coreWindow m ell F (causalFrequency advanced μ w) ((paid_fixed_contact% causal_nonreal) advanced μ hμ w) h):=by
      simpa only [starRingEnd_apply] using GaussNativeForm.pair_conjugate
        (coreWindow m ell F (causalFrequency advanced μ w) ((paid_fixed_contact% causal_nonreal) advanced μ hμ w) h)
        (affineCutoff m ell (resolventCore F (causalFrequency advanced μ w) ((paid_fixed_contact% causal_nonreal) advanced μ hμ w) f))
    rw [hc]
    rfl
  have hi:Integrable (fun w:ℝ=>v₁ w+v₂ w+(3:ℂ)*v₃ w+(3:ℂ)*v₄ w):=
    ((hi₁.add hi₂).add (hi₃'.const_mul _)).add (hi₄.const_mul _)
  refine ⟨hi.congr (Eventually.of_forall (fun w=>(he w).symm)),?_⟩
  simp_rw [he]
  have i12:Integrable (fun w:ℝ=>v₁ w+v₂ w):=hi₁.add hi₂
  have i3:Integrable (fun w:ℝ=>(3:ℂ)*v₃ w):=hi₃'.const_mul _
  have i4:Integrable (fun w:ℝ=>(3:ℂ)*v₄ w):=hi₄.const_mul _
  have i123:Integrable (fun w:ℝ=>v₁ w+v₂ w+(3:ℂ)*v₃ w):=i12.add i3
  have e12:(∫w:ℝ,v₁ w+v₂ w)=(∫w:ℝ,v₁ w)+(∫w:ℝ,v₂ w):=integral_add hi₁ hi₂
  have e123:(∫w:ℝ,v₁ w+v₂ w+(3:ℂ)*v₃ w)=
      (∫w:ℝ,v₁ w+v₂ w)+(∫w:ℝ,(3:ℂ)*v₃ w):=integral_add i12 i3
  have e1234:(∫w:ℝ,v₁ w+v₂ w+(3:ℂ)*v₃ w+(3:ℂ)*v₄ w)=
      (∫w:ℝ,v₁ w+v₂ w+(3:ℂ)*v₃ w)+(∫w:ℝ,(3:ℂ)*v₄ w):=integral_add i123 i4
  rw [e1234,e123,e12,integral_const_mul,integral_const_mul]
  calc
    _ ≤ ‖∫w:ℝ,v₁ w‖+‖∫w:ℝ,v₂ w‖+
      3*‖∫w:ℝ,v₃ w‖+3*‖∫w:ℝ,v₄ w‖ := by
      calc
        _ ≤ ‖(∫w:ℝ,v₁ w)+(∫w:ℝ,v₂ w)+(3:ℂ)*(∫w:ℝ,v₃ w)‖+
          ‖(3:ℂ)*(∫w:ℝ,v₄ w)‖:=norm_add_le _ _
        _ ≤ (‖(∫w:ℝ,v₁ w)+(∫w:ℝ,v₂ w)‖+‖(3:ℂ)*(∫w:ℝ,v₃ w)‖)+
          ‖(3:ℂ)*(∫w:ℝ,v₄ w)‖:=add_le_add (norm_add_le _ _) (le_refl _)
        _ ≤ (‖∫w:ℝ,v₁ w‖+‖∫w:ℝ,v₂ w‖)+‖(3:ℂ)*(∫w:ℝ,v₃ w)‖+
          ‖(3:ℂ)*(∫w:ℝ,v₄ w)‖:=
            add_le_add (add_le_add (norm_add_le _ _) (le_refl _)) (le_refl _)
        _= _:=by simp only [norm_mul,Complex.norm_ofNat]
    _ ≤ ε:=by dsimp only [v₁,v₂] at hp₁ hp₂ ⊢;linarith only [hp₁,hp₂,hp₃',hp₄]

private theorem decay_moment(z:ℂ)(hz:0 < z.re):
    IntegrableOn (fun t:ℝ=>(t:ℂ)*Complex.exp (-z*(t:ℂ))) (Set.Ioi 0) ∧
      (∫t:ℝ in Set.Ioi 0,(t:ℂ)*Complex.exp (-z*(t:ℂ)))=(z⁻¹)^2 := by
  have hneg:-(z.re/2) < 0:=by linarith
  have hbase:IntegrableOn (fun t:ℝ=>(2/z.re)*Real.exp (-(z.re/2)*t)) (Set.Ioi 0):=
    (integrableOn_exp_mul_Ioi hneg 0).const_mul _
  have hm:IntegrableOn (fun t:ℝ=>(t:ℂ)*Complex.exp (-z*(t:ℂ))) (Set.Ioi 0) := by
    apply hbase.mono' (((Complex.continuous_ofReal).mul ((continuous_const.mul Complex.continuous_ofReal).cexp)).aestronglyMeasurable)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have hn:0 ≤ t:=ht.le
    change ‖(t:ℂ)*Complex.exp (-z*(t:ℂ))‖  ≤  _
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn,
      Complex.norm_exp,Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    have hb: z.re/2*t  ≤  Real.exp (z.re/2*t) := by
      have h:=Real.add_one_le_exp (z.re/2*t)
      linarith only [h]
    have hb':t  ≤  (2/z.re)*Real.exp (z.re/2*t):=by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hz).mpr
      nlinarith only [hb]
    calc
      t*Real.exp (-z.re*t)  ≤  ((2/z.re)*Real.exp (z.re/2*t))*Real.exp (-z.re*t):=
        mul_le_mul_of_nonneg_right hb' (Real.exp_pos _).le
      _=(2/z.re)*Real.exp (-(z.re/2)*t):=by rw [mul_assoc,←Real.exp_add];congr 2;ring
  let primitive:ℝ → ℂ:=fun t=>-((t:ℂ)*z⁻¹+(z⁻¹)^2)*Complex.exp (-z*(t:ℂ))
  have zn:z≠0:=by intro h;simp [h] at hz
  have hd(t:ℝ):HasDerivAt primitive ((t:ℂ)*Complex.exp (-z*(t:ℂ))) t := by
    have hp:=(((((hasDerivAt_id t).ofReal_comp).mul_const z⁻¹).add_const ((z⁻¹)^2)).neg).mul
      ((((hasDerivAt_id t).ofReal_comp).const_mul (-z)).cexp)
    convert! hp using 1
    simp only [Complex.ofReal_one,id_eq,Pi.neg_apply]
    field_simp [zn]
    ring
  have ht: Tendsto (fun t:ℝ=>(t:ℂ)*Complex.exp (-z*(t:ℂ))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h: Tendsto (fun t:ℝ=>t*Real.exp (-z.re*t)) atTop (𝓝 0) := by
      have ha: Tendsto (fun t:ℝ=>z.re*t) atTop atTop:=Tendsto.const_mul_atTop hz tendsto_id
      have hp:=(Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp ha
      have hh:=hp.const_mul z.re⁻¹
      convert hh using 1
      · funext t;simp only [Function.comp_apply,pow_one];field_simp [hz.ne']
      · simp
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht,
      Complex.norm_exp,Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  have he:Tendsto (fun t:ℝ=>Complex.exp (-z*(t:ℂ))) atTop (𝓝 0) := by
    simp only [Complex.tendsto_exp_nhds_zero_iff]
    simpa only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,id_eq]
      using tendsto_const_nhds.neg_mul_atTop (neg_lt_zero.mpr hz) tendsto_id
  have hlim:Tendsto primitive atTop (𝓝 0) := by
    have h:=((ht.const_mul (-z⁻¹)).add (he.const_mul (-(z⁻¹)^2)))
    convert h using 1
    · funext t;dsimp only [primitive];ring
    · simp
  have hi:=integral_Ioi_of_hasDerivAt_of_tendsto' (fun t (_:t∈Set.Ici 0)=>hd t) hm hlim
  refine ⟨hm,?_⟩
  simpa only [primitive,Complex.ofReal_zero,zero_mul,zero_add,mul_zero,Complex.exp_zero,mul_one,sub_neg_eq_add,zero_add] using hi

private def compressionTime(advanced:Bool)(m ell:ℕ)(F:Index)(μ:ℝ)(f h:QuantumTest)(t:ℝ):ℂ :=
  ∑i,∑j,((1:ℂ)-(2*μ:ℂ)*(t:ℂ))*
    Complex.exp (-gap μ (causalValue advanced F i) (causalValue advanced F j)*(t:ℂ))*
      channelPair m ell F f h i j
private theorem gap_moment(μ a b:ℝ)(hμ:0 < μ):
    IntegrableOn (fun t:ℝ=>((1:ℂ)-(2*μ:ℂ)*(t:ℂ))*Complex.exp (-gap μ a b*(t:ℂ))) (Set.Ioi 0) ∧
      (∫t:ℝ in Set.Ioi 0,((1:ℂ)-(2*μ:ℂ)*(t:ℂ))*Complex.exp (-gap μ a b*(t:ℂ)))=
        (gap μ a b)⁻¹-(2*μ:ℂ)*(gap μ a b)⁻¹^2 := by
  have hr:(gap μ a b).re=2*μ:=by simp [gap]
  obtain ⟨hm,he⟩:=decay_moment (gap μ a b) (by rw [hr];positivity)
  have hb:IntegrableOn (fun t:ℝ=>Complex.exp (-gap μ a b*(t:ℂ))) (Set.Ioi 0):=
    (paid_fixed_bulk% decay_integrable) μ a b hμ
  have hv(t:ℝ):((1:ℂ)-(2*μ:ℂ)*(t:ℂ))*Complex.exp (-gap μ a b*(t:ℂ))=
      Complex.exp (-gap μ a b*(t:ℂ))-(2*μ:ℂ)*((t:ℂ)*Complex.exp (-gap μ a b*(t:ℂ))) := by ring
  refine ⟨(hb.sub (hm.const_mul _)).congr (Eventually.of_forall (fun t=>(hv t).symm)),?_⟩
  simp_rw [hv]
  rw [integral_sub hb (hm.const_mul _),integral_const_mul,he,
    (paid_fixed_bulk% decay_integral) μ a b hμ]
private theorem compression_time_integrable(advanced:Bool)(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0 < μ)(f h:QuantumTest):
    IntegrableOn (compressionTime advanced m ell F μ f h) (Set.Ioi 0) :=
  integrable_finsetSum _ (fun _i _=>integrable_finsetSum _ (fun _j _=>
    ((gap_moment μ _ _ hμ).1).mul_const _))
private theorem compression_frequency_integrable(advanced:Bool)(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0 < μ)(f h:QuantumTest):
    Integrable (compressionFrequency advanced m ell F μ f h) :=
  integrable_finsetSum _ (fun _i _=>integrable_finsetSum _ (fun _j _=>
    (compression_kernel_integrable μ _ _ hμ).mul_const _))
private theorem compression_frequency_time(advanced:Bool)(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0 < μ)(f h:QuantumTest):
    (∫w:ℝ,compressionFrequency advanced m ell F μ f h w)=
      (2*Real.pi:ℂ)*(∫t:ℝ in Set.Ioi 0,compressionTime advanced m ell F μ f h t) := by
  unfold compressionFrequency compressionTime
  rw [integral_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>
      (compression_kernel_integrable μ _ _ hμ).mul_const _)),
    integral_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>
      ((gap_moment μ _ _ hμ).1).mul_const _)),Finset.mul_sum]
  apply Finset.sum_congr rfl;intro i _
  rw [integral_finsetSum _ (fun j _=>(compression_kernel_integrable μ _ _ hμ).mul_const _),
    integral_finsetSum _ (fun j _=>((gap_moment μ _ _ hμ).1).mul_const _),Finset.mul_sum]
  apply Finset.sum_congr rfl;intro j _
  rw [integral_mul_const,integral_mul_const,compression_kernel_integral μ _ _ hμ,(gap_moment μ _ _ hμ).2]
  ring
private theorem compression_time_return(advanced:Bool)(m ell:ℕ)(F:Index)(μ:ℝ)(f h:QuantumTest)(t:ℝ):
    compressionTime advanced m ell F μ f h t=
      ((1-2*μ*t)*Real.exp (-2*μ*t):ℂ)*sourcePair
        (thetaAction m ell (causalCoreTime advanced F (inputCore f) t))
        (thetaAction m ell (causalCoreTime advanced F (inputCore h) t)) := by
  unfold compressionTime
  simp_rw [(paid_fixed_bulk% time_factor)]
  rw [(paid_fixed_bulk% core_channels) advanced F (inputCore f) t,
    (paid_fixed_bulk% core_channels) advanced F (inputCore h) t]
  simp only [map_sum,map_smul]
  rw [finite_pair]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  change _= _* (star (phase (causalValue advanced F i) t)*
    phase (causalValue advanced F j) t*channelPair m ell F f h i j)
  push_cast
  ring

/-- The complete CF contact is an exact signed time moment; every original
finite channel and its escape channel is included before integration. -/
theorem actual_compression_fixed_contact_integral(advanced:Bool)(m ell:ℕ)(F:Index)
    (μ:ℝ)(hμ:0 < μ)(f h:QuantumTest):
    Integrable (fun w:ℝ=>compressionContact m ell F (causalFrequency advanced μ w)
      ((paid_fixed_contact% causal_nonreal) advanced μ hμ w) f h) ∧
    IntegrableOn (fun t:ℝ=>((1-2*μ*t)*Real.exp (-2*μ*t):ℂ)*sourcePair
      (thetaAction m ell (causalCoreTime advanced F (inputCore f) t))
      (thetaAction m ell (causalCoreTime advanced F (inputCore h) t))) (Set.Ioi 0) ∧
    (∫w:ℝ,compressionContact m ell F (causalFrequency advanced μ w)
      ((paid_fixed_contact% causal_nonreal) advanced μ hμ w) f h)=
      (2*Real.pi:ℂ)*(∫t:ℝ in Set.Ioi 0,((1-2*μ*t)*Real.exp (-2*μ*t):ℂ)*sourcePair
        (thetaAction m ell (causalCoreTime advanced F (inputCore f) t))
        (thetaAction m ell (causalCoreTime advanced F (inputCore h) t))) := by
  have hfi:=compression_frequency_integrable advanced m ell F μ hμ f h
  have hf:Integrable (fun w:ℝ=>compressionFrequency advanced m ell F μ f h (ActualCausalBulkTime.direction advanced*w)):=by
    cases advanced
    · simpa only [ActualCausalBulkTime.direction,Bool.false_eq_true,ite_false,one_mul] using hfi
    · simpa only [ActualCausalBulkTime.direction,ite_true,neg_one_mul] using hfi.comp_neg
  have he:(∫w:ℝ,compressionFrequency advanced m ell F μ f h (ActualCausalBulkTime.direction advanced*w))=
      ∫w:ℝ,compressionFrequency advanced m ell F μ f h w := by
    cases advanced
    · simp only [ActualCausalBulkTime.direction,Bool.false_eq_true,ite_false,one_mul]
    · simpa only [ActualCausalBulkTime.direction,ite_true,neg_one_mul] using
        integral_neg_eq_self (compressionFrequency true m ell F μ f h) volume
  refine ⟨hf.congr (Eventually.of_forall (fun w=>(compression_frequency_return advanced m ell F μ hμ f h w).symm)),
    (compression_time_integrable advanced m ell F μ hμ f h).congr
      (Eventually.of_forall (compression_time_return advanced m ell F μ f h)),?_⟩
  rw [integral_congr_ae (Eventually.of_forall (compression_frequency_return advanced m ell F μ hμ f h)),
    he,compression_frequency_time advanced m ell F μ hμ]
  congr 1
  exact integral_congr_ae (Eventually.of_forall (compression_time_return advanced m ell F μ f h))

private theorem time_weight_bound(μ t:ℝ)(hμ:0 < μ)(ht:0 ≤ t):
    |1-2*μ*t| *Real.exp (-2*μ*t) ≤ 2*Real.exp (-μ*t) := by
  have hx:0 ≤ μ*t:=mul_nonneg hμ.le ht
  have h1:|1-2*μ*t| ≤ 1+2*μ*t:=by
    calc
      _ ≤ |(1:ℝ)| + |2*μ*t|:=abs_sub _ _
      _= _:=by rw [abs_one,abs_of_nonneg (by positivity)]
  have h2:1+2*μ*t ≤ 2*Real.exp (μ*t):=by
    have he:=Real.add_one_le_exp (μ*t)
    linarith only [he]
  calc
    _ ≤ (2*Real.exp (μ*t))*Real.exp (-2*μ*t):=
      mul_le_mul_of_nonneg_right (h1.trans h2) (Real.exp_pos _).le
    _=2*Real.exp (-μ*t):=by rw [mul_assoc,←Real.exp_add];congr 2;ring
private theorem pair_norm_price(f h:QuantumTest):‖sourcePair f h‖ ≤ ‖embed f‖^2+‖embed h‖^2 := by
  unfold sourcePair
  change ‖inner ℂ (embed f) (embed h)‖ ≤ _
  have hp:=norm_inner_le_norm (𝕜:=ℂ) (embed f) (embed h)
  nlinarith only [hp,sq_nonneg (‖embed f‖-‖embed h‖)]
private theorem compression_integral_price(advanced:Bool)(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0 < μ)(f h:QuantumTest):
    ‖∫w:ℝ,compressionContact m ell F (causalFrequency advanced μ w)
      ((paid_fixed_contact% causal_nonreal) advanced μ hμ w) f h‖ ≤
    2*((∫w:ℝ,‖embed (coreWindow m ell F (causalFrequency advanced (μ/2) w)
      ((paid_fixed_contact% causal_nonreal) advanced (μ/2) (by positivity) w) f)‖^2)+
      (∫w:ℝ,‖embed (coreWindow m ell F (causalFrequency advanced (μ/2) w)
      ((paid_fixed_contact% causal_nonreal) advanced (μ/2) (by positivity) w) h)‖^2)) := by
  obtain ⟨_,ht,he⟩:=actual_compression_fixed_contact_integral advanced m ell F μ hμ f h
  obtain ⟨_,hft,hfe⟩:=actual_causal_norm_parseval advanced F (μ/2) (by positivity)
    (thetaAction m ell) (inputCore f)
  obtain ⟨_,hht,hhe⟩:=actual_causal_norm_parseval advanced F (μ/2) (by positivity)
    (thetaAction m ell) (inputCore h)
  let ef:ℝ → ℝ:=fun t=>Real.exp (-μ*t)*‖embed (thetaAction m ell (causalCoreTime advanced F (inputCore f) t))‖^2
  let eh:ℝ → ℝ:=fun t=>Real.exp (-μ*t)*‖embed (thetaAction m ell (causalCoreTime advanced F (inputCore h) t))‖^2
  have hef:IntegrableOn ef (Set.Ioi 0):=by
    convert hft using 1;funext t;dsimp only [ef];congr 2;ring
  have heh:IntegrableOn eh (Set.Ioi 0):=by
    convert hht using 1;funext t;dsimp only [eh];congr 2;ring
  have hp:(∫t:ℝ in Set.Ioi 0,‖((1-2*μ*t)*Real.exp (-2*μ*t):ℂ)*sourcePair
      (thetaAction m ell (causalCoreTime advanced F (inputCore f) t))
      (thetaAction m ell (causalCoreTime advanced F (inputCore h) t))‖) ≤
        2*((∫t:ℝ in Set.Ioi 0,ef t)+(∫t:ℝ in Set.Ioi 0,eh t)) := by
    calc
      _ ≤ ∫t:ℝ in Set.Ioi 0,2*(ef t+eh t) := by
        apply integral_mono_ae ht.norm ((hef.add heh).const_mul 2)
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        rw [norm_mul]
        have hcast:((1:ℂ)-(2*μ:ℂ)*(t:ℂ))*(Real.exp (-2*μ*t):ℂ)=
          (((1-2*μ*t)*Real.exp (-2*μ*t):ℝ):ℂ):=by push_cast;ring
        rw [hcast,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
        have hweight:=time_weight_bound μ t hμ ht.le
        have hpair:=pair_norm_price (thetaAction m ell (causalCoreTime advanced F (inputCore f) t))
          (thetaAction m ell (causalCoreTime advanced F (inputCore h) t))
        have hb:=mul_le_mul hweight hpair (norm_nonneg _) (by positivity : 0 ≤ 2*Real.exp (-μ*t))
        exact hb.trans_eq (by dsimp only [ef,eh,Pi.add_apply];ring)
      _= _:=by rw [integral_const_mul,integral_add hef heh]
  have hfe':(∫w:ℝ,‖embed (coreWindow m ell F (causalFrequency advanced (μ/2) w)
      ((paid_fixed_contact% causal_nonreal) advanced (μ/2) (by positivity) w) f)‖^2)=
        2*Real.pi*(∫t:ℝ in Set.Ioi 0,ef t) := by
    convert hfe using 1
    · apply integral_congr_ae
      exact Eventually.of_forall (fun w=>by simp only [coreWindow,Module.End.mul_apply,resolventCore,state];rfl)
    · unfold causalNormTime;congr 1;apply integral_congr_ae
      exact Eventually.of_forall (fun t=>by dsimp only [ef];congr 2;ring)
  have hhe':(∫w:ℝ,‖embed (coreWindow m ell F (causalFrequency advanced (μ/2) w)
      ((paid_fixed_contact% causal_nonreal) advanced (μ/2) (by positivity) w) h)‖^2)=
        2*Real.pi*(∫t:ℝ in Set.Ioi 0,eh t) := by
    convert hhe using 1
    · apply integral_congr_ae
      exact Eventually.of_forall (fun w=>by simp only [coreWindow,Module.End.mul_apply,resolventCore,state];rfl)
    · unfold causalNormTime;congr 1;apply integral_congr_ae
      exact Eventually.of_forall (fun t=>by dsimp only [eh];congr 2;ring)
  rw [he,norm_mul,show ‖(2*Real.pi:ℂ)‖=2*Real.pi by
    rw [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos],hfe',hhe']
  exact ((mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
    (by positivity : 0 ≤ 2*Real.pi)).trans
    (mul_le_mul_of_nonneg_left hp (by positivity))).trans_eq (by ring)

/-- The actual frequency derivative is paid only after its ordered CF terms
are combined. The common cutoff index is generated at half the same source damping. -/
theorem actual_compression_fixed_contact_tail(μ:ℝ)(hμ:0 < μ)(f h:QuantumTest):
    ∀ ε:ℝ,0 < ε → ∃ N:ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index),∀ advanced:Bool,
        Integrable (fun w:ℝ=>compressionContact m ell F (causalFrequency advanced μ w)
          ((paid_fixed_contact% causal_nonreal) advanced μ hμ w) f h) ∧
        ‖∫w:ℝ,compressionContact m ell F (causalFrequency advanced μ w)
          ((paid_fixed_contact% causal_nonreal) advanced μ hμ w) f h‖ ≤ ε := by
  intro ε hε
  obtain ⟨Nf,hf⟩:=actual_theta_frequency_norm_tail (μ/2) (by positivity) (inputCore f) (ε/4) (by positivity)
  obtain ⟨Nh,hh⟩:=actual_theta_frequency_norm_tail (μ/2) (by positivity) (inputCore h) (ε/4) (by positivity)
  refine ⟨max Nf Nh,fun m hm ell hml=>?_⟩
  filter_upwards [hf m (by omega) ell hml,hh m (by omega) ell hml] with F hFf hFh
  intro advanced
  refine ⟨(actual_compression_fixed_contact_integral advanced m ell F μ hμ f h).1,?_⟩
  have hp:=compression_integral_price advanced m ell F μ hμ f h
  have hpf:(∫w:ℝ,‖embed (coreWindow m ell F (causalFrequency advanced (μ/2) w)
      ((paid_fixed_contact% causal_nonreal) advanced (μ/2) (by positivity) w) f)‖^2) ≤ ε/4:=by
    simpa only [coreWindow,Module.End.mul_apply,resolventCore,state,
      SourceScalarInverseRetardedBudget.theta,LinearMap.coe_mk,AddHom.coe_mk,inputCore] using hFf advanced
  have hph:(∫w:ℝ,‖embed (coreWindow m ell F (causalFrequency advanced (μ/2) w)
      ((paid_fixed_contact% causal_nonreal) advanced (μ/2) (by positivity) w) h)‖^2) ≤ ε/4:=by
    simpa only [coreWindow,Module.End.mul_apply,resolventCore,state,
      SourceScalarInverseRetardedBudget.theta,LinearMap.coe_mk,AddHom.coe_mk,inputCore] using hFh advanced
  linarith only [hp,hpf,hph]

private theorem source_damping_pos:0 < sourceMu :=
  lt_of_lt_of_le zero_lt_one source_mu_large

/-- The complete fixed BF contact now has an internally generated ordinary
complex integral and a common signed-integral tail on both physical causal lines. -/
theorem actual_fixed_balanced_contact_tail(g:QuantumTest):
    ∀ ε:ℝ,0 < ε → ∃ N:ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index),∀ advanced:Bool,
        Integrable (fun w:ℝ=>fixedBalancedContact m ell F (causalFrequency advanced sourceMu w)
          ((paid_fixed_contact% causal_nonreal) advanced sourceMu source_damping_pos w) g) ∧
        ‖∫w:ℝ,fixedBalancedContact m ell F (causalFrequency advanced sourceMu w)
          ((paid_fixed_contact% causal_nonreal) advanced sourceMu source_damping_pos w) g‖ ≤ ε := by
  intro ε hε
  obtain ⟨NA,hA⟩:=actual_generator_fixed_contact_tail sourceMu source_damping_pos g (nonmagneticSecondField g)
    (ε/2) (by positivity)
  obtain ⟨NC,hC⟩:=actual_compression_fixed_contact_tail sourceMu source_damping_pos g (nonmagneticSecondField g)
    (ε/36) (by positivity)
  refine ⟨max NA NC,fun m hm ell hml=>?_⟩
  filter_upwards [hA m (by omega) ell hml,hC m (by omega) ell hml] with F hFA hFC
  intro advanced
  obtain ⟨hiA,hpA⟩:=hFA advanced
  obtain ⟨hiC,hpC⟩:=hFC advanced
  have hi:=hiA.sub (hiC.const_mul (18:ℂ))
  refine ⟨hi.congr (Eventually.of_forall (fun w=>(actual_fixed_balanced_contact_source m ell F _ _ g).symm)),?_⟩
  simp_rw [actual_fixed_balanced_contact_source]
  rw [integral_sub hiA (hiC.const_mul _),integral_const_mul]
  have hp:=norm_sub_le (∫w:ℝ,generatorContact m ell F (causalFrequency advanced sourceMu w)
    ((paid_fixed_contact% causal_nonreal) advanced sourceMu source_damping_pos w) g (nonmagneticSecondField g))
    ((18:ℂ)*(∫w:ℝ,compressionContact m ell F (causalFrequency advanced sourceMu w)
      ((paid_fixed_contact% causal_nonreal) advanced sourceMu source_damping_pos w) g (nonmagneticSecondField g)))
  rw [norm_mul,Complex.norm_ofNat] at hp
  linarith only [hp,hpA,hpC]

end LowEnergy.ActualBalancedFixedContactPayment
