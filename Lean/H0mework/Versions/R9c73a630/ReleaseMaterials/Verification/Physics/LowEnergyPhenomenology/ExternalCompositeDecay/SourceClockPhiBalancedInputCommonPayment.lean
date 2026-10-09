import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeGaugeScalarReductionSource
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiCombinedProfileTail
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseScalarGaugeWard
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockYukawaCubicCurrent SourceClockPhiNormalizedScalarBudget SourceClockPhiCombinedScalePressure
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockPhiNativeJointPayment
open SourceLocalizedInverseFormPayment SourceResolventBandLimit SourceClockPhiCombinedProfileTail
open SourceClockPhiRadiusResponseNativeBudget ReverseNativeFrequencyWard ReverseNativeOuterSource
open SourceClockPhiOriginalGaussianH0RealPrimitives SourceScalarDoubleCurrent MeasureTheory Filter
open scoped ContDiff Topology ENNReal
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev G:End:=SourceGaugeScaleTransport.generator
private abbrev S:End:=phiInverseAction
attribute [local irreducible] sourcePair embed coreEquiv phiInverseAction phiThetaAction
private theorem gauge_inverse:Commute G S:=by
  have h:=SourceGaugeScaleTransport.generator_commutator S
  have hz:=gauge_invariant_local S (fun z=>(phiReciprocal z:ℂ) • ContinuousLinearMap.id ℂ FockFiber)
    (by intro f z;unfold S phiInverseAction;rfl) (fun _ _=>rfl)
  rw [hz] at h
  exact sub_eq_zero.mp h
private theorem row_commute(A:End)(h:Commute A S)(m ell:ℕ)(i:Fin 2):Commute A (phaseRow m ell i):=by
  have hQ:A*(1-S)=(1-S)*A:=by
    apply LinearMap.ext
    intro f
    change A (f-S f)=A f-S (A f)
    rw [map_sub]
    exact congrArg (fun q:QuantumTest=>A f-q) (congrArg (fun Q:End=>Q f) h.eq)
  have hp(k:ℕ):A*((1-S)^k)=((1-S)^k)*A:=by
    induction k with
    | zero => simp only [pow_zero,mul_one,one_mul]
    | succ k ih =>
      rw [pow_succ]
      calc
        _=(A*((1-S)^k))*(1-S):=rfl
        _=(((1-S)^k)*A)*(1-S):=by rw [ih]
        _=((1-S)^k)*(A*(1-S)):=rfl
        _=((1-S)^k)*((1-S)*A):=by rw [hQ]
        _=_:=rfl
  have hT:A*phiThetaAction m ell=phiThetaAction m ell*A:=by
    unfold phiThetaAction
    change A*((1-S)^(m+1)-(1-S)^(ell+1))=((1-S)^(m+1)-(1-S)^(ell+1))*A
    apply LinearMap.ext
    intro f
    change A (((1-S)^(m+1)) f-((1-S)^(ell+1)) f)=
      ((1-S)^(m+1)) (A f)-((1-S)^(ell+1)) (A f)
    rw [map_sub]
    exact congrArg₂ (fun u v:QuantumTest=>u-v)
      (congrArg (fun Q:End=>Q f) (hp (m+1)))
      (congrArg (fun Q:End=>Q f) (hp (ell+1)))
  fin_cases i
  · exact hT
  · change A*(-(S*phiThetaAction m ell))=(-(S*phiThetaAction m ell))*A
    apply LinearMap.ext
    intro f
    change A (-(S (phiThetaAction m ell f)))= -(S (phiThetaAction m ell (A f)))
    rw [map_neg]
    apply congrArg Neg.neg
    exact congrArg (fun Q:End=>Q f) (show A*(S*phiThetaAction m ell)=(S*phiThetaAction m ell)*A from by
    calc
      _=(A*S)*phiThetaAction m ell:=rfl
      _=(S*A)*phiThetaAction m ell:=by rw [h.eq]
      _=S*(A*phiThetaAction m ell):=rfl
      _=S*(phiThetaAction m ell*A):=by rw [hT]
      _=_:=rfl)

theorem actual_gauge_phase_row(m ell:ℕ)(i:Fin 2):bracket G (phaseRow m ell i)=0:=
  sub_eq_zero.mpr (row_commute G gauge_inverse m ell i).eq
private theorem gauge_input_response(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    gaugeInputVector m ell F z hz g=
      ∑i:Fin 2,phaseRow m ell i (resolventCore F z hz (G (coreEquiv.symm (inputSeed g i)))):=by
  simp only [gaugeInputVector,actual_gauge_phase_row,LinearMap.zero_apply,zero_add]

def balancedInputSeed(g:diagonal.domain)(i:Fin 2):diagonal.domain:=
  coreEquiv ((ReverseNativeClock.reverseNativeClock-(9:ℂ) • G) (coreEquiv.symm (inputSeed g i)))
/-- The compensated Ward still has precisely the original Phi profile jet and two fixed source-generated input seeds. -/
theorem actual_balanced_input_response(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    balancedInputVector m ell F z hz g=(3:ℂ) • phaseFirst m ell F z hz g+
      ∑i:Fin 2,phaseRow m ell i (resolventCore F z hz (coreEquiv.symm (balancedInputSeed g i))):=by
  unfold balancedInputVector
  rw [gauge_input_response]
  simp only [reverseInputVector,reverseInputSeed,balancedInputSeed,coreEquiv.symm_apply_apply,
    LinearMap.sub_apply,LinearMap.smul_apply,map_sub,map_smul,Finset.sum_sub_distrib,←Finset.smul_sum]
  module
private theorem inverse_norm(f:QuantumTest):‖embed (phiInverseAction f)‖ ≤ ‖embed f‖:=by
  have he:phiInverseBounded (embed f)=embed (phiInverseAction f):=by
    unfold phiInverseAction
    exact GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f
  have hn:‖phiInverseBounded‖ ≤ 1:=GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
  rw [←he]
  exact (phiInverseBounded.le_opNorm _).trans (by nlinarith [norm_nonneg (embed f)])
private theorem norm_add_square(x y:H):‖x+y‖^2 ≤ 2*‖x‖^2+2*‖y‖^2:=by
  have h:=sq_le_sq₀ (norm_nonneg (x+y)) (by positivity:0 ≤ ‖x‖+‖y‖) |>.mpr (norm_add_le x y)
  nlinarith [sq_nonneg (‖x‖-‖y‖)]
private theorem core_state(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    resolventCore F z hz (coreEquiv.symm g)=SourceScalarPositiveBulkWard.state F z hz g:=by
  unfold resolventCore
  simp only [LinearMap.coe_mk,AddHom.coe_mk,coreEquiv.apply_symm_apply]
private def phaseInput(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain)(i:Fin 2):QuantumTest:=
  phiThetaAction m ell (SourceScalarPositiveBulkWard.state F z hz (balancedInputSeed g i))
private theorem input_bound(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    ‖embed (balancedInputVector m ell F z hz g)‖^2 ≤ 36*(
      (‖embed (phaseFirst m ell F z hz g)‖^2+‖embed (phaseSecond m ell F z hz g)‖^2)+
      ‖embed (phaseInput m ell F z hz g 0)‖^2+‖embed (phaseInput m ell F z hz g 1)‖^2):=by
  have he:balancedInputVector m ell F z hz g=(3:ℂ) • phaseFirst m ell F z hz g+
      (phaseInput m ell F z hz g 0-phiInverseAction (phaseInput m ell F z hz g 1)):=by
    rw [actual_balanced_input_response]
    simp only [Fin.sum_univ_two,core_state,phaseRow,Matrix.cons_val_zero,
      Matrix.cons_val_one,LinearMap.neg_apply,Module.End.mul_apply,phaseInput,sub_eq_add_neg]
  rw [he,map_add,map_smul,map_sub]
  have h0:=norm_add_square ((3:ℂ) • embed (phaseFirst m ell F z hz g))
    (embed (phaseInput m ell F z hz g 0)-embed (phiInverseAction (phaseInput m ell F z hz g 1)))
  have h1:=norm_add_square (embed (phaseInput m ell F z hz g 0))
    (-embed (phiInverseAction (phaseInput m ell F z hz g 1)))
  have h2:=sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr (inverse_norm (phaseInput m ell F z hz g 1))
  simp only [norm_smul,norm_neg,←sub_eq_add_neg] at h0 h1
  norm_num only [Complex.norm_ofNat] at h0
  nlinarith [sq_nonneg ‖embed (phaseFirst m ell F z hz g)‖,
    sq_nonneg ‖embed (phaseSecond m ell F z hz g)‖,
    sq_nonneg ‖embed (phaseInput m ell F z hz g 0)‖,
    sq_nonneg ‖embed (phaseInput m ell F z hz g 1)‖]

/-- The actual gauge-compensated scalar Ward input has one original cofinal tail. N is chosen before both profile indices, the cutoff and the causal branch. -/
theorem actual_balanced_input_common_payment(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    ∀ε:ℝ,0<ε→∃N:ℕ,∀m,N ≤ m→∀ell,m ≤ ell→∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
      (∫⁻q:ℝ,ENNReal.ofReal (‖embed (balancedInputVector m ell F (actualFrequency advanced μ q)
        (reverse_frequency_nonreal advanced μ hμ q) g)‖^2)) ≤ ENNReal.ofReal ε:=by
  intro ε hε
  obtain ⟨N0,h0⟩:=actual_combined_profile_common_tail μ hμ g (ε/108) (by positivity)
  obtain ⟨N1,h1⟩:=actual_phi_theta_common_tail μ hμ (balancedInputSeed g 0) (ε/108) (by positivity)
  obtain ⟨N2,h2⟩:=actual_phi_theta_common_tail μ hμ (balancedInputSeed g 1) (ε/108) (by positivity)
  refine ⟨max N0 (max N1 N2),fun m hm ell hml=>?_⟩
  filter_upwards [h0 m (by omega) ell hml,h1 m (by omega) ell hml,h2 m (by omega) ell hml] with F hF0 hF1 hF2
  intro advanced
  let Afun(q:ℝ):ℝ:=‖embed (phaseFirst m ell F (actualFrequency advanced μ q) (reverse_frequency_nonreal advanced μ hμ q) g)‖^2+
    ‖embed (phaseSecond m ell F (actualFrequency advanced μ q) (reverse_frequency_nonreal advanced μ hμ q) g)‖^2
  let Bfun(q:ℝ):ℝ:=‖embed (phaseInput m ell F (actualFrequency advanced μ q) (reverse_frequency_nonreal advanced μ hμ q) g 0)‖^2
  let Cfun(q:ℝ):ℝ:=‖embed (phaseInput m ell F (actualFrequency advanced μ q) (reverse_frequency_nonreal advanced μ hμ q) g 1)‖^2
  have hA:(∫⁻q:ℝ,ENNReal.ofReal (Afun q)) ≤ ENNReal.ofReal (ε/108):=hF0 advanced
  have hB:(∫⁻q:ℝ,ENNReal.ofReal (Bfun q)) ≤ ENNReal.ofReal (ε/108):=hF1 advanced
  have hC:(∫⁻q:ℝ,ENNReal.ofReal (Cfun q)) ≤ ENNReal.ofReal (ε/108):=hF2 advanced
  have hmeas(i:Fin 2):Measurable (fun q:ℝ=>ENNReal.ofReal (‖embed (phaseInput m ell F
      (actualFrequency advanced μ q) (reverse_frequency_nonreal advanced μ hμ q) g i)‖^2)):=by
    have hc:Continuous (fun q:ℝ=>embed (phiThetaAction m ell (resolventCore F
        (actualFrequency advanced μ q) (reverse_frequency_nonreal advanced μ hμ q)
        (coreEquiv.symm (balancedInputSeed g i))))) :=
      continuous_iff_continuousAt.mpr (fun q=>(actual_physical_resolvent_derivative F advanced μ hμ
        (phiThetaAction m ell) (coreEquiv.symm (balancedInputSeed g i)) q).continuousAt)
    simpa only [phaseInput,core_state,Pi.pow_apply] using (hc.norm.pow 2).measurable.ennreal_ofReal
  have hsum:(∫⁻q:ℝ,ENNReal.ofReal (Afun q+Bfun q+Cfun q)) ≤ ENNReal.ofReal (ε/36):=by
    simp_rw [ENNReal.ofReal_add (show 0 ≤ Afun _+Bfun _ by dsimp [Afun,Bfun];positivity) (show 0 ≤ Cfun _ by dsimp [Cfun];positivity),
      ENNReal.ofReal_add (show 0 ≤ Afun _ by dsimp [Afun];positivity) (show 0 ≤ Bfun _ by dsimp [Bfun];positivity)]
    calc
      _ ≤ ((∫⁻q:ℝ,ENNReal.ofReal (Afun q))+(∫⁻q:ℝ,ENNReal.ofReal (Bfun q)))+(∫⁻q:ℝ,ENNReal.ofReal (Cfun q)):=
        by rw [lintegral_add_right _ (hmeas 1),lintegral_add_right _ (hmeas 0)]
      _ ≤ ENNReal.ofReal (ε/108)+ENNReal.ofReal (ε/108)+ENNReal.ofReal (ε/108):=add_le_add (add_le_add hA hB) hC
      _=_:=by rw [←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_add (by positivity) (by positivity)];congr 1;ring
  calc
    _ ≤ ∫⁻q:ℝ,ENNReal.ofReal (36*(Afun q+Bfun q+Cfun q)):=lintegral_mono (fun q=>ENNReal.ofReal_le_ofReal (input_bound m ell F _ _ g))
    _=ENNReal.ofReal 36*(∫⁻q:ℝ,ENNReal.ofReal (Afun q+Bfun q+Cfun q)):=by
      simp_rw [ENNReal.ofReal_mul (by norm_num:0 ≤ (36:ℝ))]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal 36*ENNReal.ofReal (ε/36):=mul_le_mul_of_nonneg_left hsum (show 0 ≤ ENNReal.ofReal 36 from zero_le)
    _=ENNReal.ofReal ε:=by rw [←ENNReal.ofReal_mul (by norm_num:0 ≤ (36:ℝ))];congr 1;ring
end LowEnergy.ReverseScalarGaugeWard
