import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiReversePhaseSource
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiCombinedProfileTail
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseNativeOuterSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceClockYukawaCubicCurrent SourceClockPhiNormalizedScalarBudget
open SourceClockPhiCombinedScalePressure SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff
open SourceClockPhiNativeJointPayment SourceLocalizedInverseFormPayment SourceResolventBandLimit
open SourceClockPhiCombinedProfileTail SourceClockPhiRadiusResponseNativeBudget ReverseNativeFrequencyWard
open MeasureTheory Filter
open scoped Topology ENNReal
attribute [local irreducible] embed sourcePair coreEquiv phiInverseAction phiThetaAction
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
  phiThetaAction m ell (SourceScalarPositiveBulkWard.state F z hz (reverseInputSeed g i))
private theorem input_bound(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    ‖embed (reverseInputVector m ell F z hz g)‖^2 ≤ 36*(
      (‖embed (phaseFirst m ell F z hz g)‖^2+‖embed (phaseSecond m ell F z hz g)‖^2)+
      ‖embed (phaseInput m ell F z hz g 0)‖^2+‖embed (phaseInput m ell F z hz g 1)‖^2):=by
  have he:reverseInputVector m ell F z hz g=(3:ℂ) • phaseFirst m ell F z hz g+
      (phaseInput m ell F z hz g 0-phiInverseAction (phaseInput m ell F z hz g 1)):=by
    simp only [reverseInputVector,Fin.sum_univ_two,core_state,phaseRow,Matrix.cons_val_zero,
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

/-- The complete balanced profile/input source has one original cofinal tail. N is chosen before both profile indices, the cutoff and the causal branch. -/
theorem actual_reverse_input_common_payment(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    ∀ε:ℝ,0<ε→∃N:ℕ,∀m,N ≤ m→∀ell,m ≤ ell→∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
      (∫⁻q:ℝ,ENNReal.ofReal (‖embed (reverseInputVector m ell F (actualFrequency advanced μ q)
        (reverse_frequency_nonreal advanced μ hμ q) g)‖^2)) ≤ ENNReal.ofReal ε:=by
  intro ε hε
  obtain ⟨N0,h0⟩:=actual_combined_profile_common_tail μ hμ g (ε/108) (by positivity)
  obtain ⟨N1,h1⟩:=actual_phi_theta_common_tail μ hμ (reverseInputSeed g 0) (ε/108) (by positivity)
  obtain ⟨N2,h2⟩:=actual_phi_theta_common_tail μ hμ (reverseInputSeed g 1) (ε/108) (by positivity)
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
        (coreEquiv.symm (reverseInputSeed g i))))) :=
      continuous_iff_continuousAt.mpr (fun q=>(actual_physical_resolvent_derivative F advanced μ hμ
        (phiThetaAction m ell) (coreEquiv.symm (reverseInputSeed g i)) q).continuousAt)
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
end LowEnergy.ReverseNativeOuterSource
