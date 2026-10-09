import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualScalarPhaseQuadraticMoment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualPhaseWardIntertwiner
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseFullResponse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualShiftedQuadraticWardPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourceScalarVirialBulk SourceScalarGaugeScale SourceHamiltonianScaleJet SourcePhysicalKineticSquare
open SourceScalarAffineCutoffTail
open SourceNativeCutoffContact SourceRetardedGraph SourceResolventBandLimit ActualVectorJointCost
open SourceInverseFullResponse ActualPhaseWardIntertwiner ActualPhaseBulkSquare
open ActualScalarPhaseJet ActualScalarPhaseFrequencyReturn ActualScalarPhaseQuadraticMoment
open ActualMixedWindowGram ActualMixedCovarianceTail FullYSourceResolventGraphSplice
open SourceJointResidualEnergy MeasureTheory Filter Lean Meta Elab Term
open scoped InnerProductSpace BigOperators ENNReal
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] compressionCore resolventCore diagonalAction phaseGenerator phaseJet phaseSecond
attribute [local irreducible] sourcePair coreWindow shiftedInverseWard phaseForce

elab "paid_shifted_response%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseFullResponse 0) "LowEnergy") "SourceInverseFullResponse"
  let name:=Name.str ns field.getId.eraseMacroScopes.toString
  unless (←getEnv).contains name do throwError "Missing original full source response proof"
  mkConstWithFreshMVarLevels name

/-- The shift is in the linear Ward polynomial, not in a physical generator. -/
def shiftedWardResponse : PairMatrix →ₗ[ℂ] PairMatrix where
  toFun P:=InverseVolumeWardAlgebra.inverseWard (pairDelta Phi+(2:ℂ) • LinearMap.id)
    (pairDelta Gauge) (pairDelta Coframe) (vacuumJetCoefficient:ℂ) P
  map_add' P Q := by
    simp only [InverseVolumeWardAlgebra.inverseWard,InverseVolumeWardAlgebra.mixedPolynomial,
      InverseVolumeWardAlgebra.affinePolynomial,InverseVolumeWardAlgebra.inverseLocalPolynomial,
      map_add,map_sub,map_smul,smul_add,smul_sub,smul_smul]
    module
  map_smul' c P := by
    simp only [InverseVolumeWardAlgebra.inverseWard,InverseVolumeWardAlgebra.mixedPolynomial,
      InverseVolumeWardAlgebra.affinePolynomial,InverseVolumeWardAlgebra.inverseLocalPolynomial,
      map_add,map_sub,map_smul,smul_add,smul_sub,smul_smul,RingHom.id_apply]
    module

def phaseResponseSecond : PairMatrix →ₗ[ℂ] PairMatrix :=
  (pairDelta phaseGenerator).comp (pairDelta phaseGenerator)

private theorem response_phi(f h:QuantumTest)(M:End):
    responseRead f h (deltaPhi M)=pairDelta Phi (responseRead f h M) := by
  rw [←SourceScalarAffineScaleTransport.generator_commutator]
  exact (paid_shifted_response% response_delta) Phi (paid_shifted_response% phi_pair) f h M
private theorem response_gauge(f h:QuantumTest)(M:End):
    responseRead f h (deltaGauge M)=pairDelta Gauge (responseRead f h M) := by
  rw [←SourceGaugeScaleTransport.generator_commutator]
  exact (paid_shifted_response% response_delta) Gauge (paid_shifted_response% gauge_pair) f h M
private theorem response_coframe(f h:QuantumTest)(M:End):
    responseRead f h (scaleDerivative M)=pairDelta Coframe (responseRead f h M) := by
  rw [←SourceGaugeCoframeJets.K_commutator]
  exact (paid_shifted_response% response_delta) Coframe (paid_shifted_response% coframe_pair) f h M
private theorem response_phase(f h:QuantumTest)(M:End):
    responseRead f h (phaseJet M)=pairDelta phaseGenerator (responseRead f h M) := by
  simp only [phaseJet,LinearMap.coe_mk,AddHom.coe_mk]
  exact (paid_shifted_response% response_delta) phaseGenerator (paid_quadratic_phase% phase_skew) f h M

theorem actual_shifted_response_read(f h:QuantumTest)(M:End):
    responseRead f h (shiftedInverseWard M)=shiftedWardResponse (responseRead f h M) := by
  unfold shiftedInverseWard shiftedWardResponse
  apply (paid_shifted_response% polynomial_map) (responseRead f h) phiShiftTwo deltaGauge scaleDerivative
  · intro x
    change responseRead f h (deltaPhi x+(2:ℂ) • x)=
      pairDelta Phi (responseRead f h x)+(2:ℂ) • responseRead f h x
    rw [map_add,map_smul,response_phi]
  · exact response_gauge f h
  · exact response_coframe f h

/-- Both actual source legs and every ordered phase jet are retained. -/
theorem actual_shifted_phase_response_read(f h:QuantumTest)(M:End):
    responseRead f h (phaseSecond (shiftedInverseWard M))=
      phaseResponseSecond (shiftedWardResponse (responseRead f h M)) := by
  simp only [phaseSecond,LinearMap.comp_apply]
  rw [response_phase,response_phase,actual_shifted_response_read]
  rfl

def shiftedSquare : End := phaseSecond (shiftedInverseWard (diagonalAction*diagonalAction))
attribute [local irreducible] shiftedSquare shiftedWardResponse phaseResponseSecond responseRead

/-- This is the original positive form at the actual moving theta RF input. -/
theorem actual_positive_shifted_response(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    let q:=resolventCore F z hz g
    SourceScalarInverseNativeEnergy.inverseForm (thetaAction m ell q)+
      (8/phaseCoefficient)*‖embed (phaseForce (thetaAction m ell q))‖^2=
      (-(1/(2*phaseCoefficient)))*
        (phaseResponseSecond (shiftedWardResponse
          (responseRead q q (diagonalAction*diagonalAction))) (thetaAction m ell) (thetaAction m ell)).re := by
  dsimp only
  have h:=actual_inverse_form_shifted_source_square (thetaAction m ell (resolventCore F z hz g))
  have hr:=congrFun (congrFun
    (actual_shifted_phase_response_read (resolventCore F z hz g) (resolventCore F z hz g)
      (diagonalAction*diagonalAction)) (thetaAction m ell)) (thetaAction m ell)
  simp only [responseRead,LinearMap.coe_mk,AddHom.coe_mk] at hr
  change sourcePair (thetaAction m ell (resolventCore F z hz g))
      (phaseSecond (shiftedInverseWard (diagonalAction*diagonalAction))
        (thetaAction m ell (resolventCore F z hz g)))=_ at hr
  rw [hr] at h
  simpa only [responseRead,LinearMap.coe_mk,AddHom.coe_mk] using h

private theorem inverse_input(A:End)(F:Index)(z:ℂ)(hz:z.im≠0):
    A*resolventCore F z hz=resolventCore F z hz*A+
      resolventCore F z hz*(compressionCore F*A-A*compressionCore F)*resolventCore F z hz := by
  have hi:=(paid_phase_inverse% actual_inverse) F z hz
  have h:=(paid_phase_inverse% inverse_comm) (compressionCore F-z • (1:End))
    (resolventCore F z hz) A hi.1 hi.2
  simp only [(paid_phase_inverse% comm_spectral)] at h
  change A*resolventCore F z hz-resolventCore F z hz*A=
    -resolventCore F z hz*(A*compressionCore F-compressionCore F*A)*resolventCore F z hz at h
  linear_combination (norm:=noncomm_ring) h

/-- This full RF splice includes the real cutoff commutator. -/
theorem actual_full_cutoff_input(A:End)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0):
    A*coreWindow m ell F z hz=coreWindow m ell F z hz*A+
      thetaAction m ell*resolventCore F z hz*(compressionCore F*A-A*compressionCore F)*resolventCore F z hz+
      (A*thetaAction m ell-thetaAction m ell*A)*resolventCore F z hz := by
  have h:=congrArg (fun T:End=>thetaAction m ell*T) (inverse_input A F z hz)
  simp only [coreWindow] at *
  linear_combination (norm:=noncomm_ring) h

/-- The entire actual native and Own commutator insertion on the same RF. -/
def nativeResponseCorrection(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):ℂ :=
  let R:=resolventCore F z hz
  let W:=coreWindow m ell F z hz
  sourcePair (W g) (thetaAction m ell (((R*(diagonalAction*shiftedSquare-shiftedSquare*diagonalAction)-
    R*(defectAction F*shiftedSquare-shiftedSquare*defectAction F))*R) g))

/-- The genuine radial commutator is distinct from the native/Own insertion. -/
def radialResponseCorrection(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):ℂ :=
  sourcePair (coreWindow m ell F z hz g)
    ((shiftedSquare*thetaAction m ell-thetaAction m ell*shiftedSquare) (resolventCore F z hz g))

/-- Both actual Hamiltonian and Own currents are kept in the same source word. -/
def liveResponseCorrection(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):ℂ :=
  let R:=resolventCore F z hz
  let W:=coreWindow m ell F z hz
  sourcePair (W g) (thetaAction m ell (((R*(diagonalAction*shiftedSquare-shiftedSquare*diagonalAction)-
    R*(defectAction F*shiftedSquare-shiftedSquare*defectAction F))*R) g))+
    sourcePair (W g) ((shiftedSquare*thetaAction m ell-thetaAction m ell*shiftedSquare) (R g))

theorem actual_live_response_parts(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    liveResponseCorrection m ell F z hz g=
      nativeResponseCorrection m ell F z hz g+radialResponseCorrection m ell F z hz g := rfl

/-- Native insertion, fixed source input, OwnSquare response and radial contact stay coherent. -/
theorem actual_shifted_square_input_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    sourcePair (coreWindow m ell F z hz g) (shiftedSquare (coreWindow m ell F z hz g))-
      liveResponseCorrection m ell F z hz g=
      sourcePair (coreWindow m ell F z hz g) (coreWindow m ell F z hz (shiftedSquare g)) := by
  have hc:compressionCore F=diagonalAction-defectAction F := by unfold defectAction;abel
  have h:=LinearMap.congr_fun (actual_full_cutoff_input shiftedSquare m ell F z hz) g
  rw [hc] at h
  simp only [LinearMap.add_apply,Module.End.mul_apply,LinearMap.sub_apply,mul_sub,sub_mul] at h
  change shiftedSquare (coreWindow m ell F z hz g)=_ at h
  rw [h]
  simp only [liveResponseCorrection,Module.End.mul_apply,LinearMap.sub_apply,
    mul_sub,sub_mul,map_sub,(paid_phase_frequency% pair_add_right),(paid_phase_frequency% pair_sub_right)]
  ring

/-- Phi's actual affine contact remains in the source RF splice. -/
theorem actual_phi_window_splice(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0):
    Phi*coreWindow m ell F z hz=coreWindow m ell F z hz*Phi-
      thetaAction m ell*resolventCore F z hz*deltaPhi (compressionCore F)*resolventCore F z hz+
      affineCutoff m ell*resolventCore F z hz := by
  have h:=actual_full_cutoff_input Phi m ell F z hz
  have hC:compressionCore F*Phi-Phi*compressionCore F= -deltaPhi (compressionCore F) := by
    rw [←SourceScalarAffineScaleTransport.generator_commutator]
    noncomm_ring
  have ht:Phi*thetaAction m ell-thetaAction m ell*Phi=affineCutoff m ell := by
    rw [SourceScalarAffineScaleTransport.generator_commutator]
    rfl
  rw [hC,ht] at h
  simpa only [mul_neg,neg_mul,←sub_eq_add_neg] using h

/-- Gauge has its generated zero cutoff jet; its whole CF jet remains. -/
theorem actual_gauge_window_splice(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0):
    Gauge*coreWindow m ell F z hz=coreWindow m ell F z hz*Gauge-
      thetaAction m ell*resolventCore F z hz*deltaGauge (compressionCore F)*resolventCore F z hz := by
  have h:=actual_full_cutoff_input Gauge m ell F z hz
  have hC:compressionCore F*Gauge-Gauge*compressionCore F= -deltaGauge (compressionCore F) := by
    rw [←SourceGaugeScaleTransport.generator_commutator]
    noncomm_ring
  have ht:Gauge*thetaAction m ell-thetaAction m ell*Gauge=0 := by
    rw [SourceGaugeScaleTransport.generator_commutator]
    exact ActualAffineCutoffCausalTail.actual_gauge_cutoff_zero m ell
  rw [hC,ht] at h
  simpa only [mul_neg,neg_mul,zero_mul,add_zero,←sub_eq_add_neg] using h

/-- The three coframe response jets use the real source coframe derivative. -/
theorem actual_coframe_window_splice(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0):
    Coframe*coreWindow m ell F z hz=coreWindow m ell F z hz*Coframe-
      thetaAction m ell*resolventCore F z hz*scaleDerivative (compressionCore F)*resolventCore F z hz+
      scaleDerivative (thetaAction m ell)*resolventCore F z hz := by
  have h:=actual_full_cutoff_input Coframe m ell F z hz
  have hC:compressionCore F*Coframe-Coframe*compressionCore F= -scaleDerivative (compressionCore F) := by
    rw [←SourceGaugeCoframeJets.K_commutator]
    noncomm_ring
  have ht:Coframe*thetaAction m ell-thetaAction m ell*Coframe=scaleDerivative (thetaAction m ell) :=
    SourceGaugeCoframeJets.K_commutator _
  rw [hC,ht] at h
  simpa only [mul_neg,neg_mul,←sub_eq_add_neg] using h

/-- The entire moving positive response has one source-generated live correction,
not an assumed flux budget or a CF/H0 replacement. -/
theorem actual_positive_form_input_payment(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    let W:=coreWindow m ell F z hz
    SourceScalarInverseNativeEnergy.inverseForm (W g)+(8/phaseCoefficient)*‖embed (phaseForce (W g))‖^2=
      (-(1/(2*phaseCoefficient)))*(sourcePair (W g) (W (shiftedSquare g))+
        liveResponseCorrection m ell F z hz g).re := by
  dsimp only
  have h:=actual_inverse_form_shifted_source_square (coreWindow m ell F z hz g)
  have hs:phaseSecond (shiftedInverseWard (diagonalAction*diagonalAction))=shiftedSquare := by
    unfold shiftedSquare
    rfl
  rw [hs] at h
  have hi:=actual_shifted_square_input_return m ell F z hz g
  have he:sourcePair (coreWindow m ell F z hz g) (shiftedSquare (coreWindow m ell F z hz g))=
      sourcePair (coreWindow m ell F z hz g) (coreWindow m ell F z hz (shiftedSquare g))+
        liveResponseCorrection m ell F z hz g := by linear_combination (norm:=ring) hi
  rw [he] at h
  exact h

private theorem mu_positive:0<sourceMu := lt_of_lt_of_le (by norm_num) source_mu_large

/-- The fixed source B g is paid before F; the native/Own and radial response
are explicit live data and are never assumed small. -/
theorem actual_corrected_shifted_response_tail(g:QuantumTest):
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        let f:=fun w:ℝ=>sourcePair
          (coreWindow m ell F (causalFrequency advanced sourceMu w)
            ((paid_phase_frequency% causal_nonreal) advanced sourceMu mu_positive w) g)
          (shiftedSquare (coreWindow m ell F (causalFrequency advanced sourceMu w)
            ((paid_phase_frequency% causal_nonreal) advanced sourceMu mu_positive w) g))-
          liveResponseCorrection m ell F (causalFrequency advanced sourceMu w)
            ((paid_phase_frequency% causal_nonreal) advanced sourceMu mu_positive w) g
        Integrable f ∧ ‖∫w:ℝ,f w‖≤ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=(paid_phase_moment% window_pair_tail) sourceMu mu_positive g (shiftedSquare g) ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  dsimp only
  let v:=fun w:ℝ=>sourcePair
    (coreWindow m ell F (causalFrequency advanced sourceMu w)
      ((paid_phase_frequency% causal_nonreal) advanced sourceMu mu_positive w) g)
    (coreWindow m ell F (causalFrequency advanced sourceMu w)
      ((paid_phase_frequency% causal_nonreal) advanced sourceMu mu_positive w) (shiftedSquare g))
  have he(w:ℝ):v w=inner ℂ (window m ell F (causalFrequency advanced sourceMu w) g)
      (window m ell F (causalFrequency advanced sourceMu w) (shiftedSquare g)) := by
    simp only [v,coreWindow,Module.End.mul_apply,sourcePair,(paid_mixed_core% window_core)]
  have hp:(∫⁻w:ℝ,ENNReal.ofReal ‖v w‖)≤ENNReal.ofReal ε := by
    simp_rw [he]
    exact hF advanced
  have hv:Integrable v := by
    refine ⟨?_,?_⟩
    · have hc:Continuous v := by
        change Continuous (fun w:ℝ=>v w)
        simp_rw [he]
        exact ((paid_phase_moment% window_continuous) advanced sourceMu mu_positive m ell F g).inner (𝕜:=ℂ)
          ((paid_phase_moment% window_continuous) advanced sourceMu mu_positive m ell F (shiftedSquare g))
      exact hc.aestronglyMeasurable
    · rw [hasFiniteIntegral_iff_norm]
      exact lt_of_le_of_lt hp ENNReal.ofReal_lt_top
  simp_rw [actual_shifted_square_input_return]
  refine ⟨hv,?_⟩
  apply (norm_integral_le_lintegral_norm v).trans
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hp).trans_eq (ENNReal.toReal_ofReal hε.le)

/-- The actual positive inverse form and force response, together with their
explicit native/Own/radial correction, are one internally paid signed quantity. -/
def wholePositivePayment(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):ℝ :=
  let z:=causalFrequency advanced sourceMu w
  let hz:=(paid_phase_frequency% causal_nonreal) advanced sourceMu mu_positive w
  let f:=coreWindow m ell F z hz g
  SourceScalarInverseNativeEnergy.inverseForm f+(8/phaseCoefficient)*‖embed (phaseForce f)‖^2+
    (1/(2*phaseCoefficient))*(liveResponseCorrection m ell F z hz g).re

private theorem whole_positive_return(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):
    wholePositivePayment advanced m ell F g w=
      (-(1/(2*phaseCoefficient)))*
      (sourcePair (coreWindow m ell F (causalFrequency advanced sourceMu w)
        ((paid_phase_frequency% causal_nonreal) advanced sourceMu mu_positive w) g)
        (shiftedSquare (coreWindow m ell F (causalFrequency advanced sourceMu w)
          ((paid_phase_frequency% causal_nonreal) advanced sourceMu mu_positive w) g))-
      liveResponseCorrection m ell F (causalFrequency advanced sourceMu w)
        ((paid_phase_frequency% causal_nonreal) advanced sourceMu mu_positive w) g).re := by
  have h:=actual_positive_form_input_payment m ell F (causalFrequency advanced sourceMu w)
    ((paid_phase_frequency% causal_nonreal) advanced sourceMu mu_positive w) g
  dsimp only at h
  have hi:=actual_shifted_square_input_return m ell F (causalFrequency advanced sourceMu w)
    ((paid_phase_frequency% causal_nonreal) advanced sourceMu mu_positive w) g
  have hr:=congrArg Complex.re hi
  simp only [Complex.sub_re] at hr
  simp only [wholePositivePayment,Complex.sub_re]
  rw [h,Complex.add_re]
  linear_combination (norm:=ring) (1/(2*phaseCoefficient))*hr

/-- A generated payment for the original moving positive form. Its entire
live correction remains explicit; no target budget or flux tail is a premise. -/
theorem actual_whole_positive_payment_tail(g:QuantumTest):
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (wholePositivePayment advanced m ell F g) ∧
        |∫w:ℝ,wholePositivePayment advanced m ell F g w|≤ε := by
  intro ε hε
  let a:ℝ:=1/(2*phaseCoefficient)
  have ha:0≤a:=div_nonneg (by norm_num) (mul_nonneg (by norm_num) actual_phase_coefficient_positive.le)
  let δ:=ε/(a+1)
  have hd:0<δ:=div_pos hε (by positivity)
  obtain ⟨N,hN⟩:=actual_corrected_shifted_response_tail g δ hd
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  have h:=hF advanced
  dsimp only at h
  let f:=fun w:ℝ=>sourcePair
      (coreWindow m ell F (causalFrequency advanced sourceMu w)
        ((paid_phase_frequency% causal_nonreal) advanced sourceMu mu_positive w) g)
      (shiftedSquare (coreWindow m ell F (causalFrequency advanced sourceMu w)
        ((paid_phase_frequency% causal_nonreal) advanced sourceMu mu_positive w) g))-
      liveResponseCorrection m ell F (causalFrequency advanced sourceMu w)
        ((paid_phase_frequency% causal_nonreal) advanced sourceMu mu_positive w) g
  change Integrable f ∧ ‖∫w:ℝ,f w‖≤δ at h
  have hir:Integrable (fun w:ℝ=>(f w).re) := by
    simpa only [RCLike.re_to_complex] using h.1.re
  have hword:wholePositivePayment advanced m ell F g=fun w:ℝ=>-a*(f w).re := by
    funext w
    exact whole_positive_return advanced m ell F g w
  rw [hword]
  refine ⟨hir.const_mul (-a),?_⟩
  rw [integral_const_mul,abs_mul,abs_neg,abs_of_nonneg ha]
  have he:=integral_re h.1
  simp only [RCLike.re_to_complex] at he
  rw [he]
  have hp:|(∫w:ℝ,f w).re|≤δ := (Complex.abs_re_le_norm _).trans h.2
  have hd':a*δ≤ε := by
    dsimp [δ]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0<a+1)).mpr
    nlinarith only [hε,ha]
  exact (mul_le_mul_of_nonneg_left hp ha).trans hd'

end LowEnergy.ActualShiftedQuadraticWardPayment
