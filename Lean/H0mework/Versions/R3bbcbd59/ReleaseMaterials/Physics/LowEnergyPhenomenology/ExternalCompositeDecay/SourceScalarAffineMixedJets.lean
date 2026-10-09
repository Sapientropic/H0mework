import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceScalarAffineCutoffTail
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceGaugeCoframeJets
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceScalarPositiveBulkWard

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace LowEnergy.SourceScalarAffineMixedJets
open GaussCoreHilbert GaussCoreDifferential GaussUnitaryHistory
open GaussFockPair
open SourceCoframeDilation SourceCoframeVolumeCurrent
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceGaugeCoframeJets SourceResolventBandLimit FullYSourceResolventGraphSplice
open MeasureTheory Filter
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Phi := SourceScalarAffineScaleTransport.generator

/-- The affine scalar and gauge flows restrict the same original configuration in independent coordinates. -/
theorem affine_gauge_flow (s t : ℝ) (f : QuantumTest) :
    SourceScalarAffineScaleTransport.coreFlow s (SourceGaugeScaleTransport.coreFlow t f)=
      SourceGaugeScaleTransport.coreFlow t (SourceScalarAffineScaleTransport.coreFlow s f) := by
  ext z word
  simp only [SourceScalarAffineScaleTransport.coreFlow_apply,SourceGaugeScaleTransport.coreFlow_apply]
  have h : SourceGaugeRadialCurrent.gaugeScale (Real.exp t)
      (SourceScalarAffineScaleTransport.scaleEquiv s z)=
      SourceScalarAffineScaleTransport.scaleEquiv s (SourceGaugeRadialCurrent.gaugeScale (Real.exp t) z) := rfl
  rw [h]
  ring

theorem affine_coframe_flow (s t : ℝ) (f : QuantumTest) :
    SourceScalarAffineScaleTransport.coreFlow s (coframeFlow t f)=
      coframeFlow t (SourceScalarAffineScaleTransport.coreFlow s f) := by
  ext z word
  simp only [coframeFlow,SourceScalarAffineScaleTransport.coreFlow_apply,SourceCoframeScaleTransport.coreFlow_apply]
  have h : SourceCoframeVolume.scale (SourceCoframeScaleTransport.rate ((3/2 : ℝ)*t))
      (SourceScalarAffineScaleTransport.scaleEquiv s z)=
      SourceScalarAffineScaleTransport.scaleEquiv s
        (SourceCoframeVolume.scale (SourceCoframeScaleTransport.rate ((3/2 : ℝ)*t)) z) := rfl
  rw [h]
  ring

private theorem bounded_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : E →L[ℂ] E) {f : ℝ → E} {v : E} {t : ℝ} (h : HasDerivAt f v t) :
    HasDerivAt (fun s => A (f s)) (A v) t :=
  (A.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h

theorem Phi_gauge_flow (t : ℝ) (f : QuantumTest) :
    Phi (SourceGaugeScaleTransport.coreFlow t f)=SourceGaugeScaleTransport.coreFlow t (Phi f) := by
  apply embed_injective
  have hl := SourceScalarAffineScaleTransport.strong_core_derivative
    (SourceGaugeScaleTransport.coreFlow t f) 0
  have hr := bounded_derivative
    (SourceGaugeScaleTransport.hilbertFlow t).toContinuousLinearEquiv.toContinuousLinearMap
    (SourceScalarAffineScaleTransport.strong_core_derivative f 0)
  have he (s : ℝ) : embed (SourceScalarAffineScaleTransport.coreFlow s
      (SourceGaugeScaleTransport.coreFlow t f))=
      SourceGaugeScaleTransport.hilbertFlow t (embed (SourceScalarAffineScaleTransport.coreFlow s f)) := by
    rw [affine_gauge_flow,SourceGaugeScaleTransport.hilbertFlow_on_core]
  have h := (hl.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => (he s).symm))).unique hr
  simp only [SourceScalarAffineScaleTransport.coreFlow_zero] at h
  exact h.trans (SourceGaugeScaleTransport.hilbertFlow_on_core t (Phi f))

theorem Phi_coframe_flow (s : ℝ) (f : QuantumTest) :
    Phi (coframeFlow s f)=coframeFlow s (Phi f) := by
  apply embed_injective
  have hl := SourceScalarAffineScaleTransport.strong_core_derivative (coframeFlow s f) 0
  have hr := bounded_derivative (coframeHilbert s).toContinuousLinearEquiv.toContinuousLinearMap
    (SourceScalarAffineScaleTransport.strong_core_derivative f 0)
  have he (t : ℝ) : embed (SourceScalarAffineScaleTransport.coreFlow t (coframeFlow s f))=
      coframeHilbert s (embed (SourceScalarAffineScaleTransport.coreFlow t f)) := by
    rw [affine_coframe_flow]
    exact (SourceCoframeScaleTransport.hilbertFlow_on_core _ _).symm
  have h := (hl.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => (he t).symm))).unique hr
  simp only [SourceScalarAffineScaleTransport.coreFlow_zero] at h
  exact h.trans (SourceCoframeScaleTransport.hilbertFlow_on_core _ _)

private theorem Phi_pair (f g : QuantumTest) : sourcePair f (Phi g)= -sourcePair (Phi f) g := by
  have h := (SourceScalarAffineScaleTransport.strong_core_derivative f 0).inner ℂ
    (SourceScalarAffineScaleTransport.strong_core_derivative g 0)
  have ht : HasDerivAt (fun t => sourcePair (SourceScalarAffineScaleTransport.coreFlow t f)
      (SourceScalarAffineScaleTransport.coreFlow t g))
      (sourcePair f (Phi g)+sourcePair (Phi f) g) 0 := by
    simpa only [sourcePair,SourceScalarAffineScaleTransport.coreFlow_zero] using! h
  have hc := ht.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun t => (SourceScalarAffineScaleTransport.coreFlow_pair t f g).symm))
  exact eq_neg_of_add_eq_zero_left (hc.unique (hasDerivAt_const 0 (sourcePair f g)))

theorem generators_affine_gauge : Commute Phi G := by
  apply LinearMap.ext
  intro q
  apply GaussCoreLabel.pair_separates
  intro f
  have hl := SourceGaugeScaleTransport.weak_flow_derivative f (Phi q) 0
  have hr := (SourceGaugeScaleTransport.weak_flow_derivative (Phi f) q 0).neg
  have he : (fun t => sourcePair f (SourceGaugeScaleTransport.coreFlow t (Phi q)))=
      fun t => -sourcePair (Phi f) (SourceGaugeScaleTransport.coreFlow t q) := by
    funext t
    rw [←Phi_gauge_flow,Phi_pair]
  rw [he] at hl
  have h := hl.unique hr
  simp only [SourceGaugeScaleTransport.coreFlow_zero] at h
  change sourcePair f (Phi (G q))=sourcePair f (G (Phi q))
  exact (h.trans (Phi_pair f (G q)).symm).symm

private theorem hilbert_core (a b : ℕ) (f : QuantumTest) (s t : ℝ) :
    testJet a b f s t=embed (SourceGaugeScaleTransport.coreFlow t (coframeFlow s (sourceTest a b f))) :=
  SourceGaugeScaleTransport.hilbertFlow_on_core t _

def tripleHilbert (s t u : ℝ) : H ≃ₗᵢ[ℂ] H :=
  (mixedHilbert s t).trans (SourceScalarAffineScaleTransport.hilbertFlow u)

def tripleSource (a b c : ℕ) (f : QuantumTest) : QuantumTest := sourceTest a b ((Phi^c) f)

def tripleJet (a b c : ℕ) (f : QuantumTest) (s t u : ℝ) : H :=
  SourceScalarAffineScaleTransport.hilbertFlow u (testJet a b ((Phi^c) f) s t)

theorem triple_jet_base (f : QuantumTest) (s t u : ℝ) :
    tripleJet 0 0 0 f s t u=tripleHilbert s t u (embed f) := by
  simp only [tripleJet,tripleHilbert,pow_zero,Module.End.one_apply,test_jet_zero,LinearIsometryEquiv.trans_apply]

theorem triple_jet_origin (a b c : ℕ) (f : QuantumTest) :
    tripleJet a b c f 0 0 0=embed (tripleSource a b c f) := by
  rw [tripleJet,test_jet_origin,SourceScalarAffineScaleTransport.hilbertFlow_zero]
  rfl

theorem triple_coframe_derivative (a b c : ℕ) (f : QuantumTest) (s t u : ℝ) :
    HasDerivAt (fun r => tripleJet a b c f r t u) (tripleJet (a+1) b c f s t u) s :=
  bounded_derivative (SourceScalarAffineScaleTransport.hilbertFlow u).toContinuousLinearEquiv.toContinuousLinearMap
    (test_coframe_derivative a b ((Phi^c) f) s t)

theorem triple_gauge_derivative (a b c : ℕ) (f : QuantumTest) (s t u : ℝ) :
    HasDerivAt (fun r => tripleJet a b c f s r u) (tripleJet a (b+1) c f s t u) t :=
  bounded_derivative (SourceScalarAffineScaleTransport.hilbertFlow u).toContinuousLinearEquiv.toContinuousLinearMap
    (test_gauge_derivative a b ((Phi^c) f) s t)

theorem triple_affine_derivative (a b c : ℕ) (f : QuantumTest) (s t u : ℝ) :
    HasDerivAt (tripleJet a b c f s t) (tripleJet a b (c+1) f s t u) u := by
  have hp : Phi (sourceTest a b ((Phi^c) f))=sourceTest a b ((Phi^(c+1)) f) := by
    have hK : Commute Phi K := by
      have h := SourceScalarPositiveBulkWard.original_dilation_phi
      rw [←SourceScalarAffineScaleTransport.generator_commutator] at h
      change Phi*dilation-dilation*Phi=0 at h
      have he := sub_eq_zero.mp h
      show Phi*K=K*Phi
      rw [K,mul_smul_comm,smul_mul_assoc,he]
    have hG : Commute Phi G := by
      exact generators_affine_gauge
    have h₁ := LinearMap.congr_fun (hK.pow_right a).eq ((G^b) ((Phi^c) f))
    have h₂ := LinearMap.congr_fun (hG.pow_right b).eq ((Phi^c) f)
    have hpow : Phi ((Phi^c) f)=(Phi^(c+1)) f := by rw [pow_succ'];rfl
    change Phi ((K^a) ((G^b) ((Phi^c) f)))=(K^a) (Phi ((G^b) ((Phi^c) f))) at h₁
    change Phi ((G^b) ((Phi^c) f))=(G^b) (Phi ((Phi^c) f)) at h₂
    change Phi ((K^a) ((G^b) ((Phi^c) f)))=(K^a) ((G^b) ((Phi^(c+1)) f))
    rw [h₁,h₂,hpow]
  have h := SourceScalarAffineScaleTransport.strong_core_derivative
    (SourceGaugeScaleTransport.coreFlow t (coframeFlow s (sourceTest a b ((Phi^c) f)))) u
  have he : Phi (SourceGaugeScaleTransport.coreFlow t (coframeFlow s (sourceTest a b ((Phi^c) f))))=
      SourceGaugeScaleTransport.coreFlow t (coframeFlow s (sourceTest a b ((Phi^(c+1)) f))) := by
    rw [Phi_gauge_flow,Phi_coframe_flow,hp]
  have h0 (r : ℝ) : tripleJet a b c f s t r=
      embed (SourceScalarAffineScaleTransport.coreFlow r
        (SourceGaugeScaleTransport.coreFlow t (coframeFlow s (sourceTest a b ((Phi^c) f))))) := by
    rw [tripleJet,hilbert_core,SourceScalarAffineScaleTransport.hilbertFlow_on_core]
  have h1 : HasDerivAt (fun r => embed (SourceScalarAffineScaleTransport.coreFlow r
      (SourceGaugeScaleTransport.coreFlow t (coframeFlow s (sourceTest a b ((Phi^c) f))))))
      (embed (SourceScalarAffineScaleTransport.coreFlow u
        (SourceGaugeScaleTransport.coreFlow t (coframeFlow s (sourceTest a b ((Phi^(c+1)) f)))))) u := by
    simpa only [he] using! h
  have hd : HasDerivAt (tripleJet a b c f s t)
      (embed (SourceScalarAffineScaleTransport.coreFlow u
        (SourceGaugeScaleTransport.coreFlow t (coframeFlow s (sourceTest a b ((Phi^(c+1)) f)))))) u :=
    h1.congr_of_eventuallyEq (Filter.Eventually.of_forall h0)
  simpa only [tripleJet,hilbert_core,SourceScalarAffineScaleTransport.hilbertFlow_on_core] using! hd

theorem triple_jet_norm (a b c : ℕ) (f : QuantumTest) (s t u : ℝ) :
    ‖tripleJet a b c f s t u‖=‖embed (tripleSource a b c f)‖ := by
  rw [tripleJet,LinearIsometryEquiv.norm_map,test_jet_norm]
  rfl

/-- Every fixed original three-axis source jet has the same all-frequency finite-resolvent budget. -/
theorem actual_triple_jet_energy (F : Index) (μ : ℝ) (hμ : 0<μ) (a b c : ℕ)
    (f : QuantumTest) (s t u : ℝ) :
    (∫ w : ℝ, ‖finiteResolvent F (line μ w) (tripleJet a b c f s t u)‖^2)=
      (Real.pi/μ)*‖embed (tripleSource a b c f)‖^2 := by
  simpa only [line,mul_comm (μ : ℂ) Complex.I,triple_jet_norm] using!
    SourceActualResolventEnergy.actual_square_integral F μ hμ (tripleJet a b c f s t u)

end LowEnergy.SourceScalarAffineMixedJets
