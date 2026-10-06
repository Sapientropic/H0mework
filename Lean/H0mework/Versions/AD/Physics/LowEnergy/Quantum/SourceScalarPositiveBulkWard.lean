import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceScalarAffineScaleTransport
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceGaugeCoframeWard

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarPositiveBulkWard
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussNativeForm
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation SourceHamiltonianVolume
open SourceScalarVirialBulk SourceScalarGaugeScale SourceHamiltonianScaleJet SourceOriginalHamiltonianSquare
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open FullYSourceResolventGraphSplice SourceEscapeCurrent SourcePhysicalHamiltonianSquare
open scoped ContDiff InnerProductSpace
abbrev End := SourceScalarGaugeScale.End
abbrev Op := H →L[ℂ] H

private theorem affine_volume_flow (t : ℝ) (f : QuantumTest) :
    SourceScalarAffineScaleTransport.coreFlow t (volumeAction f)=
      volumeAction (SourceScalarAffineScaleTransport.coreFlow t f) := by
  ext z word
  simp only [SourceScalarAffineScaleTransport.coreFlow_apply,volumeAction,GaussNativeForm.multiply_apply]
  change (Real.exp ((61/2 : ℝ)*t) : ℂ)*((volume z : ℂ)*f (SourceScalarAffineScaleTransport.scaleEquiv t z) word)=
    (volume z : ℂ)*((Real.exp ((61/2 : ℝ)*t) : ℂ)*f (SourceScalarAffineScaleTransport.scaleEquiv t z) word)
  ring

private theorem gauge_volume_flow (t : ℝ) (f : QuantumTest) :
    SourceGaugeScaleTransport.coreFlow t (volumeAction f)=
      volumeAction (SourceGaugeScaleTransport.coreFlow t f) := by
  ext z word
  simp only [SourceGaugeScaleTransport.coreFlow_apply,volumeAction,GaussNativeForm.multiply_apply]
  change (Real.exp (18*t) : ℂ)*((volume z : ℂ)*f (SourceGaugeRadialCurrent.gaugeScale (Real.exp t) z) word)=
    (volume z : ℂ)*((Real.exp (18*t) : ℂ)*f (SourceGaugeRadialCurrent.gaugeScale (Real.exp t) z) word)
  ring

theorem original_volume_phi : deltaPhi volumeAction=0 := by
  rw [←SourceScalarAffineScaleTransport.generator_commutator]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  have hl := SourceScalarAffineScaleTransport.coreFlow_generator (volumeAction f) z word
  have hr := (SourceScalarAffineScaleTransport.coreFlow_generator f z word).const_mul (volume z : ℂ)
  have he : (fun t => SourceScalarAffineScaleTransport.coreFlow t (volumeAction f) z word)=
      fun t => (volume z : ℂ)*SourceScalarAffineScaleTransport.coreFlow t f z word := by
    funext t
    rw [affine_volume_flow]
    rfl
  rw [he] at hl
  exact sub_eq_zero.mpr (hl.unique hr)

theorem original_volume_gauge : deltaGauge volumeAction=0 := by
  rw [←SourceGaugeScaleTransport.generator_commutator]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  have hl := SourceGaugeScaleTransport.coreFlow_generator (volumeAction f) z word
  have hr := (SourceGaugeScaleTransport.coreFlow_generator f z word).const_mul (volume z : ℂ)
  have he : (fun t => SourceGaugeScaleTransport.coreFlow t (volumeAction f) z word)=
      fun t => (volume z : ℂ)*SourceGaugeScaleTransport.coreFlow t f z word := by
    funext t
    rw [gauge_volume_flow]
    rfl
  rw [he] at hl
  exact sub_eq_zero.mpr (hl.unique hr)

private theorem affine_coframe_flow (s t : ℝ) (f : QuantumTest) :
    SourceScalarAffineScaleTransport.coreFlow t (SourceCoframeScaleTransport.coreFlow s f)=
      SourceCoframeScaleTransport.coreFlow s (SourceScalarAffineScaleTransport.coreFlow t f) := by
  ext z word
  simp only [SourceScalarAffineScaleTransport.coreFlow_apply,SourceCoframeScaleTransport.coreFlow_apply,
    SourceScalarAffineScaleTransport.scaleEquiv_apply,SourceCoframeVolume.scale]
  ring

private theorem dilation_affine_flow (t : ℝ) (f : QuantumTest) :
    dilation (SourceScalarAffineScaleTransport.coreFlow t f)=
      SourceScalarAffineScaleTransport.coreFlow t (dilation f) := by
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  by_cases hz : z∈physicalChart
  · have hz' := (SourceScalarAffineScaleTransport.scale_chart_iff t z).mpr hz
    have hl := SourceCoframeScaleTransport.coreFlow_generator
      (SourceScalarAffineScaleTransport.coreFlow t f) ⟨z,hz⟩ word
    have hr := (SourceCoframeScaleTransport.coreFlow_generator f
      ⟨SourceScalarAffineScaleTransport.scaleEquiv t z,hz'⟩ word).const_mul
        (Real.exp ((61/2 : ℝ)*t) : ℂ)
    have he : (fun s => SourceCoframeScaleTransport.coreFlow s
        (SourceScalarAffineScaleTransport.coreFlow t f) z word)=
        fun s => (Real.exp ((61/2 : ℝ)*t) : ℂ)*SourceCoframeScaleTransport.coreFlow s f
          (SourceScalarAffineScaleTransport.scaleEquiv t z) word := by
      funext s
      rw [←affine_coframe_flow,SourceScalarAffineScaleTransport.coreFlow_apply]
    rw [he] at hl
    have h := hl.unique hr
    change Complex.I*dilation (SourceScalarAffineScaleTransport.coreFlow t f) z word=
      (Real.exp ((61/2 : ℝ)*t) : ℂ)*(Complex.I*dilation f (SourceScalarAffineScaleTransport.scaleEquiv t z) word) at h
    rw [←mul_left_comm] at h
    exact mul_left_cancel₀ Complex.I_ne_zero h
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport
      (fun h => hz (q.tsupport_subset h))
    rw [h0,h0]

theorem original_dilation_phi : deltaPhi dilation=0 := by
  rw [←SourceScalarAffineScaleTransport.generator_commutator]
  apply LinearMap.ext
  intro g
  apply GaussCoreLabel.pair_separates
  intro f
  have hl := SourceScalarAffineScaleTransport.weak_flow_derivative f (dilation g) 0
  have hr := SourceScalarAffineScaleTransport.weak_flow_derivative (dilation f) g 0
  have he : (fun t => sourcePair f (SourceScalarAffineScaleTransport.coreFlow t (dilation g)))=
      fun t => sourcePair (dilation f) (SourceScalarAffineScaleTransport.coreFlow t g) := by
    funext t
    rw [←dilation_affine_flow,dilation_pair]
  rw [he] at hl
  have h := hl.unique hr
  simp only [SourceScalarAffineScaleTransport.coreFlow_zero] at h
  have hh := h.trans (dilation_pair f (SourceScalarAffineScaleTransport.generator g)).symm
  change sourcePair f (SourceScalarAffineScaleTransport.generator (dilation g)-
    dilation (SourceScalarAffineScaleTransport.generator g))=sourcePair f 0
  simp only [sourcePair,map_sub,map_zero,inner_sub_right,inner_zero_right] at hh ⊢
  exact sub_eq_zero.mpr hh

theorem original_dilation_gauge : deltaGauge dilation=0 := by
  have h := SourceGaugeCoframeJets.generators_commute.eq
  change SourceGaugeScaleTransport.generator*((3*Complex.I/2 : ℂ) • dilation)=
    ((3*Complex.I/2 : ℂ) • dilation)*SourceGaugeScaleTransport.generator at h
  rw [mul_smul_comm,smul_mul_assoc] at h
  have hc : (3*Complex.I/2 : ℂ)≠0 := by exact div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (by norm_num)
  have he := (smul_right_injective _ hc) h
  rw [←SourceGaugeScaleTransport.generator_commutator,he,sub_self]

private theorem ad_product {R : Type*} [Ring R] (G A B : R) :
    G*(A*B)-(A*B)*G=(G*A-A*G)*B+A*(G*B-B*G) := by noncomm_ring

private theorem phi_product (A B : End) : deltaPhi (A*B)=deltaPhi A*B+A*deltaPhi B :=
  ad_product phiEulerAction A B
private theorem gauge_product (A B : End) : deltaGauge (A*B)=deltaGauge A*B+A*deltaGauge B :=
  ad_product SourceGaugeRadialPair.gaugeEulerAction A B
private theorem coframe_product (A B : End) : scaleDerivative (A*B)=scaleDerivative A*B+A*scaleDerivative B := by
  rw [←SourceGaugeCoframeJets.K_commutator,←SourceGaugeCoframeJets.K_commutator,
    ←SourceGaugeCoframeJets.K_commutator]
  exact ad_product SourceGaugeCoframeJets.K A B

private theorem volume_coframe : scaleDerivative volumeAction=(3 : ℂ) • volumeAction := by
  change (3*Complex.I/2) • (dilation*volumeAction-volumeAction*dilation)=_
  rw [SourceDilationKinetic.volume_scale_current,smul_smul]
  congr 1
  calc (3*Complex.I/2)*(-2*Complex.I) = -3*(Complex.I*Complex.I) := by ring
       _ = 3 := by rw [Complex.I_mul_I];ring

private theorem dilation_coframe : scaleDerivative dilation=0 := by
  change (3*Complex.I/2) • (dilation*dilation-dilation*dilation)=0
  rw [sub_self,smul_zero]

/-- The volume shift of the coframe derivation is forced by the original degree-three U. -/
def shiftedCoframe : End →ₗ[ℂ] End := scaleDerivative-(3 : ℂ) • LinearMap.id

def localPolynomial (A : End) : End := scaleDerivative (scaleDerivative (scaleDerivative A))+
  (3 : ℂ) • scaleDerivative (scaleDerivative A)-scaleDerivative A-(3 : ℂ) • A

def shiftedLocalPolynomial (A : End) : End := shiftedCoframe (shiftedCoframe (shiftedCoframe A))+
  (3 : ℂ) • shiftedCoframe (shiftedCoframe A)-shiftedCoframe A-(3 : ℂ) • A

def mixedPolynomial (A : End) : End :=
  let J := deltaPhi A-deltaGauge A
  deltaGauge (deltaGauge J)-(5 : ℂ) • deltaGauge J+(4 : ℂ) • J

def affinePolynomial (A : End) : End := deltaPhi (deltaPhi A)-(3 : ℂ) • deltaPhi A+(2 : ℂ) • A

def weightedBulkJet (A : End) : End := mixedPolynomial A+
  (vacuumJetCoefficient : ℂ) • affinePolynomial (shiftedLocalPolynomial A)

private theorem phi_volume_mul (A : End) : deltaPhi (volumeAction*A)=volumeAction*deltaPhi A := by
  rw [phi_product,original_volume_phi,zero_mul,zero_add]
private theorem gauge_volume_mul (A : End) : deltaGauge (volumeAction*A)=volumeAction*deltaGauge A := by
  rw [gauge_product,original_volume_gauge,zero_mul,zero_add]
private theorem shifted_volume_mul (A : End) : shiftedCoframe (volumeAction*A)=volumeAction*scaleDerivative A := by
  change scaleDerivative (volumeAction*A)-(3 : ℂ) • (volumeAction*A)=_
  rw [coframe_product,volume_coframe,smul_mul_assoc]
  exact add_sub_cancel_left _ _

private theorem mixed_volume (A : End) : mixedPolynomial (volumeAction*A)=volumeAction*mixedPolynomial A := by
  simp only [mixedPolynomial,phi_volume_mul,gauge_volume_mul,←mul_sub,←mul_add,←mul_smul_comm]
private theorem affine_volume (A : End) : affinePolynomial (volumeAction*A)=volumeAction*affinePolynomial A := by
  simp only [affinePolynomial,phi_volume_mul,mul_sub,mul_add,mul_smul_comm]
private theorem shifted_local_volume (A : End) : shiftedLocalPolynomial (volumeAction*A)=volumeAction*localPolynomial A := by
  simp only [shiftedLocalPolynomial,shifted_volume_mul,localPolynomial,mul_sub,mul_add,mul_smul_comm]

private theorem weighted_source : weightedBulkJet (volumeAction*diagonalAction)=volumeAction*positiveBulk := by
  rw [weightedBulkJet,mixed_volume,shifted_local_volume,affine_volume,←mul_smul_comm,←mul_add]
  have hb : mixedPolynomial diagonalAction+(vacuumJetCoefficient : ℂ) •
      affinePolynomial (localPolynomial diagonalAction)=positiveBulk := by
    have h := original_positive_bulk_source_jet
    run_tac Lean.Elab.Tactic.withMainContext do
      (← Lean.Elab.Tactic.getMainGoal).assign (← Lean.Meta.getFVarFromUserName `h)
      Lean.Elab.Tactic.replaceMainGoal []
  exact congrArg (fun A : End => volumeAction*A) hb

private theorem mixed_add (A B : End) : mixedPolynomial (A+B)=mixedPolynomial A+mixedPolynomial B := by
  simp only [mixedPolynomial,map_add,map_sub]
  module
private theorem mixed_smul (c : ℂ) (A : End) : mixedPolynomial (c • A)=c • mixedPolynomial A := by
  simp only [mixedPolynomial,map_smul,←smul_sub]
  module
private theorem local_add (A B : End) : shiftedLocalPolynomial (A+B)=shiftedLocalPolynomial A+shiftedLocalPolynomial B := by
  simp only [shiftedLocalPolynomial,map_add]
  module
private theorem local_smul (c : ℂ) (A : End) : shiftedLocalPolynomial (c • A)=c • shiftedLocalPolynomial A := by
  simp only [shiftedLocalPolynomial,map_smul]
  module
private theorem affine_add (A B : End) : affinePolynomial (A+B)=affinePolynomial A+affinePolynomial B := by
  simp only [affinePolynomial,map_add]
  module
private theorem affine_smul (c : ℂ) (A : End) : affinePolynomial (c • A)=c • affinePolynomial A := by
  simp only [affinePolynomial,map_smul]
  module
private theorem weighted_add (A B : End) : weightedBulkJet (A+B)=weightedBulkJet A+weightedBulkJet B := by
  rw [weightedBulkJet,mixed_add,local_add,affine_add,smul_add,weightedBulkJet,weightedBulkJet]
  abel
private theorem weighted_smul (c : ℂ) (A : End) : weightedBulkJet (c • A)=c • weightedBulkJet A := by
  rw [weightedBulkJet,mixed_smul,local_smul,affine_smul,smul_comm (vacuumJetCoefficient : ℂ) c,←smul_add]
  rfl

/-- Both original source polynomial factors annihilate the complete volume-current correction. -/
theorem original_dilation_annihilation : weightedBulkJet dilation=0 := by
  have hm : mixedPolynomial dilation=0 := by
    simp only [mixedPolynomial,original_dilation_phi,original_dilation_gauge,sub_self,map_zero,smul_zero,add_zero]
  have hD : shiftedCoframe dilation=(-3 : ℂ) • dilation := by
    simp only [shiftedCoframe,LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply,dilation_coframe,zero_sub,neg_smul]
  have hl : shiftedLocalPolynomial dilation=0 := by
    simp only [shiftedLocalPolynomial,hD,map_smul]
    module
  rw [weightedBulkJet,hm,hl,affinePolynomial,map_zero,map_zero,smul_zero,smul_zero,sub_zero,add_zero,smul_zero,add_zero]

/-- The positive native70/gauge/shifted-scalar bulk is a current of the actual symmetric H0-U source; no dilation remainder survives this whole polynomial. -/
theorem original_positive_bulk_symmetric_jet : weightedBulkJet symmetricScale=volumeAction*positiveBulk := by
  have hU : volumeAction*diagonalAction=symmetricScale+(3*Complex.I*(sourceTime 0 : ℂ)/8) • dilation := by
    have h := full_source_volume_current
    rw [symmetric_scale_source]
    linear_combination (norm := module) (-1/2 : ℂ) • h
  have ht : weightedBulkJet (symmetricScale+(3*Complex.I*(sourceTime 0 : ℂ)/8) • dilation)=
      weightedBulkJet symmetricScale := by
    rw [weighted_add,weighted_smul,original_dilation_annihilation,smul_zero,add_zero]
  exact ht.symm.trans ((congrArg weightedBulkJet hU.symm).trans weighted_source)

/-- The shifted vacuum factor is δc(δc−2)(δc−4); its zero constant term is exact. -/
theorem original_shifted_polynomial (A : End) : shiftedLocalPolynomial A=
    scaleDerivative (scaleDerivative (scaleDerivative A))-(6 : ℂ) • scaleDerivative (scaleDerivative A)+
      (8 : ℂ) • scaleDerivative A := by
  simp only [shiftedLocalPolynomial,shiftedCoframe,LinearMap.sub_apply,LinearMap.smul_apply,
    LinearMap.id_apply,map_sub,map_smul]
  module


open SourcePhysicalKineticSquare SourceScalarNativeComparison SourceScalarRetardedGram

private theorem inverse_volume_left (f : QuantumTest) : inverseVolumeAction (volumeAction f)=f := by
  have hc : Commute inverseVolumeAction volumeAction := by
    apply LinearMap.ext
    intro q
    apply DFunLike.ext
    intro z
    exact smul_comm (reciprocalVolume z : ℂ) (volume z : ℂ) (q z)
  exact (LinearMap.congr_fun hc.eq f).trans (volume_inverse f)

private theorem real_physical_return (A : End)
    (hU : ∀ f g,sourcePair f (volumeAction g)=sourcePair (volumeAction f) g)
    (hS : ∀ f g,sourcePair f (inverseRootAction g)=sourcePair (inverseRootAction f) g)
    (hc : Commute inverseRootAction A) (f : QuantumTest) :
    sourcePair f (volumeAction (A f))=
      sourcePair (inverseRootAction (volumeAction f)) (A (inverseRootAction (volumeAction f))) := by
  let x := volumeAction f
  have he : sourcePair (inverseVolumeAction x) (volumeAction (A (inverseVolumeAction x)))=
      sourcePair (inverseRootAction x) (A (inverseRootAction x)) := by
    rw [hU,volume_inverse,←inverse_root_square]
    have hec : A (inverseRootAction (inverseRootAction x))=
        inverseRootAction (A (inverseRootAction x)) :=
      (LinearMap.congr_fun hc.eq (inverseRootAction x)).symm
    rw [hec,hS]
  simpa only [x,inverse_volume_left] using! he

private theorem weighted_electric (f : QuantumTest) :
    sourcePair f (volumeAction (gaugeKinetic f))=
      sourcePair (inverseRootAction (volumeAction f)) (gaugeKinetic (inverseRootAction (volumeAction f))) :=
  real_physical_return gaugeKinetic (fun _ _ => multiply_pair _ _ _ _)
    (fun _ _ => multiply_pair _ _ _ _) inverse_root_electric f

private theorem weighted_shifted (f : QuantumTest) :
    sourcePair f (volumeAction (shiftedAction f))=
      sourcePair (inverseRootAction (volumeAction f)) (shiftedAction (inverseRootAction (volumeAction f))) :=
  real_physical_return shiftedAction (fun _ _ => multiply_pair _ _ _ _)
    (fun _ _ => multiply_pair _ _ _ _) (SourcePhysicalHamiltonianSquare.inverse_root_real _ _) f

def weightedBulkForm (f : QuantumTest) : ℝ := (sourcePair f (weightedBulkJet symmetricScale f)).re

/-- All native70 rows survive. The other two summands are the original positive electric and shifted-scalar forms. -/
theorem original_weighted_bulk_form (f : QuantumTest) : weightedBulkForm f=
    4*sourceTime 0*nativeScalarEnergy f+
      36*(sourcePair (inverseRootAction (volumeAction f)) (gaugeKinetic (inverseRootAction (volumeAction f)))).re+
      8*(sourcePair (inverseRootAction (volumeAction f)) (shiftedAction (inverseRootAction (volumeAction f)))).re := by
  rw [weightedBulkForm,original_positive_bulk_symmetric_jet,original_positive_bulk]
  simp only [Module.End.mul_apply,LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul,
    sourcePair,inner_add_right,inner_smul_right]
  change (((-8 : ℂ)*sourcePair f (volumeAction (scalarKinetic f))+
    (36 : ℂ)*sourcePair f (volumeAction (gaugeKinetic f)))+
    (8 : ℂ)*sourcePair f (volumeAction (shiftedAction f))).re=_
  rw [weighted_electric,weighted_shifted]
  simp only [Complex.add_re,Complex.mul_re,Complex.neg_re,Complex.neg_im,
    Complex.re_ofNat,Complex.im_ofNat,neg_zero,zero_mul,sub_zero]
  rw [actual_native_scalar_form]
  simp only [sourcePair]
  ring

theorem original_native_bulk_bound (f : QuantumTest) :
    4*sourceTime 0*nativeScalarEnergy f ≤ weightedBulkForm f := by
  rw [original_weighted_bulk_form]
  have hg := original_gauge_kinetic_nonnegative (inverseRootAction (volumeAction f))
  have hs := original_shifted_nonnegative (inverseRootAction (volumeAction f))
  linarith

theorem original_weighted_bulk_nonnegative (f : QuantumTest) : 0 ≤ weightedBulkForm f := by
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  exact (mul_nonneg (mul_nonneg (by norm_num) hn.le)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans (original_native_bulk_bound f)

open SourceMixedNativeReturn SourceScalarPairedTransport SourceJointScaleBudget

private def inputTest (F : Index) (g : diagonal.domain) (x : H) : QuantumTest :=
  coreEquiv.symm (Submodule.inclusion (input_span_core F g) ((inputSpan F g).orthogonalProjectionOnto x))
private theorem input_embed (F : Index) (g : diagonal.domain) (x : H) :
    embed (inputTest F g x)=((inputSpan F g).orthogonalProjectionOnto x : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem compression_input (F : Index) (g : diagonal.domain) (x : H) :
    GaussGradedCompression.compression F ((inputSpan F g).orthogonalProjectionOnto x : H)=
      GaussGradedCompression.compression F x := by
  apply ext_inner_left ℂ
  intro y
  have hy : GaussGradedCompression.compression F y∈inputSpan F g :=
    Submodule.mem_sup_left (SourceRetardedIncrement.compression_mem_support F y)
  exact (GaussGradedCompression.compression_pair F y _).symm.trans
    ((Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
      ⟨GaussGradedCompression.compression F y,hy⟩ x).trans (GaussGradedCompression.compression_pair F y x))
private theorem input_compression (F : Index) (g : diagonal.domain) (x : H) :
    embed (inputTest F g (GaussGradedCompression.compression F x))=GaussGradedCompression.compression F x := by
  rw [input_embed]
  exact congrArg Subtype.val ((inputSpan F g).orthogonalProjectionOnto_mem_subspace_eq_self
    ⟨GaussGradedCompression.compression F x,Submodule.mem_sup_left (SourceRetardedIncrement.compression_mem_support F x)⟩)
private theorem compression_core (F : Index) (f : QuantumTest) :
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem read_compression_left (F : Index) (g : diagonal.domain) (A : End) :
    sourceRead F g (compressionCore F*A)=GaussGradedCompression.compression F*sourceRead F g A := by
  apply ContinuousLinearMap.ext
  intro x
  exact compression_core F (A (inputTest F g x))
private theorem read_compression_right (F : Index) (g : diagonal.domain) (A : End) :
    sourceRead F g (A*compressionCore F)=sourceRead F g A*GaussGradedCompression.compression F := by
  apply ContinuousLinearMap.ext
  intro x
  have he : compressionCore F (inputTest F g x)=inputTest F g (GaussGradedCompression.compression F x) := by
    apply embed_injective
    exact (compression_core F _).trans ((congrArg (GaussGradedCompression.compression F) (input_embed F g x)).trans
      ((compression_input F g x).trans (input_compression F g x).symm))
  exact congrArg (fun f : QuantumTest => embed (A f)) he

/-- The symmetric scale's actual two projection defects, on the original whole input carrier. -/
def symmetricProjectionFlux (F : Index) (g : diagonal.domain) : Op :=
  (1/2 : ℂ) • sourceRead F g (defectAction F*volumeAction+volumeAction*defectAction F)

theorem actual_symmetric_compression (F : Index) (g : diagonal.domain) :
    sourceRead F g symmetricScale=
      (1/2 : ℂ) • (GaussGradedCompression.compression F*sourceRead F g volumeAction+
        sourceRead F g volumeAction*GaussGradedCompression.compression F)+symmetricProjectionFlux F g := by
  have hs : symmetricScale=(1/2 : ℂ) • (compressionCore F*volumeAction+volumeAction*compressionCore F)+
      (1/2 : ℂ) • (defectAction F*volumeAction+volumeAction*defectAction F) := by
    rw [symmetric_scale_source,defectAction]
    simp only [sub_mul,mul_sub]
    module
  have h := congrArg (sourceRead F g) hs
  simpa only [map_add,map_smul,read_compression_left,read_compression_right,symmetricProjectionFlux] using! h

private theorem anticommutator_resolvent {R : Type*} [Ring R] [Algebra ℂ R]
    (C V r : R) (z : ℂ) (hl : r*(C-z • 1)=1) (hr : (C-z • 1)*r=1) :
    r*((1/2 : ℂ) • (C*V+V*C))*r=
      (1/2 : ℂ) • (V*r+r*V)+z • (r*V*r) := by
  have hL : r*C=1+z • r := by
    rw [mul_sub,mul_smul_comm,mul_one] at hl
    exact sub_eq_iff_eq_add.mp hl
  have hR : C*r=1+z • r := by
    rw [sub_mul,smul_mul_assoc,one_mul] at hr
    exact sub_eq_iff_eq_add.mp hr
  calc
    _=(1/2 : ℂ) • ((r*C)*V*r+r*V*(C*r)) := by
      simp only [mul_smul_comm,smul_mul_assoc,mul_add,add_mul,mul_assoc]
    _=_ := by rw [hL,hR];simp only [add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,mul_smul_comm];module

private theorem anticommutator_flux {R : Type*} [Ring R] [Algebra ℂ R]
    (C V r Q P : R) (z : ℂ) (hl : r*(C-z • 1)=1) (hr : (C-z • 1)*r=1)
    (hq : Q=(1/2 : ℂ) • (C*V+V*C)+P) :
    r*Q*r=(1/2 : ℂ) • (V*r+r*V)+z • (r*V*r)+r*P*r := by
  rw [hq,mul_add,add_mul,anticommutator_resolvent C V r z hl hr]

/-- Whole retarded Q0 has two finite U endpoints, the z-weighted U sandwich, and both generated projection defects. -/
theorem actual_symmetric_retarded (F : Index) (g : diagonal.domain) (z : ℂ) (hz : z.im≠0) :
    finiteResolvent F z*sourceRead F g symmetricScale*finiteResolvent F z=
      (1/2 : ℂ) • (sourceRead F g volumeAction*finiteResolvent F z+
        finiteResolvent F z*sourceRead F g volumeAction)+
      z • (finiteResolvent F z*sourceRead F g volumeAction*finiteResolvent F z)+
      finiteResolvent F z*symmetricProjectionFlux F g*finiteResolvent F z := by
  have h := anticommutator_flux (R := Op) (GaussGradedCompression.compression F)
    (sourceRead F g volumeAction) (finiteResolvent F z) (sourceRead F g symmetricScale)
    (symmetricProjectionFlux F g) z
    (FullYSourceResolventGraphSplice.resolvent_left _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
    (FullYSourceResolventGraphSplice.resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
    (actual_symmetric_compression F g)
  exact h


abbrev Phi := SourceScalarAffineScaleTransport.generator
abbrev Gauge := SourceGaugeScaleTransport.generator
abbrev Coframe := SourceGaugeCoframeJets.K

private theorem flow_pair_generator (flow : ℝ → End) (G : End)
    (hzero : ∀ f,flow 0 f=f)
    (hpair : ∀ t f g,sourcePair (flow t f) (flow t g)=sourcePair f g)
    (hderiv : ∀ f,HasDerivAt (fun t : ℝ => embed (flow t f)) (embed (G f)) 0)
    (f g : QuantumTest) : sourcePair f (G g)= -sourcePair (G f) g := by
  have h := (hderiv f).inner ℂ (hderiv g)
  simp only [hzero] at h
  have he : (fun t : ℝ => inner ℂ (embed (flow t f)) (embed (flow t g)))=
      fun _ => sourcePair f g := funext (fun t => hpair t f g)
  rw [he] at h
  have heq := h.unique (hasDerivAt_const (0 : ℝ) (sourcePair f g))
  change sourcePair f (G g)+sourcePair (G f) g=0 at heq
  exact eq_neg_of_add_eq_zero_left heq

private theorem phi_pair (f g : QuantumTest) : sourcePair f (Phi g)= -sourcePair (Phi f) g :=
  flow_pair_generator SourceScalarAffineScaleTransport.coreFlow Phi
    SourceScalarAffineScaleTransport.coreFlow_zero SourceScalarAffineScaleTransport.coreFlow_pair
    (fun q => by simpa only [SourceScalarAffineScaleTransport.coreFlow_zero] using!
      SourceScalarAffineScaleTransport.strong_core_derivative q 0) f g
private theorem gauge_pair (f g : QuantumTest) : sourcePair f (Gauge g)= -sourcePair (Gauge f) g :=
  flow_pair_generator SourceGaugeScaleTransport.coreFlow Gauge
    SourceGaugeScaleTransport.coreFlow_zero SourceGaugeScaleTransport.coreFlow_pair
    (fun q => by simpa only [SourceGaugeScaleTransport.coreFlow_zero] using!
      SourceGaugeScaleTransport.strong_core_derivative q 0) f g
private theorem coframe_pair (f g : QuantumTest) : sourcePair f (Coframe g)= -sourcePair (Coframe f) g := by
  have hc : star (3*Complex.I/2 : ℂ)= -(3*Complex.I/2 : ℂ) := by simp;ring
  have hd := dilation_pair f g
  change sourcePair f ((3*Complex.I/2 : ℂ) • dilation g)=
    -sourcePair ((3*Complex.I/2 : ℂ) • dilation f) g
  simp only [sourcePair,map_smul,inner_smul_left,inner_smul_right,starRingEnd_apply] at hd ⊢
  rw [hc,hd]
  ring

abbrev PairMatrix := End → End → ℂ

/-- Acting on both actual source legs, with the anti-transpose signs fixed by the original Haar half-density. -/
def pairDelta (G : End) : PairMatrix →ₗ[ℂ] PairMatrix where
  toFun P A B := -P (G*A) B-P A (G*B)
  map_add' P Q := by ext A B;simp only [Pi.add_apply];ring
  map_smul' c P := by ext A B;simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply];ring

private def pairRead (f g : QuantumTest) : End →ₗ[ℂ] PairMatrix where
  toFun M A B := sourcePair (A f) (M (B g))
  map_add' M N := by ext A B;simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_right,Pi.add_apply]
  map_smul' c M := by ext A B;simp only [LinearMap.smul_apply,sourcePair,map_smul,inner_smul_right,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]

private theorem pair_read_delta (G : End) (hG : ∀ f g,sourcePair f (G g)= -sourcePair (G f) g)
    (f g : QuantumTest) (M : End) : pairRead f g (G*M-M*G)=pairDelta G (pairRead f g M) := by
  ext A B
  change sourcePair (A f) (G (M (B g))-M (G (B g)))=
    -sourcePair (G (A f)) (M (B g))-sourcePair (A f) (M (G (B g)))
  simp only [sourcePair,map_sub,inner_sub_right] at hG ⊢
  rw [hG]

/-- The exact original coefficients; this polynomial is used on source operators and on their whole polarized responses. -/
def polynomial {V : Type*} [AddCommGroup V] [Module ℂ V]
    (dp dg dc : V →ₗ[ℂ] V) (x : V) : V :=
  let J := dp x-dg x
  let C := dc (dc (dc x))-(6 : ℂ) • dc (dc x)+(8 : ℂ) • dc x
  dg (dg J)-(5 : ℂ) • dg J+(4 : ℂ) • J+
    (vacuumJetCoefficient : ℂ) • (dp (dp C)-(3 : ℂ) • dp C+(2 : ℂ) • C)

private theorem polynomial_source (A : End) :
    polynomial deltaPhi deltaGauge scaleDerivative A=weightedBulkJet A := by
  rw [weightedBulkJet,original_shifted_polynomial]
  simp only [polynomial,mixedPolynomial,affinePolynomial]

private theorem polynomial_map {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (l : V →ₗ[ℂ] W)
    (dp dg dc : V →ₗ[ℂ] V) (ep eg ec : W →ₗ[ℂ] W)
    (hp : ∀ x,l (dp x)=ep (l x)) (hg : ∀ x,l (dg x)=eg (l x)) (hc : ∀ x,l (dc x)=ec (l x)) (x : V) :
    l (polynomial dp dg dc x)=polynomial ep eg ec (l x) := by
  simp only [polynomial,map_add,map_sub,map_smul,hp,hg,hc]

private theorem pair_read_polynomial (f g : QuantumTest) (M : End) :
    pairRead f g (weightedBulkJet M)=
      polynomial (pairDelta Phi) (pairDelta Gauge) (pairDelta Coframe) (pairRead f g M) := by
  rw [←polynomial_source]
  apply polynomial_map (pairRead f g)
  · intro A
    rw [←SourceScalarAffineScaleTransport.generator_commutator]
    exact pair_read_delta Phi phi_pair f g A
  · intro A
    rw [←SourceGaugeScaleTransport.generator_commutator]
    exact pair_read_delta Gauge gauge_pair f g A
  · intro A
    rw [←SourceGaugeCoframeJets.K_commutator]
    exact pair_read_delta Coframe coframe_pair f g A

private theorem core_embed (g : diagonal.domain) : embed (coreEquiv.symm g)=(g : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply g)

def state (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : QuantumTest :=
  coreEquiv.symm (sourceCore F z hz g)

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g : H) := core_embed _

private theorem state_action (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    diagonalAction (state F z hz g)=coreEquiv.symm g+z • state F z hz g+defectAction F (state F z hz g) := by
  apply embed_injective
  have h := source_core_action F z hz g
  change embed (diagonalAction (state F z hz g))=_ at h
  simp only [map_add,map_smul,core_embed,state_embed]
  exact h.trans (congrArg (fun d : H => (g : H)+z • finiteResolvent F z (g : H)+d)
    (actual_source_defect F z hz g).symm)

/-- Every changed source test generates its own full defect and H0 commutator. -/
def raisedDefect (F : Index) (A : End) (q : QuantumTest) : QuantumTest :=
  (diagonalAction*A-A*diagonalAction) q+A (defectAction F q)

private theorem raised_action {V : Type*} [AddCommGroup V] [Module ℂ V]
    (H A : V →ₗ[ℂ] V) (q u d : V) (z : ℂ) (h : H q=u+z • q+d) :
    H (A q)=A u+z • A q+(H (A q)-A (H q)+A d) := by
  rw [h,map_add,map_add,map_smul]
  abel

theorem actual_raised_source (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) (A : End) :
    diagonalAction (A (state F z hz g))=
      A (coreEquiv.symm g)+z • A (state F z hz g)+raisedDefect F A (state F z hz g) := by
  simpa only [raisedDefect,LinearMap.sub_apply,Module.End.mul_apply] using!
    raised_action diagonalAction A (state F z hz g) (coreEquiv.symm g)
      (defectAction F (state F z hz g)) z (state_action F z hz g)

private theorem symmetric_pair_source (f g : QuantumTest) : sourcePair f (symmetricScale g)=
    (1/2 : ℂ)*(sourcePair (diagonalAction f) (volumeAction g)+sourcePair (volumeAction f) (diagonalAction g)) := by
  rw [symmetric_scale_source]
  change sourcePair f ((1/2 : ℂ) • (diagonalAction (volumeAction g)+volumeAction (diagonalAction g)))=_
  simp only [sourcePair,map_smul,map_add,inner_smul_right,inner_add_right]
  change (1/2 : ℂ)*(sourcePair f (diagonalAction (volumeAction g))+sourcePair f (volumeAction (diagonalAction g)))=_
  have hU : sourcePair f (volumeAction (diagonalAction g))=
      sourcePair (volumeAction f) (diagonalAction g) := multiply_pair _ _ _ _
  rw [diagonalAction_pair,hU]
  rfl

/-- Literal polarized Q0 response: both source inputs, the complete complex frequency term, and both raised defects. -/
def resolvedPair (F : Index) (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0)
    (g k : diagonal.domain) : PairMatrix := fun A B =>
  let p := state F zl hl k
  let q := state F zr hr g
  (1/2 : ℂ)*(sourcePair (A (coreEquiv.symm k)) (volumeAction (B q))+
    sourcePair (volumeAction (A p)) (B (coreEquiv.symm g))+
    (star zl+zr)*sourcePair (A p) (volumeAction (B q))+
    sourcePair (raisedDefect F A p) (volumeAction (B q))+
    sourcePair (volumeAction (A p)) (raisedDefect F B q))

theorem actual_symmetric_pair (F : Index) (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0)
    (g k : diagonal.domain) :
    pairRead (state F zl hl k) (state F zr hr g) symmetricScale=resolvedPair F zl zr hl hr g k := by
  ext A B
  change sourcePair (A (state F zl hl k)) (symmetricScale (B (state F zr hr g)))=_
  rw [symmetric_pair_source,actual_raised_source,actual_raised_source]
  simp only [resolvedPair,sourcePair,map_add,map_smul,inner_add_left,inner_add_right,
    inner_smul_left,inner_smul_right,starRingEnd_apply]
  have hU := multiply_pair volume (fun _ => volume_smooth.contDiffAt) (A (state F zl hl k)) (B (state F zr hr g))
  change inner ℂ (embed (A (state F zl hl k))) (embed (volumeAction (B (state F zr hr g))))=
    inner ℂ (embed (volumeAction (A (state F zl hl k)))) (embed (B (state F zr hr g))) at hU
  rw [hU]
  ring

def resolvedBulk (F : Index) (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0)
    (g k : diagonal.domain) : PairMatrix :=
  polynomial (pairDelta Phi) (pairDelta Gauge) (pairDelta Coframe) (resolvedPair F zl zr hl hr g k)

/-- The complete source polynomial lands on the same finite-resolvent pair before any norm or separate leg estimate. -/
theorem actual_positive_bulk_ward (F : Index) (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0)
    (g k : diagonal.domain) (A B : End) :
    sourcePair (A (state F zl hl k)) (volumeAction (positiveBulk (B (state F zr hr g))))=
      resolvedBulk F zl zr hl hr g k A B := by
  have h := pair_read_polynomial (state F zl hl k) (state F zr hr g) symmetricScale
  rw [original_positive_bulk_symmetric_jet,actual_symmetric_pair] at h
  exact congrFun (congrFun h A) B

/-- The same generated signed word controls every localized original scalar70 Gram; no state bound is an input. -/
theorem actual_positive_bulk_gram (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) (A : End) :
    4*sourceTime 0*nativeScalarEnergy (A (state F z hz g)) ≤
      (resolvedBulk F z z hz hz g g A A).re := by
  have h := original_native_bulk_bound (A (state F z hz g))
  rw [weightedBulkForm,original_positive_bulk_symmetric_jet] at h
  exact h.trans_eq (congrArg Complex.re (actual_positive_bulk_ward F z z hz hz g g A A))


/-- The spectral U term has its own source weight; the vacuum completion leaves this exact coefficient. -/
theorem original_volume_polynomial : weightedBulkJet volumeAction=
    (-6*(vacuumJetCoefficient : ℂ)) • volumeAction := by
  have hm : mixedPolynomial volumeAction=0 := by
    simp only [mixedPolynomial,original_volume_phi,original_volume_gauge,sub_self,map_zero,smul_zero,add_zero]
  have hc : shiftedCoframe volumeAction=0 := by
    simp only [shiftedCoframe,LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply,volume_coframe,sub_self]
  have hl : shiftedLocalPolynomial volumeAction=(-3 : ℂ) • volumeAction := by
    simp only [shiftedLocalPolynomial,hc,map_zero,smul_zero,zero_add,zero_sub,neg_smul,neg_zero]
  rw [weightedBulkJet,hm,hl,affinePolynomial]
  simp only [map_smul,original_volume_phi,map_zero,smul_zero,sub_self,zero_add]
  module

private theorem polynomial_add {V : Type*} [AddCommGroup V] [Module ℂ V]
    (dp dg dc : V →ₗ[ℂ] V) (x y : V) :
    polynomial dp dg dc (x+y)=polynomial dp dg dc x+polynomial dp dg dc y := by
  simp only [polynomial,map_add,map_sub,map_smul]
  module
private theorem polynomial_smul {V : Type*} [AddCommGroup V] [Module ℂ V]
    (dp dg dc : V →ₗ[ℂ] V) (c : ℂ) (x : V) :
    polynomial dp dg dc (c • x)=c • polynomial dp dg dc x := by
  simp only [polynomial,map_smul,map_add,map_sub]
  module

/-- Only the original fixed source inputs occur here; their partners remain the exact same finite-resolvent source legs. -/
def fixedPair (F : Index) (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0)
    (g k : diagonal.domain) : PairMatrix := fun A B =>
  (1/2 : ℂ)*(sourcePair (A (coreEquiv.symm k)) (volumeAction (B (state F zr hr g)))+
    sourcePair (volumeAction (A (state F zl hl k))) (B (coreEquiv.symm g)))

/-- Both transformed source defects are retained with their exact signs, including the original grade/input/escape flux. -/
def defectPair (F : Index) (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0)
    (g k : diagonal.domain) : PairMatrix := fun A B =>
  (1/2 : ℂ)*(sourcePair (raisedDefect F A (state F zl hl k)) (volumeAction (B (state F zr hr g)))+
    sourcePair (volumeAction (A (state F zl hl k))) (raisedDefect F B (state F zr hr g)))

private theorem resolved_pair_split (F : Index) (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0)
    (g k : diagonal.domain) : resolvedPair F zl zr hl hr g k=
      fixedPair F zl zr hl hr g k+defectPair F zl zr hl hr g k+
        ((star zl+zr)/2) • pairRead (state F zl hl k) (state F zr hr g) volumeAction := by
  ext A B
  simp only [resolvedPair,fixedPair,defectPair,Pi.add_apply,Pi.smul_apply,pairRead,LinearMap.coe_mk,AddHom.coe_mk,smul_eq_mul]
  ring

def fixedBulk (F : Index) (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0)
    (g k : diagonal.domain) : PairMatrix :=
  polynomial (pairDelta Phi) (pairDelta Gauge) (pairDelta Coframe) (fixedPair F zl zr hl hr g k)
def defectBulk (F : Index) (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0)
    (g k : diagonal.domain) : PairMatrix :=
  polynomial (pairDelta Phi) (pairDelta Gauge) (pairDelta Coframe) (defectPair F zl zr hl hr g k)

/-- Full source normal form. The mixed φ/g frequency term cancels; the exact vacuum frequency term survives. -/
theorem actual_positive_bulk_normal (F : Index) (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0)
    (g k : diagonal.domain) (A B : End) :
    sourcePair (A (state F zl hl k)) (volumeAction (positiveBulk (B (state F zr hr g))))=
      fixedBulk F zl zr hl hr g k A B+defectBulk F zl zr hl hr g k A B-
        (3*(vacuumJetCoefficient : ℂ)*(star zl+zr))*
          sourcePair (A (state F zl hl k)) (volumeAction (B (state F zr hr g))) := by
  have hp := pair_read_polynomial (state F zl hl k) (state F zr hr g) volumeAction
  rw [original_volume_polynomial,map_smul] at hp
  rw [actual_positive_bulk_ward,resolvedBulk,resolved_pair_split,polynomial_add,polynomial_add,polynomial_smul,←hp]
  change fixedBulk F zl zr hl hr g k A B+defectBulk F zl zr hl hr g k A B+
    ((star zl+zr)/2)*((-6*(vacuumJetCoefficient : ℂ))*
      sourcePair (A (state F zl hl k)) (volumeAction (B (state F zr hr g))))=_
  ring

/-- All four actual entries are polarized before taking the positive real form. -/
theorem actual_joint_bulk_ward (F : Index) (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0)
    (g k : diagonal.domain) (A B : End) (a b : ℂ) :
    weightedBulkForm (a • A (state F zl hl k)+b • B (state F zr hr g))=
      (star a*a*resolvedBulk F zl zl hl hl k k A A+
       star a*b*resolvedBulk F zl zr hl hr g k A B+
       star b*a*resolvedBulk F zr zl hr hl k g B A+
       star b*b*resolvedBulk F zr zr hr hr g g B B).re := by
  rw [weightedBulkForm,original_positive_bulk_symmetric_jet]
  simp only [Module.End.mul_apply,map_add,map_smul,sourcePair,inner_add_left,inner_add_right,
    inner_smul_left,inner_smul_right,starRingEnd_apply]
  have hAA := actual_positive_bulk_ward F zl zl hl hl k k A A
  have hAB := actual_positive_bulk_ward F zl zr hl hr g k A B
  have hBA := actual_positive_bulk_ward F zr zl hr hl k g B A
  have hBB := actual_positive_bulk_ward F zr zr hr hr g g B B
  simp only [sourcePair] at hAA hAB hBA hBB
  rw [hAA,hAB,hBA,hBB]
  congr 1
  ring

/-- Complete same-F native70 Gram, with complex left/right crosses and all generated source defects. -/
theorem actual_joint_native_ward (F : Index) (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0)
    (g k : diagonal.domain) (A B : End) (a b : ℂ) :
    4*sourceTime 0*(∑ i : ScalarIndex,
      ‖a • embed (covariantMomentum (scalarDirection i) (A (state F zl hl k)))+
       b • embed (covariantMomentum (scalarDirection i) (B (state F zr hr g)))‖^2) ≤
      (star a*a*resolvedBulk F zl zl hl hl k k A A+
       star a*b*resolvedBulk F zl zr hl hr g k A B+
       star b*a*resolvedBulk F zr zl hr hl k g B A+
       star b*b*resolvedBulk F zr zr hr hr g g B B).re := by
  have h := original_native_bulk_bound (a • A (state F zl hl k)+b • B (state F zr hr g))
  rw [actual_joint_bulk_ward] at h
  simpa only [nativeScalarEnergy,map_add,map_smul] using! h


/-- Direct consumer of the original joint Γ native cost: the full polarized source word bounds the same signed cost with both actual d_F inputs. -/
theorem actual_joint_signed_cost_ward (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) (a b : ℂ) :
    let hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
    4*sourceTime 0*signedNativeCost F z hz g k a b ≤
      (star a*a*resolvedBulk F (star z) (star z) hs hs k k 1 1+
       star a*b*resolvedBulk F (star z) z hs hz g k 1 1+
       star b*a*resolvedBulk F z (star z) hz hs k g 1 1+
       star b*b*resolvedBulk F z z hz hz g g 1 1).re := by
  intro hs
  have h := original_native_bulk_bound (jointState F z hz g k a b)
  rw [←actual_joint_native_cost] at h
  have he := actual_joint_bulk_ward F (star z) z hs hz g k 1 1 a b
  change weightedBulkForm (jointState F z hz g k a b)=_ at he
  exact h.trans_eq he

end LowEnergy.SourceScalarPositiveBulkWard
