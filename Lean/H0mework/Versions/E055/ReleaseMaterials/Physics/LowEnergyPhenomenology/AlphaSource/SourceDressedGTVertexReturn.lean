import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceDressedGTSampleWard
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPhysicalWard
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstFourPointTransfer

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalDressedGTVertexReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalDressedSpinChargeReturn PreparationPhysicalFirstPoleGaugeVertex
open PreparationPhysicalFirstGaugeBackgroundReturn PreparationPhysicalFirstGaugeMaterialDifference
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates GaussCoreHilbert GaussCoreDifferential GaussFockLift
open GaussQuantumMultiplier GaussDensityCore GaussFockPair
open PreparationVacuumSourceActionJets PreparationVacuumActionDecomposition
open PreparationVacuumActionFieldLift PreparationVacuumSourceFieldFamily
open PreparationVacuumFieldConstraintResponse PreparationVacuumFieldCovector
open PreparationVacuumFullFieldRiesz PreparationVacuumMixedFieldReturn
open PreparationVacuumSourcePreparedResponse PreparationVacuumSourceFieldFamily
open CanonicalGradedSpatialSource CanonicalPhysicalYResolvent
open GaussComposite GaussComposite.SourceGraph MeasureTheory Filter
open GaussUnitaryHistory (Index)
open scoped BigOperators InnerProductSpace ContDiff Topology
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
local instance : NormedAlgebra ℝ FiberOp:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _

/-- The first-jet primitive consists of computed native connections and the actual mother/Y variations. -/
def sourceGTFieldForm (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (r : ℝ) : ℂ :=
  (∫z,sourceGTNativeSample a b z (fieldCoordinateCurve f r z) ∂GaussHistoryHilbert.configurationMeasure)+
  Complex.I*(∫z,pairSample (fieldCoordinateCurve f r z) (a z)
    (quantizer (symbolFirst p (sourceState (fieldCoordinateCurve f r z))
      (sourceFirstGaugeState (sourceState (fieldCoordinateCurve f r z)))) (b z)) ∂GaussHistoryHilbert.configurationMeasure)-
  Complex.I*(∫z,pairSample (fieldCoordinateCurve f r z) (a z)
    (sourceGTRetained (fieldCoordinateCurve f r z) (b z)) ∂GaussHistoryHilbert.configurationMeasure)

def sourceGTCurrentCore (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) : ℂ :=
  deriv (sourceGTFieldForm f p a b) 0

/-- This is the actual source-test approximation, not the physical-basis compression used by another response. -/
def sourceGTFrameDifference (F : Index) (x : H) : QuantumTest :=
  sourceTestApprox F (sourceFirstCharge x)-sourceFirstChargeCore (sourceTestApprox F x)

/-- The two original frames supply independent input and output corrections. -/
def sourceGTCurrentRead (f : Field289) (p : PhysicalMomentum) (F : Index) (x y : H) : ℂ :=
  sourceGTCurrentCore f p (sourceTestApprox F x) (sourceTestApprox F y)+
    (fieldJets f p (sourceTestApprox F x) (sourceGTFrameDifference F y)).first 0-
    (fieldJets f p (sourceGTFrameDifference F x) (sourceTestApprox F y)).first 0

private abbrev qFiber : FiberOp:=quantized sourceFirstChargeMatrix

private theorem core_ext (A B : H→L[ℂ]H) (same : ∀a : QuantumTest,A (embed a)=B (embed a)) : A=B := by
  apply ContinuousLinearMap.ext
  intro x
  have core : (GaussCoreHilbert.Core:Set H)⊆{x|A x=B x} := by
    intro x hx
    obtain ⟨a,ha⟩:=embed_surjective_core ⟨x,hx⟩
    change A x=B x
    change embed a=x at ha
    rw [←ha]
    exact same a
  exact closure_minimal core (isClosed_eq A.continuous B.continuous)
    (GaussHistoryHilbert.fockTestDomain_dense x)

/-- The normalized scalar Yukawa orbit, before completion on the actual configuration measure. -/
def sourceGTBoundedFiber (z : SourceCoordinateSlice) : FiberOp :=
  Complex.I • sourceGTYukawa (GaussYukawaCoefficient.normalizedScalar z)

private theorem bounded_fiber_source (z : SourceCoordinateSlice) :
    GaussYukawaCoefficient.normalized z*qFiber-qFiber*GaussYukawaCoefficient.normalized z=
      sourceGTBoundedFiber z := sourceGTYukawa_generated (GaussYukawaCoefficient.normalizedScalar z)

private theorem bounded_fiber_smooth (z : GaussHistoryHilbert.physicalChart) :
    ContDiffAt ℝ ∞ sourceGTBoundedFiber z.val := by
  have same : sourceGTBoundedFiber=fun z=>
      GaussYukawaCoefficient.normalized z*qFiber-qFiber*GaussYukawaCoefficient.normalized z :=
    funext (fun z=>(bounded_fiber_source z).symm)
  rw [same]
  exact ((GaussYukawaCoefficient.normalized_smooth.mul contDiff_const).sub
    (contDiff_const.mul GaussYukawaCoefficient.normalized_smooth)).contDiffAt

private theorem bounded_fiber_price (z : SourceCoordinateSlice) (v : FockFiber) :
    ‖sourceGTBoundedFiber z v‖≤(2*‖qFiber‖*GaussYukawaCoefficient.bound)*‖v‖ := by
  rw [←bounded_fiber_source]
  apply (ContinuousLinearMap.le_opNorm _ v).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
  calc
    ‖GaussYukawaCoefficient.normalized z*qFiber-qFiber*GaussYukawaCoefficient.normalized z‖≤
        ‖GaussYukawaCoefficient.normalized z*qFiber‖+‖qFiber*GaussYukawaCoefficient.normalized z‖ := norm_sub_le _ _
    _≤‖GaussYukawaCoefficient.normalized z‖*‖qFiber‖+‖qFiber‖*‖GaussYukawaCoefficient.normalized z‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _=2*‖qFiber‖*‖GaussYukawaCoefficient.normalized z‖ := by ring
    _≤_ := mul_le_mul_of_nonneg_left ((GaussYukawaCoefficient.normalized z).opNorm_le_bound
      GaussYukawaCoefficient.bound_nonneg (GaussYukawaCoefficient.normalized_bound z)) (by positivity)

def sourceGTBoundedY : H→L[ℂ]H :=
  GaussBoundedMultiplier.extension sourceGTBoundedFiber bounded_fiber_smooth
    (fun z c=>(GaussQuantumMultiplier.weight_commute c
      (GaussYukawaCoefficient.fullMatrix (SourceQuantumScalarChart.action
        (GaussYukawaCoefficient.normalizedScalar z) sourceFirstTemporalLie))).smul_right Complex.I)
    (2*‖qFiber‖*GaussYukawaCoefficient.bound)
    (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg qFiber)) GaussYukawaCoefficient.bound_nonneg)
    (fun z v=>bounded_fiber_price z.val v)

private theorem boundedY_core (a : QuantumTest) : sourceGTBoundedY (embed a)=
    embed (localMultiplier sourceGTBoundedFiber bounded_fiber_smooth a) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ a

theorem sourceGTBoundedY_generated :
    GaussYukawaOperator.bounded*sourceFirstCharge-sourceFirstCharge*GaussYukawaOperator.bounded=sourceGTBoundedY := by
  apply core_ext
  intro a
  simp only [sub_apply,mul_apply_eq_comp,sourceFirstChargeCore_embed,GaussYukawaOperator.bounded_core,boundedY_core]
  rw [←map_sub]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  exact congrArg (fun T : FiberOp=>T (a z)) (bounded_fiber_source z)

private theorem inverse_radius_charge :
    GaussRadialDomain.inverseRadius*sourceFirstCharge=sourceFirstCharge*GaussRadialDomain.inverseRadius := by
  apply core_ext
  intro a
  simp only [mul_apply_eq_comp,sourceFirstChargeCore_embed,GaussRadialDomain.inverse_core]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  exact (map_smul qFiber (GaussRadialDomain.reciprocal z:ℂ) (a z)).symm

attribute [local irreducible] sourceGTBoundedY GaussYukawaOperator.bounded
  GaussRadialDomain.inverseRadius sourceFirstCharge

/-- The original cutoff recurrence acts on the computed Yukawa orbit, at the same cutoff index. -/
def sourceGTCutoff : ℕ→H→L[ℂ]H
  | 0=>sourceGTBoundedY
  | n+1=>sourceGTBoundedY+(1-GaussRadialDomain.inverseRadius)*sourceGTCutoff n

theorem sourceGTCutoff_generated (n : ℕ) :
    FullYSourceCutoffVolterra.cutoff n*sourceFirstCharge-sourceFirstCharge*FullYSourceCutoffVolterra.cutoff n=
      sourceGTCutoff n := by
  have algebra {T : Type} [Ring T] (B R Y Q : T) (commute : R*Q=Q*R) :
      (B+(1-R)*Y)*Q-Q*(B+(1-R)*Y)=
      (B*Q-Q*B)+(1-R)*(Y*Q-Q*Y) := by
    simp only [add_mul,mul_add,sub_mul,mul_sub,one_mul,←mul_assoc]
    rw [commute]
    abel
  induction n with
  | zero=>exact sourceGTBoundedY_generated
  | succ n ih=>
    change (GaussYukawaOperator.bounded+(1-GaussRadialDomain.inverseRadius)*FullYSourceCutoffVolterra.cutoff n)*sourceFirstCharge-
      sourceFirstCharge*(GaussYukawaOperator.bounded+(1-GaussRadialDomain.inverseRadius)*FullYSourceCutoffVolterra.cutoff n)=
      sourceGTBoundedY+(1-GaussRadialDomain.inverseRadius)*sourceGTCutoff n
    exact (algebra (T:=H→L[ℂ]H) GaussYukawaOperator.bounded GaussRadialDomain.inverseRadius
      (FullYSourceCutoffVolterra.cutoff n) sourceFirstCharge inverse_radius_charge).trans
      (congrArg₂ (fun X Y : H→L[ℂ]H=>X+(1-GaussRadialDomain.inverseRadius)*Y)
        sourceGTBoundedY_generated ih)

/-- Only the original C uses its physical frame. The current reader still uses its separate sourceTestApprox frame. -/
def sourceGTCompressionInsertion (p : PhysicalMomentum) (F : Index) : H→L[ℂ]H :=
  PreparationPhysicalFirstChargeFourPointReturn.sourceFirstFrameInsertion p F
    (fun i j=>PreparationVacuumGradedTransport.transportedForm 0 p
      (PreparationVacuumGradedTransport.bareTest p F i) (PreparationVacuumGradedTransport.bareTest p F j) 0)

theorem sourceGTCompressionInsertion_generated (p : PhysicalMomentum) (F : Index) :
    CanonicalPhysicalSpatial.compression p F*sourceFirstCharge-sourceFirstCharge*CanonicalPhysicalSpatial.compression p F=
      sourceGTCompressionInsertion p F := by
  rw [←PreparationVacuumGradedTransport.transportedCompression_zero 0 p F]
  exact PreparationPhysicalFirstChargeFourPointReturn.sourceFirstFrameInsertion_generated p F _

/-- Actual two-sided material insertion: original physical frame plus the source-generated Yukawa recurrence. -/
def sourceGTMaterialInsertion (p : PhysicalMomentum) (F : Index) (n : ℕ) : H→L[ℂ]H :=
  sourceGTCompressionInsertion p F+sourceGTCutoff n

theorem sourceGTMaterialInsertion_generated (p : PhysicalMomentum) (F : Index) (n : ℕ) :
    (CanonicalPhysicalSpatial.compression p F+FullYSourceCutoffVolterra.cutoff n)*sourceFirstCharge-
      sourceFirstCharge*(CanonicalPhysicalSpatial.compression p F+FullYSourceCutoffVolterra.cutoff n)=
      sourceGTMaterialInsertion p F n := by
  have algebra (A B Q : H→L[ℂ]H) : (A+B)*Q-Q*(A+B)=(A*Q-Q*A)+(B*Q-Q*B) := by noncomm_ring
  rw [algebra,sourceGTCompressionInsertion_generated,sourceGTCutoff_generated]
  rfl


private theorem native_integrable (f : Field289) (a b : QuantumTest) :
    ∀ᶠr in 𝓝 (0:ℝ),Integrable (fun z=>nativeSample a b z (fieldCoordinateCurve f r z))
      GaussHistoryHilbert.configurationMeasure :=
  fieldSample_integrable (nativeSample a b) f a
    (fun r z hz hx=>nativeSample_param a b (fun u : Parameter=>fieldCoordinateCurve f u.1 u.2) Prod.snd
      (r,z) hx (field_curve_smooth f r ⟨z,hz⟩) contDiffAt_snd) (nativeSample_zero_outside a b)

private theorem fiber_integrable (f : Field289) (A : SourceCoordinateSlice→PreparationVacuumSourceFieldFamily.FiberMap)
    (hA : ∀x : GaussHistoryHilbert.physicalChart,ContDiffAt ℝ ∞ A x.val) (a b : QuantumTest) :
    ∀ᶠr in 𝓝 (0:ℝ),Integrable (fun z=>fiberSample A a b z (fieldCoordinateCurve f r z))
      GaussHistoryHilbert.configurationMeasure :=
  fieldSample_integrable (fiberSample A a b) f a
    (fun r z hz hx=>fiberSample_param A hA a b (fun u : Parameter=>fieldCoordinateCurve f u.1 u.2) Prod.snd
      (r,z) hx (field_curve_smooth f r ⟨z,hz⟩) contDiffAt_snd) (fiberSample_zero_outside A a b)

private theorem retained_sample (a b : QuantumTest) (z : SourceCoordinateSlice)
    (x : GaussHistoryHilbert.physicalChart) :
    fiberSample retainedCoefficient a (sourceFirstChargeCore b) z x.val-
      fiberSample retainedCoefficient (sourceFirstChargeCore a) b z x.val=
      Complex.I*pairSample x.val (a z) (sourceGTRetained x.val (b z)) := by
  change pairSample x.val (a z) (retainedCoefficient x.val (quantized sourceFirstChargeMatrix (b z)))-
    pairSample x.val (quantized sourceFirstChargeMatrix (a z)) (retainedCoefficient x.val (b z))=_
  rw [←sourceGTDensity_pair]
  have generated:=congrArg (fun A : FiberOp=>pairSample x.val (a z) (A (b z))) (sourceGTRetained_generated x)
  have subPair (u v w : FockFiber) : pairSample x.val u (v-w)=
      pairSample x.val u v-pairSample x.val u w := by
    simp only [pairSample,PiLp.sub_apply,mul_sub,Finset.sum_sub_distrib]
  simpa only [sub_apply,mul_apply_eq_comp,smul_apply,subPair,pairSample_smul_right] using generated

/-- A genuine configuration-integral germ; the primitive contains no target commutator. -/
theorem sourceGTFieldForm_generated (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    (fun r=>fieldForm f p a (sourceFirstChargeCore b) r-fieldForm f p (sourceFirstChargeCore a) b r)=ᶠ[𝓝 (0:ℝ)]
      sourceGTFieldForm f p a b := by
  have near : ∀ᶠr in 𝓝 (0:ℝ),|r|<fieldRadius f a :=
    (continuous_abs.tendsto 0).eventually (gt_mem_nhds (by simpa using fieldRadius_positive f a))
  filter_upwards [near,native_integrable f a (sourceFirstChargeCore b),
    native_integrable f (sourceFirstChargeCore a) b,
    fiber_integrable f (actualFiber p) (actualFiber_smooth p) a (sourceFirstChargeCore b),
    fiber_integrable f (actualFiber p) (actualFiber_smooth p) (sourceFirstChargeCore a) b,
    fiber_integrable f retainedCoefficient retainedCoefficient_smooth a (sourceFirstChargeCore b),
    fiber_integrable f retainedCoefficient retainedCoefficient_smooth (sourceFirstChargeCore a) b] with r hr hnL hnR hmL hmR hyL hyR
  have native : nativeFieldForm f a (sourceFirstChargeCore b) r-
      nativeFieldForm f (sourceFirstChargeCore a) b r=
      ∫z,sourceGTNativeSample a b z (fieldCoordinateCurve f r z) ∂GaussHistoryHilbert.configurationMeasure := by
    rw [nativeFieldForm,nativeFieldForm,←integral_sub hnL hnR]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z=>sourceGTNativeSample_generated a b z _)
  have matter : fiberFieldForm f (actualFiber p) a (sourceFirstChargeCore b) r-
      fiberFieldForm f (actualFiber p) (sourceFirstChargeCore a) b r=
      Complex.I*(∫z,pairSample (fieldCoordinateCurve f r z) (a z)
        (quantizer (symbolFirst p (sourceState (fieldCoordinateCurve f r z))
          (sourceFirstGaugeState (sourceState (fieldCoordinateCurve f r z)))) (b z))
        ∂GaussHistoryHilbert.configurationMeasure) := by
    rw [fiberFieldForm,fiberFieldForm,←integral_sub hmL hmR,←integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    by_cases inside : z∈tsupport a
    · exact sourceGTActualSample p a b z ⟨_,fieldRadius_chart f a r z hr.le inside⟩
    · have zero:=image_eq_zero_of_notMem_tsupport inside
      change pairSample (fieldCoordinateCurve f r z) (a z)
        (actualFiber p (fieldCoordinateCurve f r z) (quantized sourceFirstChargeMatrix (b z)))-
        pairSample (fieldCoordinateCurve f r z) (quantized sourceFirstChargeMatrix (a z))
          (actualFiber p (fieldCoordinateCurve f r z) (b z))=_
      simp only [zero,map_zero,pairSample_zero_left,mul_zero,sub_self]
  have retained : fiberFieldForm f retainedCoefficient a (sourceFirstChargeCore b) r-
      fiberFieldForm f retainedCoefficient (sourceFirstChargeCore a) b r=
      Complex.I*(∫z,pairSample (fieldCoordinateCurve f r z) (a z)
        (sourceGTRetained (fieldCoordinateCurve f r z) (b z)) ∂GaussHistoryHilbert.configurationMeasure) := by
    rw [fiberFieldForm,fiberFieldForm,←integral_sub hyL hyR,←integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    by_cases inside : z∈tsupport a
    · exact retained_sample a b z ⟨_,fieldRadius_chart f a r z hr.le inside⟩
    · have zero:=image_eq_zero_of_notMem_tsupport inside
      change pairSample (fieldCoordinateCurve f r z) (a z)
        (retainedCoefficient (fieldCoordinateCurve f r z) (quantized sourceFirstChargeMatrix (b z)))-
        pairSample (fieldCoordinateCurve f r z) (quantized sourceFirstChargeMatrix (a z))
          (retainedCoefficient (fieldCoordinateCurve f r z) (b z))=_
      simp only [zero,map_zero,pairSample_zero_left,mul_zero,sub_self]
  simp only [fieldForm,sourceGTFieldForm,sourceGTCoframeForm]
  linear_combination native+matter-retained

theorem sourceGTCurrentCore_generated (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    sourceGTCurrentCore f p a b=
      (fieldJets f p a (sourceFirstChargeCore b)).first 0-
        (fieldJets f p (sourceFirstChargeCore a) b).first 0 := by
  have derivative:=((fieldJets f p a (sourceFirstChargeCore b)).actual.1).sub
    ((fieldJets f p (sourceFirstChargeCore a) b).actual.1)
  exact (derivative.congr_of_eventuallyEq (sourceGTFieldForm_generated f p a b).symm).deriv

private theorem first_add_left (f : Field289) (p : PhysicalMomentum) (a b c : QuantumTest) :
    (fieldJets f p (a+b) c).first 0=(fieldJets f p a c).first 0+(fieldJets f p b c).first 0 :=
  ((fieldJets f p (a+b) c).actual.1).unique
    ((((fieldJets f p a c).actual.1).add (fieldJets f p b c).actual.1).congr_of_eventuallyEq
      ((fieldForm_sesq f p).add_left a b c))

private theorem first_add_right (f : Field289) (p : PhysicalMomentum) (a b c : QuantumTest) :
    (fieldJets f p a (b+c)).first 0=(fieldJets f p a b).first 0+(fieldJets f p a c).first 0 :=
  ((fieldJets f p a (b+c)).actual.1).unique
    ((((fieldJets f p a b).actual.1).add (fieldJets f p a c).actual.1).congr_of_eventuallyEq
      ((fieldForm_sesq f p).add_right a b c))

/-- The computed integral derivative enters the actual finite Riesz reader, with both original frame errors. -/
theorem sourceGTCurrentRead_generated (f : Field289) (p : PhysicalMomentum) (F : Index) (x y : H) :
    inner ℂ x ((currentRestriction f p F 0*sourceFirstCharge-
      sourceFirstCharge*currentRestriction f p F 0) y)=sourceGTCurrentRead f p F x y := by
  simp only [sub_apply,mul_apply_eq_comp,inner_sub_right]
  rw [←sourceFirstCharge_pair,currentRestriction_original_pair,currentRestriction_original_pair]
  have frame (v : H) : sourceTestApprox F (sourceFirstCharge v)=
      sourceFirstChargeCore (sourceTestApprox F v)+sourceGTFrameDifference F v := by
    unfold sourceGTFrameDifference
    abel
  rw [frame x,frame y,first_add_left,first_add_right]
  unfold sourceGTCurrentRead
  rw [sourceGTCurrentCore_generated]
  ring

private theorem inverse_charge (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (hz : z.im≠0) :
    finiteFull p F n z*sourceFirstCharge-sourceFirstCharge*finiteFull p F n z=
      -(finiteFull p F n z*sourceGTMaterialInsertion p F n*finiteFull p F n z) := by
  let A:=CanonicalPhysicalSpatial.compression p F+FullYSourceCutoffVolterra.cutoff n-z • (1:H→L[ℂ]H)
  let G:=finiteFull p F n z
  have left : G*A=1:=finiteFull_left p F n z hz
  have right : A*G=1:=finiteFull_right p F n z hz
  have shift : A*sourceFirstCharge-sourceFirstCharge*A=sourceGTMaterialInsertion p F n := by
    dsimp [A]
    have generated:=sourceGTMaterialInsertion_generated p F n
    simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
    calc
      _=(CanonicalPhysicalSpatial.compression p F+FullYSourceCutoffVolterra.cutoff n)*sourceFirstCharge-
          sourceFirstCharge*(CanonicalPhysicalSpatial.compression p F+FullYSourceCutoffVolterra.cutoff n) := by abel
      _=sourceGTMaterialInsertion p F n := generated
  calc
    _=G*sourceFirstCharge*(A*G)-(G*A)*sourceFirstCharge*G := by rw [left,right,mul_one,one_mul]
    _= -(G*(A*sourceFirstCharge-sourceFirstCharge*A)*G) := by
      simp only [mul_sub,sub_mul,neg_sub,mul_assoc]
    _=_ := by rw [shift]

attribute [local irreducible] finiteFull currentRestriction sourceGTMaterialInsertion

/-- All three internal variations use the original two inverses; the middle term is the computed full-source integral. -/
def sourceGTVertexRead (f : Field289) (p k : PhysicalMomentum) (F : Index) (n : ℕ)
    (z w : ℂ) (x y : H) : ℂ :=
  sourceGTCurrentRead f p F ((finiteFull (p+k) F n z).adjoint x) (finiteFull p F n w y)-
    inner ℂ x ((finiteFull (p+k) F n z*sourceGTMaterialInsertion (p+k) F n*
      currentVertex f p k F n z w) y)-
    inner ℂ x ((currentVertex f p k F n z w*sourceGTMaterialInsertion p F n*
      finiteFull p F n w) y)

theorem sourceGTVertexRead_generated (f : Field289) (p k : PhysicalMomentum) (F : Index) (n : ℕ)
    (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) (x y : H) :
    inner ℂ x ((currentVertex f p k F n z w*sourceFirstCharge-
      sourceFirstCharge*currentVertex f p k F n z w) y)=sourceGTVertexRead f p k F n z w x y := by
  have product {T : Type} [Ring T] (A B C Q : T) :
      (A*B*C)*Q-Q*(A*B*C)=(A*Q-Q*A)*B*C+A*(B*Q-Q*B)*C+A*B*(C*Q-Q*C) := by
    simp only [sub_mul,mul_sub,mul_assoc]
    abel
  have expanded:=product (T:=H→L[ℂ]H) (finiteFull (p+k) F n z)
    (currentRestriction f p F 0) (finiteFull p F n w) sourceFirstCharge
  have left:=inverse_charge (p+k) F n z hz
  have right:=inverse_charge p F n w hw
  have full:=expanded.trans (congrArg₂ (fun L R : H→L[ℂ]H=>
    L*currentRestriction f p F 0*finiteFull p F n w+
      finiteFull (p+k) F n z*(currentRestriction f p F 0*sourceFirstCharge-
        sourceFirstCharge*currentRestriction f p F 0)*finiteFull p F n w+
      finiteFull (p+k) F n z*currentRestriction f p F 0*R) left right)
  have read:=congrArg (fun T : H→L[ℂ]H=>inner ℂ x (T y)) full
  apply read.trans
  have middle:=sourceGTCurrentRead_generated f p F ((finiteFull (p+k) F n z).adjoint x)
    (finiteFull p F n w y)
  rw [(finiteFull (p+k) F n z).adjoint_inner_left] at middle
  unfold sourceGTVertexRead currentVertex
  simp only [add_apply,neg_apply,mul_apply_eq_comp,map_neg,inner_add_right,inner_neg_right] at middle ⊢
  rw [middle]
  ring

/-- The already generated endpoint characters and the actual internal GT response share one source-prepared observable. -/
def sourceDressedCompleteGTRead (epsilon : ℝ) (precision : 0<epsilon) (f : Field289)
    (p k : PhysicalMomentum) (F : Index) (n : ℕ) (z w : ℂ)
    (left right : Bool) (a s b t : Fin 2) : ℂ :=
  (star (sourceDressedCharacter left)+sourceDressedCharacter right)*
    preparedCurrent epsilon precision f p k F n z w left right a s b t-
  Complex.I*sourceGTVertexRead f p k F n z w
    (completedLeg left a s (sourceProfile epsilon precision))
    (completedLeg right b t (sourceProfile epsilon precision))

theorem sourceDressedCompleteGT_generated (epsilon : ℝ) (precision : 0<epsilon) (i : Fin 289)
    (p k : PhysicalMomentum) (F : Index) (n : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (left right : Bool) (a s b t : Fin 2) :
    sourceDressedPreparedCovector epsilon precision p k F n z w left right a s b t i-
      Complex.I*inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
        ((currentVertex (fieldBasis i) p k F n z w*sourceFirstCharge-
          sourceFirstCharge*currentVertex (fieldBasis i) p k F n z w)
          (completedLeg right b t (sourceProfile epsilon precision)))=
    sourceDressedCompleteGTRead epsilon precision (fieldBasis i) p k F n z w left right a s b t := by
  rw [sourceDressedPrepared_return,sourceGTVertexRead_generated (fieldBasis i) p k F n z w hz hw]
  rfl

/-- The original finite reader and full-Y prices bound the complete internal return without separating unpriced integrals. -/
theorem sourceGTVertexRead_price (f : Field289) (p k : PhysicalMomentum) (F : Index) (n : ℕ)
    (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) (x y : H) :
    ‖sourceGTVertexRead f p k F n z w x y‖≤
      ‖x‖*(2*‖sourceFirstCharge‖*(normBound n z*currentPrice f p F*normBound n w))*‖y‖ := by
  rw [←sourceGTVertexRead_generated f p k F n z w hz hw]
  apply vertex_pair_price
  have original:=currentVertex_price f p k F n z w hz hw
  calc
    ‖currentVertex f p k F n z w*sourceFirstCharge-sourceFirstCharge*currentVertex f p k F n z w‖≤
        ‖currentVertex f p k F n z w*sourceFirstCharge‖+‖sourceFirstCharge*currentVertex f p k F n z w‖ := norm_sub_le _ _
    _≤‖currentVertex f p k F n z w‖*‖sourceFirstCharge‖+‖sourceFirstCharge‖*‖currentVertex f p k F n z w‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _=2*‖sourceFirstCharge‖*‖currentVertex f p k F n z w‖ := by ring
    _≤_ := mul_le_mul_of_nonneg_left original (by positivity)

theorem sourceDressedCompleteGT_price (epsilon : ℝ) (precision : 0<epsilon) (f : Field289)
    (p k : PhysicalMomentum) (F : Index) (n : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (left right : Bool) (a s b t : Fin 2) :
    ‖sourceDressedCompleteGTRead epsilon precision f p k F n z w left right a s b t‖≤
      (‖star (sourceDressedCharacter left)+sourceDressedCharacter right‖+2*‖sourceFirstCharge‖)*
        (‖completedLeg left a s (sourceProfile epsilon precision)‖*
          (normBound n z*currentPrice f p F*normBound n w)*
          ‖completedLeg right b t (sourceProfile epsilon precision)‖) := by
  have current:=preparedCurrent_price epsilon precision f p k F n z w hz hw left right a s b t
  have internal:=sourceGTVertexRead_price f p k F n z w hz hw
    (completedLeg left a s (sourceProfile epsilon precision))
    (completedLeg right b t (sourceProfile epsilon precision))
  unfold sourceDressedCompleteGTRead
  apply (norm_sub_le _ _).trans
  rw [norm_mul,norm_mul,Complex.norm_I,one_mul]
  calc
    _≤‖star (sourceDressedCharacter left)+sourceDressedCharacter right‖*
        (‖completedLeg left a s (sourceProfile epsilon precision)‖*
          (normBound n z*currentPrice f p F*normBound n w)*
          ‖completedLeg right b t (sourceProfile epsilon precision)‖)+
      ‖completedLeg left a s (sourceProfile epsilon precision)‖*
        (2*‖sourceFirstCharge‖*(normBound n z*currentPrice f p F*normBound n w))*
          ‖completedLeg right b t (sourceProfile epsilon precision)‖ :=
      add_le_add (mul_le_mul_of_nonneg_left current (norm_nonneg _)) internal
    _=_ := by ring

/-- The actual two resolved source legs consume the mixed mother Ward, with the complete density and complementary field terms visible. -/
theorem sourceGTPreparedMixed_balance (epsilon : ℝ) (precision : 0<epsilon) (f : Field289)
    (p k : PhysicalMomentum) (F : Index) (n : ℕ) (z w : ℂ)
    (left right : Bool) (a s b t : Fin 2) (x : GaussHistoryHilbert.physicalChart) :
    let l:=sourceTestApprox F ((finiteFull (p+k) F n z).adjoint
      (completedLeg left a s (sourceProfile epsilon precision)))
    let r:=sourceTestApprox F (finiteFull p F n w (completedLeg right b t (sourceProfile epsilon precision)))
    sampleCurrent (fiberSample (actualFiber p) l (sourceFirstChargeCore r)) f x.val-
      sampleCurrent (fiberSample (actualFiber p) (sourceFirstChargeCore l) r) f x.val+
      (pairSample x.val (l x.val)
        (quantizer (symbolFirst p (sourceState x.val) (complement f x.val)) (sourceFirstChargeCore r x.val))-
      pairSample x.val (sourceFirstChargeCore l x.val)
        (quantizer (symbolFirst p (sourceState x.val) (complement f x.val)) (r x.val)))=
      densityCurrent f p l (sourceFirstChargeCore r) x.val-
      densityCurrent f p (sourceFirstChargeCore l) r x.val+
      Complex.I*pairSample x.val (l x.val)
        (quantizer (sourceFirstBackgroundMixed p (sourceState x.val) f) (r x.val)) := by
  dsimp only
  let l:=sourceTestApprox F ((finiteFull (p+k) F n z).adjoint
    (completedLeg left a s (sourceProfile epsilon precision)))
  let r:=sourceTestApprox F (finiteFull p F n w (completedLeg right b t (sourceProfile epsilon precision)))
  have first:=fiber_sample_mother_balance f p l (sourceFirstChargeCore r) x
  have second:=fiber_sample_mother_balance f p (sourceFirstChargeCore l) r x
  have mixed:=congrArg (fun T : FiberOp=>pairSample x.val (l x.val) (T (r x.val)))
    (sourceGTMixedFiber_generated p x f)
  simp only [sub_apply,mul_apply_eq_comp,smul_apply,pairSample_smul_right] at mixed
  have pairing : pairSample x.val (l x.val)
      (fiberFamily f p x.val (sourceFirstChargeCore r x.val))-
      pairSample x.val (sourceFirstChargeCore l x.val) (fiberFamily f p x.val (r x.val))=
      -Complex.I*pairSample x.val (l x.val)
        (quantizer (sourceFirstBackgroundMixed p (sourceState x.val) f) (r x.val)) := by
    change pairSample _ _ (fiberFamily f p x.val (qFiber (r x.val)))-
      pairSample _ (qFiber (l x.val)) (fiberFamily f p x.val (r x.val))=_
    rw [←sourceGTDensity_pair]
    simpa only [pairSample,PiLp.sub_apply,mul_sub,Finset.sum_sub_distrib] using mixed
  linear_combination first-second-pairing

end LowEnergy.PreparationPhysicalDressedGTVertexReturn
