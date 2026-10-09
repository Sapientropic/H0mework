import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMOriginFields
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstGaugeCurrentWard
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceJointPhaseAction
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceModeContactRead

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMOriginWard
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalNormalizedFullField PreparationVacuumNativeFieldInjection
open PreparationVacuumNativeLocalWard PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumLowerClassical PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift
open PreparationVacuumOriginalGreenFeedback PreparationVacuumGaugeSourceInjection PreparationVacuumActualFieldQuantization
open SourceQuantumScalarChart SourceQuantumFockGauge SourceQuantumConfigurationHilbert GaussNativeMatter GaussHistoryHilbert GaussQuantumMultiplier
open StageNineHolonomicField StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource ProofFreeRicherAnholonomicSource
open StageNineP286InfinitesimalGaugeTransformation StageNineCoframeGravityGaugeRegularity
open StageNineP286GaugeAuxiliaryVariation StageNineP286BracketCalculus
open StageNineP286GaugeConnectionVariation StageNineCompactSupportIntegrationByParts
open SU7MotherLieAlgebra SU7MotherGaugeTheory DiracExteriorMatterAction StageNineDiracDualYukawaSpinJurisdiction DiracCliffordRepresentation
open Stage9C.Material.SpinPair FullQuantum.CoframeResponse FullQuantum.StateGreen
open PointwiseLorentzianCoframeJet PointwiseDiracSpinConnectionLift
open PreparationPhysicalPhaseGaugeRealization PreparationPhysicalJointEMCouplingUnitReturn
open ActualEMCompleteOrbit PhysicalEMGaugeRealization PreparationPhysicalNativePoleChargeReturn
open PreparationVacuumPhysicalModeContact PreparationVacuumRestModeCoupling
open Filter Set
open scoped BigOperators Matrix Topology ContDiff Matrix.Norms.L2Operator
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

/-- The gauge generator is the exact source EM element, on the full original carrier. -/
theorem em_joint_generator_original : sourceJointGenerator=emGaugeAction := by
  unfold sourceJointGenerator sourceJointMother nativeMother
  rw [phase_lie_original]
  rfl

/-- All nine original configuration fields remain explicit, including independent conjugate matter and gauge auxiliary. -/
def emGaugePrimitive (c : StageNineHolonomicConfiguration) : StageNineHolonomicConfiguration where
  coframe:=0
  gravityConnection:=0
  gravityAuxiliary:=0
  gravitySimplicityMultiplier:=0
  gaugeConnection x mu:=p286CoordinateEquiv.symm
    (nativeGaugeDirection sourcePhaseGaugeLie 0 (actualConnection c x) mu)
  gaugeAuxiliary x pair:=p286LieBracket (p286CoordinateEquiv.symm sourcePhaseGaugeLie) (c.gaugeAuxiliary x pair)
  scalar x:=action (c.scalar x) sourcePhaseGaugeLie
  matter x:=sourceJointGenerator (c.matter x)
  conjugateMatter x:=-(c.conjugateMatter x).comp sourceJointGenerator

theorem emGaugePrimitive_independent_pair (c : StageNineHolonomicConfiguration) (x : BasePoint) :
    (emGaugePrimitive c).conjugateMatter x (c.matter x)+
      c.conjugateMatter x ((emGaugePrimitive c).matter x)=0 := by
  change -c.conjugateMatter x (sourceJointGenerator (c.matter x))+
    c.conjugateMatter x (sourceJointGenerator (c.matter x))=0
  exact neg_add_cancel _

/-- The actual nonzero scalar orbit and the two independent endpoint variations are consumed together by the original repaired Yukawa Ward identity. -/
theorem emGaugePrimitive_scalarWard (c : StageNineHolonomicConfiguration) (x : BasePoint) :
    c.conjugateMatter x (diracDualRightChiralYukawaAction
      (scalarCoordinateEquiv.symm ((emGaugePrimitive c).scalar x)) (c.matter x))+
    c.conjugateMatter x (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (c.scalar x))
      ((emGaugePrimitive c).matter x))+
    (emGaugePrimitive c).conjugateMatter x
      (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (c.scalar x)) (c.matter x))=0 := by
  change c.conjugateMatter x (diracDualRightChiralYukawaAction
      (scalarCoordinateEquiv.symm (action (c.scalar x) sourcePhaseGaugeLie)) (c.matter x))+
    c.conjugateMatter x (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (c.scalar x))
      (sourceJointGenerator (c.matter x)))+
    (-(c.conjugateMatter x).comp sourceJointGenerator)
      (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (c.scalar x)) (c.matter x))=0
  rw [scalarAction_mother]
  exact independent_dual_scalar_ward (nativeMother sourcePhaseGaugeLie)
    (scalarCoordinateEquiv.symm (c.scalar x)) (c.matter x) (c.conjugateMatter x)

/-- This state tangent is a restriction of the original full configuration variation. -/
def emGaugeState : ActionState→ₗ[ℝ]ActionState where
  toFun s:=(0,(fun mu=>nativePrimal sourcePhaseGaugeLie*s.2.1 mu-s.2.1 mu*nativePrimal sourcePhaseGaugeLie),
    nativePrimal sourcePhaseGaugeLie*s.2.2-s.2.2*nativePrimal sourcePhaseGaugeLie)
  map_add' a b:=by
    let G:=nativePrimal sourcePhaseGaugeLie
    apply Prod.ext
    · simp
    apply Prod.ext
    · funext mu
      change G*(a.2.1 mu+b.2.1 mu)-(a.2.1 mu+b.2.1 mu)*G=
        (G*a.2.1 mu-a.2.1 mu*G)+(G*b.2.1 mu-b.2.1 mu*G)
      noncomm_ring
    · change G*(a.2.2+b.2.2)-(a.2.2+b.2.2)*G=
        (G*a.2.2-a.2.2*G)+(G*b.2.2-b.2.2*G)
      noncomm_ring
  map_smul' r a:=by
    let G:=nativePrimal sourcePhaseGaugeLie
    apply Prod.ext
    · simp
    apply Prod.ext
    · funext mu
      change G*(r • a.2.1 mu)-(r • a.2.1 mu)*G=r • (G*a.2.1 mu-a.2.1 mu*G)
      rw [mul_smul_comm,smul_mul_assoc,smul_sub]
    · change G*(r • a.2.2)-(r • a.2.2)*G=r • (G*a.2.2-a.2.2*G)
      rw [mul_smul_comm,smul_mul_assoc,smul_sub]

theorem emGaugePrimitive_state (c : StageNineHolonomicConfiguration) (x : BasePoint) :
    configurationState (emGaugePrimitive c) x=emGaugeState (configurationState c x) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext mu
    change Quantum.operatorMatrix (FullQuantum.connection (emGaugePrimitive c) x mu)=
      nativePrimal sourcePhaseGaugeLie*Quantum.operatorMatrix (FullQuantum.connection c x mu)-
        Quantum.operatorMatrix (FullQuantum.connection c x mu)*nativePrimal sourcePhaseGaugeLie
    rw [originalConnection_source,originalConnection_source]
    change spinCoordinates (PointwiseDiracSpinConnectionLift.diracSpinConnectionLift 0 mu)+
      nativePrimal (show NativeLie from p286CoordinateEquiv (p286CoordinateEquiv.symm
        (nativeGaugeDirection sourcePhaseGaugeLie 0 (actualConnection c x) mu)))=_
    rw [LinearEquiv.apply_symm_apply]
    have spinzero : PointwiseDiracSpinConnectionLift.diracSpinConnectionLift 0 mu=0 :=
      (PointwiseDiracSpinConnectionLift.diracSpinConnectionLiftLinear mu).map_zero
    simp only [spinzero,map_zero,zero_add,nativeGaugeDirection,Pi.zero_apply,sub_zero]
    have original:=originalGauge_commutator sourcePhaseGaugeLie
      (show NativeLie from p286CoordinateEquiv (c.gaugeConnection x mu))
    change nativePrimal (lie sourcePhaseGaugeLie (actualConnection c x mu))=_ at original
    rw [original,mul_add,add_mul,originalSpin_internal_commute]
    abel
  · exact originalScalar_commutator sourcePhaseGaugeLie (c.scalar x)

/-- The same full nine-field affine occurrence supplies the original action-state line for every real parameter. -/
theorem emGaugePrimitive_ray (c : StageNineHolonomicConfiguration) (x : BasePoint) (r : ℝ) :
    configurationState (configurationRay c (emGaugePrimitive c) r) x=
      configurationState c x+r • emGaugeState (configurationState c x) := by
  rw [configurationState_ray,emGaugePrimitive_state]


/-- The full source EM generator retains its actual scalar orbit. -/
def emBackgroundAd : SourceMatrix→ₗ[ℂ]SourceMatrix where
  toFun A:=nativePrimal sourcePhaseGaugeLie*A-A*nativePrimal sourcePhaseGaugeLie
  map_add' A B:=by simp only [mul_add,add_mul];abel
  map_smul' c A:=by simp only [mul_smul_comm,smul_mul_assoc,smul_sub,RingHom.id_apply]

private theorem coefficient_commute (e : LorentzianCoframe) (mu : Fin 4) :
    Commute (nativePrimal sourcePhaseGaugeLie) (coefficientMatrix mu e) := by
  change _*(Complex.I • spinCoordinates (inverseCoframeDiracGamma {coframe:=e,derivative:=0} mu))=
    (Complex.I • spinCoordinates (inverseCoframeDiracGamma {coframe:=e,derivative:=0} mu))*_
  rw [mul_smul_comm,smul_mul_assoc,originalSpin_internal_commute]

private theorem inverse_commute (s : ActionState) (valid : s∈validStates) :
    Commute (nativePrimal sourcePhaseGaugeLie) (Ring.inverse (principalMatrix s.1)) := by
  let unit:=principalMatrix_regular s.1 valid.2
  have base : Commute (nativePrimal sourcePhaseGaugeLie) (↑unit.unit : SourceMatrix) := by
    rw [unit.unit_spec,principalMatrix_coefficient]
    exact coefficient_commute s.1 0
  have inverse:=base.units_inv_right
  rw [←Ring.inverse_unit,unit.unit_spec] at inverse
  exact inverse

private theorem ad_factor (B A : SourceMatrix) (commute : Commute (nativePrimal sourcePhaseGaugeLie) B) :
    emBackgroundAd (B*A)=B*emBackgroundAd A := by
  change _*(B*A)-(B*A)*_=B*(_*A-A*_)
  rw [←mul_assoc _ B,commute.eq]
  noncomm_ring

private theorem lower_jet (s : ActionState) :
    sourceLowerJet s (emGaugeState s)=emBackgroundAd (stateLower s) := by
  simp only [sourceLowerJet,emGaugeState,LinearMap.coe_mk,AddHom.coe_mk,
    sourceCoframeCoefficientJet,mul_zero,zero_mul,neg_zero,map_zero,zero_add]
  change (∑mu : Fin 4,coefficientMatrix mu s.1*emBackgroundAd (s.2.1 mu))+
    emBackgroundAd s.2.2=emBackgroundAd (stateLower s)
  simp only [stateLower,map_add,map_sum,ad_factor _ _ (coefficient_commute _ _)]

/-- The source inverse-principal jet and scalar Yukawa supplement generate the complete Hamiltonian commutator on all four Fourier coefficients. -/
theorem emBackgroundHamiltonian (s : ActionState) (valid : s∈validStates) (k : Fin 4) :
    sourceHamiltonianJetMatrix s (emGaugeState s) k=emBackgroundAd (stateHamiltonian s k) := by
  have inverseZero : sourcePrincipalInverseJet s (emGaugeState s)=0 := by
    simp [sourcePrincipalInverseJet,emGaugeState,sourceCoframeCoefficientJet]
  cases k using Fin.cases with
  | zero=>
    simp only [sourceHamiltonianJetMatrix,Fin.cases_zero,inverseZero,zero_mul,zero_add,lower_jet,
      stateHamiltonian,timeSymbol,map_smul,ad_factor _ _ (inverse_commute s valid)]
  | succ j=>
    simp only [sourceHamiltonianJetMatrix,Fin.cases_succ]
    rw [inverseZero]
    simp only [zero_mul,emGaugeState,LinearMap.coe_mk,AddHom.coe_mk,sourceCoframeCoefficientJet,
      mul_zero,neg_zero,map_zero,add_zero,stateHamiltonian]
    simp only [Fin.cases_succ,ad_factor _ _ (inverse_commute s valid)]
    change 0=Ring.inverse (principalMatrix s.1)*
      (nativePrimal sourcePhaseGaugeLie*coefficientMatrix j.succ s.1-
        coefficientMatrix j.succ s.1*nativePrimal sourcePhaseGaugeLie)
    rw [(coefficient_commute s.1 j.succ).eq,sub_self,mul_zero]

/-- Independent conjugate matter uses the original opposite branch of the Lie generator. -/
def emBackgroundFullGenerator : FullMatrix :=
  Matrix.fromBlocks (nativePrimal sourcePhaseGaugeLie) 0 0
    ((nativePrimal sourcePhaseGaugeLie).map (starRingEnd ℂ))

def emBackgroundFullAd : FullMatrix→ₗ[ℂ]FullMatrix where
  toFun A:=emBackgroundFullGenerator*A-A*emBackgroundFullGenerator
  map_add' A B:=by simp only [mul_add,add_mul];abel
  map_smul' c A:=by simp only [mul_smul_comm,smul_mul_assoc,smul_sub,RingHom.id_apply]

private theorem affine_ad (A : Fin 4→SourceMatrix) (p : CanonicalGradedSpatialSource.PhysicalMomentum) :
    affineMatrix (fun k=>emBackgroundAd (A k)) p=emBackgroundAd (affineMatrix A p) := by
  simp only [affineMatrix,map_add,map_sum,map_smul]

private theorem blocks_sub (A B C D : SourceMatrix) :
    Matrix.fromBlocks A 0 0 B-Matrix.fromBlocks C 0 0 D=Matrix.fromBlocks (A-C) 0 0 (B-D) := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks]

private theorem fourier_ad (A : Fin 4→SourceMatrix) (p : CanonicalGradedSpatialSource.PhysicalMomentum) :
    fourierLinear p (fun k=>emBackgroundAd (A k))=
      emBackgroundFullAd (fourierLinear p A) := by
  change Matrix.fromBlocks (affineMatrix (fun k=>emBackgroundAd (A k)) p) 0 0
    (-((affineMatrix (fun k=>emBackgroundAd (A k)) (-p)).map (starRingEnd ℂ)))=_
  rw [affine_ad,affine_ad]
  simp only [emBackgroundAd,emBackgroundFullAd,emBackgroundFullGenerator,
    LinearMap.coe_mk,AddHom.coe_mk,fourierLinear,realFourierMatrix,Matrix.fromBlocks_multiply,
    mul_zero,zero_mul,add_zero,zero_add,mul_neg,neg_mul,neg_zero,blocks_sub,
    Matrix.map_sub _ (fun a b=>map_sub (starRingEnd ℂ) a b),Matrix.map_mul]
  change Matrix.fromBlocks _ 0 0
    (-((nativePrimal sourcePhaseGaugeLie).map (starRingEnd ℂ)*
      (affineMatrix A (-p)).map (starRingEnd ℂ)-(affineMatrix A (-p)).map (starRingEnd ℂ)*
        (nativePrimal sourcePhaseGaugeLie).map (starRingEnd ℂ)))=_
  congr 1
  abel

/-- The original action normalization and Fourier negative-momentum branch are consumed, rather than replaced by a new response. -/
theorem emBackgroundSymbol (p : CanonicalGradedSpatialSource.PhysicalMomentum)
    (s : ActionState) (valid : s∈validStates) :
    symbolFirst p s (emGaugeState s)=emBackgroundFullAd (sourceSymbol p s) := by
  rw [←sourceNormalizedEnergySymbol_original p s _ valid,sourceNormalizedEnergySymbol_matrix p s _ valid]
  rw [show sourceHamiltonianJetMatrix s (emGaugeState s)=
    (fun k=>emBackgroundAd (stateHamiltonian s k)) from funext (emBackgroundHamiltonian s valid)]
  exact fourier_ad (stateHamiltonian s) p

/-- This derivative is the restriction of the actual full nine-field configuration ray. -/
theorem emBackground_curve (p : CanonicalGradedSpatialSource.PhysicalMomentum) (z : physicalChart) :
    HasDerivAt (fun r : ℝ=>sourceSymbol p (configurationState
      (configurationRay (emitter z.val) (emGaugePrimitive (emitter z.val)) r) 0))
      (emBackgroundFullAd (sourceSymbol p (sourceState z.val))) 0 := by
  have valid : sourceState z.val∈validStates:=⟨coframe_nondegenerate z,CanonicalGradedSpatialSource.temporal_noncharacteristic z⟩
  have generated:=symbol_first_generated p (sourceState z.val) (emGaugeState (sourceState z.val)) valid
  simpa only [emGaugePrimitive_ray,configurationState_emitter,emBackgroundSymbol p _ valid] using generated

/-- The contact differentiates the actual field-dependent gauge tangent; it is not discarded from the Hessian. -/
def emBackgroundMixed (p : CanonicalGradedSpatialSource.PhysicalMomentum) (s : ActionState) (f : Field289) : FullMatrix :=
  symbolSecond p s (emGaugeState s) (fieldDirection f)+
    symbolFirst p s (emGaugeState (fieldDirection f))

private theorem mixed_derivative (p : CanonicalGradedSpatialSource.PhysicalMomentum) (s : ActionState)
    (valid : s∈validStates) (f : Field289) :
    HasDerivAt (fun r : ℝ=>symbolFirst p (s+r • fieldDirection f)
      (emGaugeState (s+r • fieldDirection f))) (emBackgroundMixed p s f) 0 := by
  have outer:=((sourceSymbol_smooth p s valid).fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have D:=outer.hasFDerivAt.comp_hasDerivAt_of_eq 0 (state_line s (fieldDirection f)) (by simp)
  have native:=emGaugeState.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0
    (state_line s (fieldDirection f))
  have generated:=D.clm_apply native
  convert! generated using 1
  simp only [emBackgroundMixed,symbolSecond,symbolFirst,Function.comp_apply,zero_smul,add_zero,
    LinearMap.coe_toContinuousLinearMap']

/-- The original all289 current Hessian retains both the second variation and its actual gauge contact. -/
theorem emBackgroundMixed_return (p : CanonicalGradedSpatialSource.PhysicalMomentum)
    (s : ActionState) (valid : s∈validStates) (f : Field289) :
    emBackgroundMixed p s f=emBackgroundFullAd (symbolFirst p s (fieldDirection f)) := by
  have left:=mixed_derivative p s valid f
  have right:=(emBackgroundFullAd.restrictScalars ℝ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0
    (symbol_first_generated p s (fieldDirection f) valid)
  have near : ∀ᶠr in 𝓝 (0:ℝ),s+r • fieldDirection f∈validStates :=
    (state_line s (fieldDirection f)).continuousAt.preimage_mem_nhds (by simpa using validStates_open.mem_nhds valid)
  have same : (fun r : ℝ=>symbolFirst p (s+r • fieldDirection f) (emGaugeState (s+r • fieldDirection f)))=ᶠ[𝓝 (0:ℝ)]
      (fun r=>emBackgroundFullAd (sourceSymbol p (s+r • fieldDirection f))) :=
    near.mono fun r hr=>emBackgroundSymbol p _ hr
  exact left.unique (right.congr_of_eventuallyEq same)

/-- Complete CAR and the original current fiber consume this full-background Ward identity, including the computed scalar orbit and mixed contact. -/
theorem emBackgroundCurrent_return (p : CanonicalGradedSpatialSource.PhysicalMomentum)
    (z : physicalChart) (f : Field289) :
    quantizer (emBackgroundMixed p (sourceState z.val) f)=
      -(quantized emBackgroundFullGenerator*fiberFamily f p z.val-
        fiberFamily f p z.val*quantized emBackgroundFullGenerator) := by
  have valid : sourceState z.val∈validStates:=⟨coframe_nondegenerate z,CanonicalGradedSpatialSource.temporal_noncharacteristic z⟩
  rw [emBackgroundMixed_return p _ valid]
  change quantizer (emBackgroundFullGenerator*symbolFirst p (sourceState z.val) (fieldDirection f)-
    symbolFirst p (sourceState z.val) (fieldDirection f)*emBackgroundFullGenerator)=_
  rw [paidCoframeQuantizerComm%,symbolFirst_actual]
  change quantized emBackgroundFullGenerator*(-fiberFamily f p z.val)-
    (-fiberFamily f p z.val)*quantized emBackgroundFullGenerator=_
  ext v
  simp only [mul_apply_eq_comp,neg_apply,
    sub_apply,map_neg]
  abel


end LowEnergy.GaussComposite.ActualEMOriginWard
