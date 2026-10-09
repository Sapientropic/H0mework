import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMOriginWardAction

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

/-- The joint source generator retains the actual independent dual on every exterior basis state. -/
theorem em_background_independent_dual (chi : Module.Dual ℂ DiracExteriorMatterCarrier) :
    Quantum.dualCoordinates (-chi.comp emGaugeAction)=
      ((nativePrimal sourcePhaseGaugeLie).map (starRingEnd ℂ))*ᵥQuantum.dualCoordinates chi := by
  rw [←em_joint_generator_original]
  have diagonal : (nativePrimal sourcePhaseGaugeLie).map (starRingEnd ℂ)=
      Matrix.diagonal (fun i=> -(sourceJointWholeWeight i:ℂ)*Complex.I) := by
    rw [sourceJoint_native,sourceJoint_matrix]
    ext i j
    by_cases same : i=j
    · subst j
      simp [Matrix.map_apply]
    · simp [Matrix.map_apply,same]
  rw [diagonal]
  funext i
  rw [Matrix.mulVec_diagonal]
  simp only [Quantum.dualCoordinates,LinearMap.neg_apply,LinearMap.comp_apply,
    sourceJoint_basis,map_smul,smul_eq_mul,neg_mul]

/-- Every component restricts the already generated complete actual EM orbit. -/
theorem em_primitive_actual : emGaugePrimitive actual=emOrbit := by
  apply StageNineHolonomicConfiguration.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · funext point mu
    change p286CoordinateEquiv.symm (nativeGaugeDirection sourcePhaseGaugeLie 0 (actualConnection actual point) mu)=_
    simp only [nativeGaugeDirection,Pi.zero_apply,sub_zero,lie,coordinateBracket,actualConnection,holonomicP286GaugeConnectionCoordinate,
      LinearEquiv.symm_apply_apply,phase_lie_original,emOrbit]
  · funext point pair
    change p286LieBracket (p286CoordinateEquiv.symm sourcePhaseGaugeLie) (actual.gaugeAuxiliary point pair)=_
    rw [phase_lie_original]
    rfl
  · funext point
    change action (actual.scalar point) sourcePhaseGaugeLie=sourcePhaseGaugeScalarVariation
    rw [actual_scalar]
    rfl
  · funext point
    change sourceJointGenerator (actual.matter point)=emGaugeAction (actual.matter point)
    rw [em_joint_generator_original]
  · funext point
    change -(actual.conjugateMatter point).comp sourceJointGenerator= -(actual.conjugateMatter point).comp emGaugeAction
    rw [em_joint_generator_original]

/-- The scalar is the literal nonzero source variation, not a gauge direction silently removed from the action. -/
def emScalarCounterState : ActionState :=
  (0,0,scalarLinear sourcePhaseGaugeScalarVariation)

/-- The original matter-action state sees exactly the native origin plus the complete EM scalar variation. -/
theorem em_origin_state_countervariation :
    emGaugeState sourceReferenceState=fieldDirection (sourceNativeOriginReal 0)+emScalarCounterState := by
  have origin:=sourceNativeOriginAction_state 0
  have fieldConnection (mu : Fin 4) :
      nativePrimal (fieldGauge (sourceNativeOriginReal 0) mu)=sourceNativeOriginConnection 0 mu := by
    rw [sourceNativeOriginReal_gauge]
    fin_cases mu <;> simp [sourceNativeOriginConnection]
  rw [origin]
  apply Prod.ext
  · simp [emGaugeState,emScalarCounterState]
  apply Prod.ext
  · funext mu
    have same:=congrArg (fun s : ActionState=>s.2.1 mu) (emGaugePrimitive_state actual 0)
    rw [em_primitive_actual] at same
    change Quantum.operatorMatrix (FullQuantum.connection emOrbit 0 mu)=_ at same
    rw [originalConnection_source] at same
    have spinzero : diracSpinConnectionLift (emOrbit.gravityConnection 0) mu=0 := by
      change diracSpinConnectionLift 0 mu=0
      exact (diracSpinConnectionLiftLinear mu).map_zero
    rw [spinzero,map_zero,zero_add] at same
    rw [←native_origin_gauge_orbit,LinearEquiv.apply_symm_apply,fieldConnection] at same
    simpa only [emScalarCounterState,Prod.fst_add,Prod.snd_add,Pi.add_apply,Pi.zero_apply,add_zero,sourceReferenceState] using same.symm
  · change nativePrimal sourcePhaseGaugeLie*scalarLinear (actual.scalar 0)-
      scalarLinear (actual.scalar 0)*nativePrimal sourcePhaseGaugeLie=0+scalarLinear sourcePhaseGaugeScalarVariation
    rw [zero_add,←originalScalar_commutator,actual_scalar]
    rfl

/-- The two raw spatial rows are the original native-origin state with its source coefficient. -/
theorem em_origin_mode_state :
    fieldDirection (sourceNativeOriginReal 0)=(gaugeScale/2:ℝ) • fieldDirection sourceModeField := by
  have scale : sourceNativeOriginGaugeWeight=gaugeScale/2 := by
    unfold sourceNativeOriginGaugeWeight gaugeScale spinScale
    ring
  have mode : fieldDirection sourceModeField=fieldDirection (gaugeField 1 0)-fieldDirection (gaugeField 2 1) :=
    fieldDirectionLinear.map_sub _ _
  rw [sourceNativeOriginAction_state,mode,gauge_direction,gauge_direction]
  apply Prod.ext
  · simp
  apply Prod.ext
  · funext mu
    simp only [sourceNativeOriginConnection,ite_true,scale,Prod.smul_snd,Prod.smul_fst,Prod.fst_sub,Prod.snd_sub,Pi.smul_apply,Pi.sub_apply]
  · simp

/-- The emitted configuration differs from the actual source; its complete EM variation is retained. -/
def emOriginDeviationState (s : ActionState) : ActionState := emGaugeState (s-sourceReferenceState)

theorem em_origin_emitted_state (s : ActionState) :
    emGaugeState s=(gaugeScale/2:ℝ) • fieldDirection sourceModeField+emScalarCounterState+emOriginDeviationState s := by
  have split : s=sourceReferenceState+(s-sourceReferenceState) := by abel
  conv_lhs => rw [split,map_add,em_origin_state_countervariation,em_origin_mode_state]
  rfl

/-- The raw action includes its original density weight and its complete independent-dual Fourier branches. -/
def emOriginRawWard (p : CanonicalGradedSpatialSource.PhysicalMomentum) (s : ActionState) : FullMatrix :=
  -(4:ℂ) • (sourceActionWeight s*emBackgroundFullAd (sourceSymbol p s))

def emOriginRawScalar (p : CanonicalGradedSpatialSource.PhysicalMomentum) (s : ActionState) : FullMatrix :=
  -(4:ℂ) • (sourceActionWeight s*symbolFirst p s emScalarCounterState)

def emOriginRawDeviation (p : CanonicalGradedSpatialSource.PhysicalMomentum) (s : ActionState) : FullMatrix :=
  -(4:ℂ) • (sourceActionWeight s*symbolFirst p s (emOriginDeviationState s))

private theorem mode_symbol (p : CanonicalGradedSpatialSource.PhysicalMomentum) (s : ActionState) (valid : s∈validStates) :
    -(4:ℂ) • (sourceActionWeight s*symbolFirst p s (fieldDirection sourceModeField))=sourceModeSymbol s := by
  have mode : fieldDirection sourceModeField=fieldDirection (gaugeField 1 0)-fieldDirection (gaugeField 2 1) :=
    fieldDirectionLinear.map_sub _ _
  unfold symbolFirst
  rw [mode,map_sub,mul_sub,smul_sub]
  change -(4:ℂ) • (sourceActionWeight s*symbolFirst p s (fieldDirection (gaugeField 1 0)))-
    (-(4:ℂ) • (sourceActionWeight s*symbolFirst p s (fieldDirection (gaugeField 2 1))))=sourceModeSymbol s
  rw [←rawActionSymbol_source (gaugeField 1 0) p s valid,←rawActionSymbol_source (gaugeField 2 1) p s valid]
  exact sourceModeSymbol_generated p s valid.1

/-- The original chi reader is generated from the full EM Ward, its scalar countervariation and the actual emitted-state deviation. -/
theorem em_origin_raw_mode_ward (p : CanonicalGradedSpatialSource.PhysicalMomentum)
    (s : ActionState) (valid : s∈validStates) :
    (gaugeScale/2:ℝ) • sourceModeSymbol s=
      emOriginRawWard p s-emOriginRawScalar p s-emOriginRawDeviation p s := by
  have full:=emBackgroundSymbol p s valid
  have expand : symbolFirst p s (emGaugeState s)=
      (gaugeScale/2:ℝ) • symbolFirst p s (fieldDirection sourceModeField)+
        symbolFirst p s emScalarCounterState+symbolFirst p s (emOriginDeviationState s) := by
    rw [em_origin_emitted_state]
    unfold symbolFirst
    rw [map_add,map_add,map_smul]
  rw [←mode_symbol p s valid]
  unfold emOriginRawWard emOriginRawScalar emOriginRawDeviation
  rw [←full,expand,mul_add,mul_add,mul_smul_comm,smul_add,smul_add,smul_comm (-(4:ℂ)) (gaugeScale/2:ℝ)]
  abel

private theorem em_reference_valid : sourceReferenceState∈validStates := by
  have original:=configurationState_emitter sourcePoint.val
  have source : configurationState actual 0=sourceState sourcePoint.val := by
    rw [←original]
    apply Prod.ext
    · exact emitted_source_coframe.symm
    apply Prod.ext
    · funext mu
      change Quantum.operatorMatrix (FullQuantum.connection actual 0 mu)=Quantum.operatorMatrix (FullQuantum.connection (emitter sourcePoint.val) 0 mu)
      unfold FullQuantum.connection
      rw [emitted_source_gauge]
      rfl
    · change scalarLinear (actual.scalar 0)=scalarLinear ((emitter sourcePoint.val).scalar 0)
      rw [emitted_source_scalar]
  rw [sourceReferenceState,source]
  exact sourceState_valid sourcePoint

/-- The actual source generates its validity and zero deviation; the scalar countervariation remains explicit. -/
theorem em_origin_reference_ward (p : CanonicalGradedSpatialSource.PhysicalMomentum) :
    (gaugeScale/2:ℝ) • sourceModeSymbol sourceReferenceState=
      emOriginRawWard p sourceReferenceState-emOriginRawScalar p sourceReferenceState := by
  have source:=em_origin_raw_mode_ward p sourceReferenceState em_reference_valid
  simpa only [emOriginRawDeviation,emOriginDeviationState,sub_self,map_zero,symbolFirst,zero_apply,mul_zero,smul_zero,sub_zero] using source

end LowEnergy.GaussComposite.ActualEMOriginWard
