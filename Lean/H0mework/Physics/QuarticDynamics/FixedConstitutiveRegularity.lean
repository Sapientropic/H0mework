import H0mework.Physics.QuarticDynamics.FixedConstitutiveAnchor
import H0mework.Physics.Constitutive.P286GaugeConstitutiveEliminationRegularity

/-!
# Fixed U6 radial-quartic constitutive regularity

The fixed action-generated radial connection has a smooth representative on
the authoritative fixed P506/L0 input.  Its coframe and P286 connection agree
globally with the literal radial connection actual, so curvature and the live
constitutive auxiliary transport back without changing the generated field.

The resulting theorem exposes differentiability of the literal auxiliary
coordinate field at every point of the canonical zero slice.  No residual,
target field, branch, or equation receipt is consumed.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6RadialQuarticConstitutiveRegularity

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeHolonomicRegularity
open StageNineCoframeGravityGaugeRegularity
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalP286Verdict
open StageNineDiracDualFormNativeFixedP506CompleteJointP286AlgebraicMatterScalarDelta
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ZeroSliceActionProfile
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticConstitutiveAnchor
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeConstitutiveEliminationRegularity
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGaugeCurvatureTransport
open StageNineP286ColorCartanQuadraticConnectionJet
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286RadialQuarticActionPrincipal
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

local instance radialRegularityP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance radialRegularityP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Algebraic : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent Source FixedInput

private abbrev U6 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

private abbrev Charge : P286CoordinateCarrier :=
  fixedP506L0U6OccurrenceP286MotherActionCharge

private abbrev ConnectionActual : StageNineHolonomicConfiguration :=
  fixedP506L0U6RadialQuarticConnectionActual

private abbrev Actual : StageNineHolonomicConfiguration :=
  fixedP506L0U6RadialQuarticConstitutiveActual

private def Proxy : StageNineHolonomicConfiguration :=
  varyP286GaugeConnectionCoordinate FixedInput
    (p286RadialQuarticTemporalConnection Charge) 1

private theorem proxy_smooth : Proxy.Smooth := by
  unfold Proxy
  exact varyP286GaugeConnectionCoordinate_smooth_of_contDiff
    FixedInput fixedP506FormNativeJointActionSolvedSuccessor_smooth
    (p286RadialQuarticTemporalConnection Charge)
    (p286RadialQuarticTemporalConnection_contDiff Charge) 1

private theorem algebraic_gaugeConnection_eq_fixedInput :
    Algebraic.gaugeConnection = FixedInput.gaugeConnection := by
  rw [show Algebraic =
      diracDualFormNativeP286CanonicalJointCandidate Source
        (completeJointGlobalTemporalCurrent Source FixedInput) 0 by
    exact fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_eq_zeroCandidate]
  rw [diracDualFormNativeP286CanonicalJointCandidate,
    diracDualFormNativeP286CanonicalConnectionCandidate_zero]
  rfl

private theorem connectionActual_coframe_eq_proxy :
    ConnectionActual.coframe = Proxy.coframe := by
  unfold ConnectionActual fixedP506L0U6RadialQuarticConnectionActual Proxy
  change U6.coframe = FixedInput.coframe
  have u6Coframe : U6.coframe = Algebraic.coframe := by
    simpa [U6, Algebraic] using fixedP506L0U6_coframe_eq_algebraic
  have algebraicCoframe : Algebraic.coframe = FixedInput.coframe := by
    simp [Algebraic, completeJointGlobalP286AlgebraicCurrent,
      completeJointGlobalTemporalCurrent]
  exact u6Coframe.trans algebraicCoframe

private theorem connectionActual_gaugeConnection_eq_proxy :
    ConnectionActual.gaugeConnection = Proxy.gaugeConnection := by
  have u6Algebraic : U6.gaugeConnection = Algebraic.gaugeConnection := by
    simpa [U6, Algebraic] using
      fixedP506L0U6_gaugeConnection_eq_algebraic
  have u6Gauge : U6.gaugeConnection = FixedInput.gaugeConnection :=
    u6Algebraic.trans algebraic_gaugeConnection_eq_fixedInput
  funext point direction
  apply p286CoordinateEquiv.injective
  change
    holonomicP286GaugeConnectionCoordinate ConnectionActual point direction =
      holonomicP286GaugeConnectionCoordinate Proxy point direction
  unfold ConnectionActual fixedP506L0U6RadialQuarticConnectionActual Proxy
  rw [holonomicP286GaugeConnectionCoordinate_vary,
    holonomicP286GaugeConnectionCoordinate_vary]
  simp only [one_smul, Pi.add_apply]
  rw [show holonomicP286GaugeConnectionCoordinate U6 point =
      holonomicP286GaugeConnectionCoordinate FixedInput point by
    unfold holonomicP286GaugeConnectionCoordinate
    rw [u6Gauge]]

private theorem proxy_curvatureCoordinate_contDiff :
    ContDiff ℝ ∞ (holonomicP286GaugeCurvatureCoordinate Proxy) := by
  apply contDiff_pi'
  intro pair
  apply contDiff_piLp'
  intro coordinate
  let projection : P286CoordinateCarrier →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj coordinate).comp
      (EuclideanSpace.equiv P286CoordinateIndex ℝ).toContinuousLinearMap
  exact projection.contDiff.comp
    (holonomicGaugeCurvature_coordinate_contDiff Proxy proxy_smooth pair)

/-- The fixed constitutive actual retains the smooth radial connection, so
its generated gauge curvature has the same global coordinate regularity.
This exposes regularity of an already generated action write; it does not
replace the actual by the proof proxy. -/
theorem
    fixedP506L0U6RadialQuarticConstitutiveActual_gaugeCurvatureCoordinate_contDiff :
    ContDiff ℝ ∞
      (holonomicP286GaugeCurvatureCoordinate Actual) := by
  have connectionEq : Actual.gaugeConnection = Proxy.gaugeConnection := by
    change ConnectionActual.gaugeConnection = Proxy.gaugeConnection
    exact connectionActual_gaugeConnection_eq_proxy
  rw [show holonomicP286GaugeCurvatureCoordinate Actual =
      holonomicP286GaugeCurvatureCoordinate Proxy by
    funext point pair
    change
      p286CoordinateEquiv
          (holonomicGaugeCurvature Actual point pair) =
        p286CoordinateEquiv
          (holonomicGaugeCurvature Proxy point pair)
    rw [holonomicGaugeCurvature_eq_of_connection_eq Actual Proxy
      connectionEq point]]
  exact proxy_curvatureCoordinate_contDiff

/-- Instance-independent real-coordinate readout of the generated curvature
regularity.  This is the stable seam for downstream modules that choose the
same finite basis through a different definitional `Fintype` witness. -/
theorem
    fixedP506L0U6RadialQuarticConstitutiveActual_gaugeCurvatureCoordinate_component_contDiff
    (pair : Fin 6) (coordinate : P286CoordinateIndex) :
    ContDiff ℝ ∞ (fun point =>
      holonomicP286GaugeCurvatureCoordinate Actual point pair coordinate) := by
  exact (contDiff_piLp 2).mp
    (contDiff_pi.mp
      fixedP506L0U6RadialQuarticConstitutiveActual_gaugeCurvatureCoordinate_contDiff
      pair) coordinate

private theorem actual_auxiliaryCoordinate_eq_proxyConstitutive :
    holonomicP286GaugeAuxiliaryCoordinate Actual =
      fun point =>
        formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
          (sourceGeneratedUnifiedCouplings Source)
          (Proxy.coframe point)
          (holonomicP286GaugeCurvatureCoordinate Proxy point) := by
  funext point pair
  unfold Actual fixedP506L0U6RadialQuarticConstitutiveActual
  unfold holonomicP286GaugeAuxiliaryCoordinate
  rw [diracDualFormNativeConstitutiveWrittenCurrent_gaugeAuxiliary]
  unfold diracDualFormNativeConstitutiveAuxiliaryField
  have curvatureEq :
      holonomicGaugeCurvature ConnectionActual point =
        holonomicGaugeCurvature Proxy point :=
    holonomicGaugeCurvature_eq_of_connection_eq ConnectionActual Proxy
      connectionActual_gaugeConnection_eq_proxy point
  rw [congrFun connectionActual_coframe_eq_proxy point, curvatureEq]
  change
    (formNativeP286GaugeActualToCoordinateLinear
      (formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (Proxy.coframe point)
        (holonomicGaugeCurvature Proxy point))) pair = _
  unfold formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
  rw [show holonomicP286GaugeCurvatureCoordinate Proxy point =
      formNativeP286GaugeActualToCoordinateLinear
        (holonomicGaugeCurvature Proxy point) by rfl]
  rw [formNativeP286GaugeActual_coordinate_actual]

/-- The literal action-generated radial constitutive auxiliary is smooth in
a neighborhood of every point of the canonical zero slice. -/
theorem
    fixedP506L0U6RadialQuarticConstitutiveActual_auxiliaryCoordinate_contDiffAt_zeroSlice
    (space : StageNineSpatialPoint) :
    ContDiffAt ℝ ∞
      (holonomicP286GaugeAuxiliaryCoordinate Actual)
      (canonicalCauchySlicePoint 0 space) := by
  let point := canonicalCauchySlicePoint 0 space
  have u6CoframeEqAlgebraic : U6.coframe = Algebraic.coframe := by
    simpa [U6, Algebraic] using fixedP506L0U6_coframe_eq_algebraic
  have connectionCoframeEqU6 : ConnectionActual.coframe = U6.coframe := by
    rfl
  have proxyCoframeEqAlgebraic : Proxy.coframe = Algebraic.coframe :=
    connectionActual_coframe_eq_proxy.symm.trans
      (connectionCoframeEqU6.trans u6CoframeEqAlgebraic)
  have nondegenerate : Matrix.det (Proxy.coframe point) ≠ 0 := by
    rw [congrFun proxyCoframeEqAlgebraic point]
    change Matrix.det
      (Algebraic.coframe (canonicalCauchySlicePoint 0 space)) ≠ 0
    have identityCoframe :
        Algebraic.coframe (canonicalCauchySlicePoint 0 space) = 1 := by
      simpa [Algebraic] using fixedP506L0Algebraic_coframe_zeroSlice space
    rw [identityCoframe]
    norm_num
  have outer :=
    formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary_joint_contDiffAt
      (sourceGeneratedUnifiedCouplings Source)
      (Proxy.coframe point) nondegenerate
      (holonomicP286GaugeCurvatureCoordinate Proxy point)
  have inner : ContDiffAt ℝ ∞
      (fun candidate =>
        (Proxy.coframe candidate,
          holonomicP286GaugeCurvatureCoordinate Proxy candidate)) point :=
    (holonomicCoframe_contDiff Proxy proxy_smooth).contDiffAt.prodMk
      proxy_curvatureCoordinate_contDiff.contDiffAt
  rw [actual_auxiliaryCoordinate_eq_proxyConstitutive]
  have composed := outer.comp point inner
  change ContDiffAt ℝ ∞
    (fun candidate =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (Proxy.coframe candidate)
        (holonomicP286GaugeCurvatureCoordinate Proxy candidate))
    point at composed
  simpa [point] using composed

/-- Instance-independent real-coordinate readout of the local constitutive
auxiliary regularity. -/
theorem
    fixedP506L0U6RadialQuarticConstitutiveActual_auxiliaryCoordinate_component_contDiffAt_zeroSlice
    (space : StageNineSpatialPoint) (pair : Fin 6)
    (coordinate : P286CoordinateIndex) :
    ContDiffAt ℝ ∞
      (fun point =>
        holonomicP286GaugeAuxiliaryCoordinate Actual point pair coordinate)
      (canonicalCauchySlicePoint 0 space) := by
  exact (contDiffAt_piLp 2).mp
    (contDiffAt_pi.mp
      (fixedP506L0U6RadialQuarticConstitutiveActual_auxiliaryCoordinate_contDiffAt_zeroSlice
        space) pair) coordinate

/-- Differentiability is the first-jet readout of the stronger local
regularity theorem above. -/
theorem
    fixedP506L0U6RadialQuarticConstitutiveActual_auxiliaryCoordinate_differentiableAt_zeroSlice
    (space : StageNineSpatialPoint) :
    DifferentiableAt ℝ
      (holonomicP286GaugeAuxiliaryCoordinate Actual)
      (canonicalCauchySlicePoint 0 space) :=
  (fixedP506L0U6RadialQuarticConstitutiveActual_auxiliaryCoordinate_contDiffAt_zeroSlice
    space).differentiableAt (by simp)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6RadialQuarticConstitutiveRegularity
