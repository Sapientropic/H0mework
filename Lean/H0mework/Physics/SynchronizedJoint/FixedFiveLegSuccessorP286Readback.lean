import H0mework.Physics.SynchronizedJoint.FixedFiveLegSuccessor
import H0mework.Physics.SynchronizedJoint.FixedP286ConnectionScalarReadback
import H0mework.Physics.FullOccurrence.FixedAssemblySeamClosure
import H0mework.Physics.ElectricEC.FixedP286AllPointSettlement
import H0mework.Physics.DualVariation.P286CanonicalJointActionProducerSoundness

/-!
# P286 read-after-write on the Lorentz-path five-leg successor

The full-occurrence compiler is the strongest existing source/current-only
whole-field writer: every spacetime point is canonically recentered, all five
native mother-action legs run in their fixed order, and all nine primitive
origin values are assembled into one common successor.

This module computes the P286 connection read on that actual.  The compiler
preserves the supplied coframe, gauge connection, scalar, matter, and adjoint
fields.  Its P286 auxiliary is the live constitutive value of the same gauge
connection, which is already the auxiliary carried by the Lorentz-path
current.  Hence the complete P286 connection read is unchanged.  The existing
unit-spatial nonzero read therefore persists as a producer-consistency
obstruction.  No residual coordinate or its negative enters the writer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathFiveLegSuccessorP286Readback

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionFixedP506GlobalRegularity
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointP286LiveElectricCauchyOperator
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathFiveLegSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathP286AuxiliaryReadback
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathP286ConnectionScalarReadback
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeamClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECP286AllPointSettlement
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerSoundness
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGaugeCurvatureTransport
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineP286ActionCauchySplit
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286HolonomicSecondJetCarrier
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance fiveLegReadbackP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance fiveLegReadbackP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Input : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

private abbrev Successor : StageNineHolonomicConfiguration :=
  fixedP506L0LorentzPathFiveLegSuccessor

private abbrev Raw : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionActual

private theorem raw_smooth : Raw.Smooth :=
  fixedP506L0CompleteJointActionSpacetimeSection_smooth

private theorem current_gaugeConnection_eq_raw :
    Current.gaugeConnection = Raw.gaugeConnection := by
  calc
    Current.gaugeConnection = Input.gaugeConnection :=
      final_gaugeConnection_eq_input
    _ = Raw.gaugeConnection :=
      (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator_gaugeConnection
        Source Input).symm

/-! ## Primitive gauge-connection custody -/

/-- The occurrence-diagonal P286 write changes only the local homogeneous
second jet; its assembled connection value is exactly the supplied whole
connection field. -/
theorem fixedP506L0LorentzPathFiveLegSuccessor_gaugeConnection_eq_current :
    Successor.gaugeConnection = Current.gaugeConnection := by
  funext point
  change
    (completeJointLiveElectricECFullOccurrenceContact Source Current point
      ).gaugeConnection 0 = Current.gaugeConnection point
  unfold completeJointLiveElectricECFullOccurrenceContact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeConnection]
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeConnection]
  calc
    (completeJointGlobalP286AlgebraicCurrent Source
        (fullyRecenterHolonomicConfiguration Current point)
      ).gaugeConnection 0 =
        (completeJointGlobalTemporalCurrent Source
          (fullyRecenterHolonomicConfiguration Current point)
        ).gaugeConnection 0 := by
      exact canonicalJointCandidate_connection_origin_raw
        (completeJointGlobalTemporalCurrent Source
          (fullyRecenterHolonomicConfiguration Current point))
        (diracDualFormNativeP286CanonicalGeneratedWrite Source
          (completeJointGlobalTemporalCurrent Source
            (fullyRecenterHolonomicConfiguration Current point)))
    _ = (fullyRecenterHolonomicConfiguration Current point
          ).gaugeConnection 0 :=
      rfl
    _ = Current.gaugeConnection point :=
      fullyRecenterHolonomicConfiguration_gaugeConnection_origin Current point

/-! ## Live constitutive auxiliary custody -/

private abbrev LocalTemporal (point : BasePoint) :
    StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source
    (fullyRecenterHolonomicConfiguration Current point)

private abbrev LocalWrite (point : BasePoint) : P286GaugeOneForm :=
  diracDualFormNativeP286CanonicalGeneratedWrite Source
    (LocalTemporal point)

private abbrev LocalCandidate (point : BasePoint) :
    StageNineHolonomicConfiguration :=
  diracDualFormNativeP286CanonicalConnectionCandidate
    (LocalTemporal point) (LocalWrite point)

private abbrev ProxyRecenter (point : BasePoint) :
    StageNineHolonomicConfiguration :=
  fullyRecenterHolonomicConfiguration Raw point

private abbrev ProxyCandidate (point : BasePoint) :
    StageNineHolonomicConfiguration :=
  diracDualFormNativeP286CanonicalConnectionCandidate
    (ProxyRecenter point) (LocalWrite point)

private theorem proxyRecenter_smooth (point : BasePoint) :
    (ProxyRecenter point).Smooth :=
  fullyRecenterHolonomicConfiguration_smooth Raw raw_smooth point

private theorem localTemporal_gaugeConnection_eq_proxyRecenter
    (point : BasePoint) :
    (LocalTemporal point).gaugeConnection =
      (ProxyRecenter point).gaugeConnection := by
  funext localPoint
  change
    Current.gaugeConnection
        (canonicalSpacetimeContactTranslation point localPoint) =
      Raw.gaugeConnection
        (canonicalSpacetimeContactTranslation point localPoint)
  exact congrFun current_gaugeConnection_eq_raw _

private theorem canonicalConnectionCandidate_gaugeConnection_eq_of_connection_eq
    (first second : StageNineHolonomicConfiguration)
    (connectionEq : first.gaugeConnection = second.gaugeConnection)
    (write : P286GaugeOneForm) :
    (diracDualFormNativeP286CanonicalConnectionCandidate first write
      ).gaugeConnection =
      (diracDualFormNativeP286CanonicalConnectionCandidate second write
        ).gaugeConnection := by
  funext point direction
  simp only [diracDualFormNativeP286CanonicalConnectionCandidate,
    installP286HolonomicConnectionSecondJet,
    varyP286GaugeConnectionCoordinate,
    holonomicP286GaugeConnectionCoordinate]
  rw [connectionEq]

private theorem localCandidate_gaugeConnection_eq_proxyCandidate
    (point : BasePoint) :
    (LocalCandidate point).gaugeConnection =
      (ProxyCandidate point).gaugeConnection :=
  canonicalConnectionCandidate_gaugeConnection_eq_of_connection_eq
    (LocalTemporal point) (ProxyRecenter point)
    (localTemporal_gaugeConnection_eq_proxyRecenter point)
    (LocalWrite point)

private theorem installSecondJet_gaugeCurvature_origin
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (jet : P286HolonomicConnectionSecondJet)
    (parameter : ℝ) :
    holonomicGaugeCurvature
        (installP286HolonomicConnectionSecondJet configuration jet parameter)
        0 = holonomicGaugeCurvature configuration 0 := by
  funext pair
  apply p286CoordinateEquiv.injective
  exact congrFun
    (installP286HolonomicConnectionSecondJet_curvature_origin
      configuration smooth jet parameter) pair

private theorem localCandidate_gaugeCurvature_origin_eq_current
    (point : BasePoint) :
    holonomicGaugeCurvature (LocalCandidate point) 0 =
      holonomicGaugeCurvature Current point := by
  calc
    holonomicGaugeCurvature (LocalCandidate point) 0 =
        holonomicGaugeCurvature (ProxyCandidate point) 0 :=
      holonomicGaugeCurvature_eq_of_connection_eq
        (LocalCandidate point) (ProxyCandidate point)
        (localCandidate_gaugeConnection_eq_proxyCandidate point) 0
    _ = holonomicGaugeCurvature (ProxyRecenter point) 0 := by
      exact installSecondJet_gaugeCurvature_origin
        (ProxyRecenter point) (proxyRecenter_smooth point)
        (p286CanonicalDiagonalResponseSecondJet (LocalWrite point)) 1
    _ = holonomicGaugeCurvature Raw point :=
      fullyRecenterHolonomicConfiguration_gaugeCurvature_origin_unconditional
        Raw point
    _ = holonomicGaugeCurvature Current point :=
      (holonomicGaugeCurvature_eq_of_connection_eq Current Raw
        current_gaugeConnection_eq_raw point).symm

private theorem localAlgebraic_gaugeCurvature_origin_eq_current
    (point : BasePoint) :
    holonomicGaugeCurvature
        (completeJointGlobalP286AlgebraicCurrent Source
          (fullyRecenterHolonomicConfiguration Current point)) 0 =
      holonomicGaugeCurvature Current point := by
  calc
    holonomicGaugeCurvature
        (completeJointGlobalP286AlgebraicCurrent Source
          (fullyRecenterHolonomicConfiguration Current point)) 0 =
        holonomicGaugeCurvature (LocalCandidate point) 0 := by
      exact holonomicGaugeCurvature_eq_of_connection_eq
        (completeJointGlobalP286AlgebraicCurrent Source
          (fullyRecenterHolonomicConfiguration Current point))
        (LocalCandidate point) rfl 0
    _ = holonomicGaugeCurvature Current point :=
      localCandidate_gaugeCurvature_origin_eq_current point

private theorem canonical_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) =
      (0 : BasePoint) := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]

private theorem localLiveElectric_gaugeAuxiliary_origin_eq_algebraic
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
        Source (fullyRecenterHolonomicConfiguration Current point)
      ).gaugeAuxiliary 0 =
      (completeJointGlobalP286AlgebraicCurrent Source
        (fullyRecenterHolonomicConfiguration Current point)
      ).gaugeAuxiliary 0 := by
  funext pair
  apply p286CoordinateEquiv.injective
  have zeroSliceEquality := congrFun
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeAuxiliary_zeroSlice
      Source (fullyRecenterHolonomicConfiguration Current point)
      (0 : StageNineSpatialPoint)) pair
  simpa only [canonical_zero,
    holonomicP286GaugeAuxiliaryCoordinate] using zeroSliceEquality

private theorem successor_gaugeAuxiliary_eq_constitutive :
    Successor.gaugeAuxiliary =
      diracDualFormNativeConstitutiveAuxiliaryField Source Current := by
  funext point
  change
    (completeJointLiveElectricECFullOccurrenceContact Source Current point
      ).gaugeAuxiliary 0 =
      diracDualFormNativeConstitutiveAuxiliaryField Source Current point
  unfold completeJointLiveElectricECFullOccurrenceContact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeAuxiliary]
  calc
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
        Source (fullyRecenterHolonomicConfiguration Current point)
      ).gaugeAuxiliary 0 =
        (completeJointGlobalP286AlgebraicCurrent Source
          (fullyRecenterHolonomicConfiguration Current point)
        ).gaugeAuxiliary 0 :=
      localLiveElectric_gaugeAuxiliary_origin_eq_algebraic point
    _ = diracDualFormNativeConstitutiveAuxiliaryField Source Current point := by
      change
        formNativeP286GaugeEliminatedAuxiliaryAtBoundary
            (sourceGeneratedUnifiedCouplings Source)
            ((fullyRecenterHolonomicConfiguration Current point).coframe 0)
            (holonomicGaugeCurvature
              (completeJointGlobalP286AlgebraicCurrent Source
                (fullyRecenterHolonomicConfiguration Current point)) 0) =
          formNativeP286GaugeEliminatedAuxiliaryAtBoundary
            (sourceGeneratedUnifiedCouplings Source)
            (Current.coframe point)
            (holonomicGaugeCurvature Current point)
      rw [fullyRecenterHolonomicConfiguration_coframe_origin,
        localAlgebraic_gaugeCurvature_origin_eq_current]

private theorem current_gaugeAuxiliary_eq_constitutive :
    Current.gaugeAuxiliary =
      diracDualFormNativeConstitutiveAuxiliaryField Source Current := by
  funext point
  have residualZero := final_p286AuxiliaryResidual_allPoint_zero point
  have equation :=
    (formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff
      (sourceGeneratedUnifiedCouplings Source)
      (toContinuumPointField Current point)).1 residualZero
  have nondegenerate : Matrix.det (Current.coframe point) ≠ 0 :=
    fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual_nondegenerate
      point
  have eliminated :=
    (formNativeP286GaugeAuxiliaryEquationAtBoundary_iff_eliminated
      (sourceGeneratedUnifiedCouplings Source)
      (toContinuumPointField Current point) nondegenerate).1 equation
  change
    Current.gaugeAuxiliary point =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (Current.coframe point) (holonomicGaugeCurvature Current point)
  exact eliminated

theorem fixedP506L0LorentzPathFiveLegSuccessor_gaugeAuxiliary_eq_current :
    Successor.gaugeAuxiliary = Current.gaugeAuxiliary :=
  successor_gaugeAuxiliary_eq_constitutive.trans
    current_gaugeAuxiliary_eq_constitutive.symm

/-! ## Whole P286 changed-read verdict -/

private theorem successor_p286EulerThreeForm_eq_current :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Successor =
      holonomicFormNativeP286GaugeEulerThreeForm Source 0 Current := by
  apply holonomicFormNativeP286GaugeEulerThreeForm_eq_of_primitiveFields
  · exact
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe
        Source Current
  · exact fixedP506L0LorentzPathFiveLegSuccessor_gaugeConnection_eq_current
  · exact fixedP506L0LorentzPathFiveLegSuccessor_gaugeAuxiliary_eq_current
  · exact
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_scalar_eq_current
        Source Current
  · exact
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_matter_eq_current
        Source Current
  · exact
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_conjugateMatter_eq_current
        Source Current

/-- The complete P286 connection residual of the one generated common
successor is exactly the prior changed read at every spacetime point. -/
theorem fixedP506L0LorentzPathFiveLegSuccessor_p286GaugeConnection_eq_current
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source Successor point
      ).p286GaugeConnection =
      (diracDualFormNativePointwiseJointResidual Source Current point
        ).p286GaugeConnection :=
  congrFun successor_p286EulerThreeForm_eq_current point

/-- At the explicit source-owned unit-spatial occurrence, the five-leg common
successor still has a nonzero P286 connection residual. -/
theorem
    fixedP506L0LorentzPathFiveLegSuccessor_p286GaugeConnection_unitSpatial_ne_zero :
    (diracDualFormNativePointwiseJointResidual Source Successor
        (canonicalCauchySlicePoint 0 (EuclideanSpace.single 0 1))
      ).p286GaugeConnection ≠ 0 := by
  rw [fixedP506L0LorentzPathFiveLegSuccessor_p286GaugeConnection_eq_current]
  exact final_p286GaugeConnectionResidual_zeroSlice_unitSpatial_ne_zero

/-- Hence the strongest existing source/current-only full-occurrence writer
does not yet produce the S9-C joint zero fiber.  This is a read-after-write
consistency verdict on its actual output, not an independent constraint and
not permission to invert the residual. -/
theorem fixedP506L0LorentzPathFiveLegSuccessor_not_onPointwiseJointZeroFiber :
    ¬ OnDiracDualFormNativePointwiseJointZeroFiber Source Successor
        (canonicalCauchySlicePoint 0 (EuclideanSpace.single 0 1)) := by
  intro zeroFiber
  apply
    fixedP506L0LorentzPathFiveLegSuccessor_p286GaugeConnection_unitSpatial_ne_zero
  unfold OnDiracDualFormNativePointwiseJointZeroFiber at zeroFiber
  have projected := congrArg
    (fun residual : DiracDualFormNativePointwiseJointResidualCarrier =>
      residual.p286GaugeConnection) zeroFiber
  simpa using projected

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathFiveLegSuccessorP286Readback
