import H0mework.Physics.FullOccurrence.FixedAssemblySeamClosure
import H0mework.Physics.ElectricEC.FixedP286AllPointSettlement
import H0mework.Physics.DualVariation.P286CanonicalJointActionProducerSoundness

/-!
# Fixed P506/L0 full-occurrence global P286 verdict

The full-occurrence diagonal is already one source/current-only global write.
This module identifies its two primitive P286 gauge fields with the existing
action-owned constitutive settlement, then reads the two final P286 Euler
coordinates on that same actual.

No residual, assembly seam, support coordinate, target field, or zero-fiber
receipt enters either writer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalP286Verdict

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeCompleteJointP286LiveElectricCauchyOperator
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeamClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECP286AllPointSettlement
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerSoundness
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGaugeCurvatureTransport
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286HolonomicSecondJetCarrier
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineP286ActionCauchySplit
open SU7MotherLieAlgebra

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance globalP286VerdictModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance globalP286VerdictCoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance globalP286VerdictCoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Algebraic : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent Source FixedInput

private abbrev U5 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

private abbrev U6 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

private abbrev Settlement : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECP286ConstitutiveSettlementActual

/-! ## A smooth representative of the generated P286 connection -/

/-- The fixed algebraic action connection, installed on the already smooth
fixed input.  The complete temporal leg changes matter/scalar primitives but
not this connection, so this is a regular representative of the literal
connection carried by `Algebraic` and `U5`; it does not alter the generated
write. -/
private def SmoothGaugeProxy : StageNineHolonomicConfiguration :=
  diracDualFormNativeP286CanonicalConnectionCandidate FixedInput
    (diracDualFormNativeP286CanonicalGeneratedWrite Source
      (completeJointGlobalTemporalCurrent Source FixedInput))

private theorem smoothGaugeProxy_smooth : SmoothGaugeProxy.Smooth := by
  unfold SmoothGaugeProxy
    diracDualFormNativeP286CanonicalConnectionCandidate
  exact
    installP286HolonomicConnectionSecondJet_smooth FixedInput
      fixedP506FormNativeJointActionSolvedSuccessor_smooth
      (p286CanonicalDiagonalResponseSecondJet
        (diracDualFormNativeP286CanonicalGeneratedWrite Source
          (completeJointGlobalTemporalCurrent Source FixedInput)))
      1

private theorem smoothGaugeProxy_gaugeConnection_eq_algebraic :
    SmoothGaugeProxy.gaugeConnection = Algebraic.gaugeConnection := by
  rfl

private theorem current_gaugeConnection_eq_algebraic :
    U5.gaugeConnection = Algebraic.gaugeConnection :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gaugeConnection_eq_preEC.trans
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeConnection
      Source FixedInput)

private theorem current_gaugeConnection_eq_smoothGaugeProxy :
    U5.gaugeConnection = SmoothGaugeProxy.gaugeConnection :=
  current_gaugeConnection_eq_algebraic.trans
    smoothGaugeProxy_gaugeConnection_eq_algebraic.symm

/-- The literal U5 P286 connection has the smooth polynomial representative
installed by the same canonical action write.  This exposes regularity of an
already generated primitive field; the proxy does not replace U5 or select a
new write. -/
theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_gaugeConnectionCoordinate_contDiff
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ (fun point =>
      p286CoordinateEquiv (U5.gaugeConnection point direction)) := by
  rw [current_gaugeConnection_eq_smoothGaugeProxy]
  exact smoothGaugeProxy_smooth.2.2.2.2.1 direction

/-- The installed holonomic Hessian has zero curvature contribution at its
own origin.  This is the actual-valued form of the existing coordinate
theorem. -/
private theorem installP286HolonomicConnectionSecondJet_gaugeCurvature_origin
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (jet : P286HolonomicConnectionSecondJet)
    (parameter : ℝ) :
    holonomicGaugeCurvature
        (installP286HolonomicConnectionSecondJet configuration jet parameter)
        0 =
      holonomicGaugeCurvature configuration 0 := by
  funext pair
  apply p286CoordinateEquiv.injective
  exact congrFun
    (installP286HolonomicConnectionSecondJet_curvature_origin
      configuration smooth jet parameter) pair

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

private abbrev LocalTemporal (point : BasePoint) :
    StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source
    (fullyRecenterHolonomicConfiguration U5 point)

private abbrev LocalWrite (point : BasePoint) : P286GaugeOneForm :=
  diracDualFormNativeP286CanonicalGeneratedWrite Source (LocalTemporal point)

private abbrev ProxyRecenter (point : BasePoint) :
    StageNineHolonomicConfiguration :=
  fullyRecenterHolonomicConfiguration SmoothGaugeProxy point

private abbrev LocalCandidate (point : BasePoint) :
    StageNineHolonomicConfiguration :=
  diracDualFormNativeP286CanonicalConnectionCandidate
    (LocalTemporal point) (LocalWrite point)

private abbrev ProxyCandidate (point : BasePoint) :
    StageNineHolonomicConfiguration :=
  diracDualFormNativeP286CanonicalConnectionCandidate
    (ProxyRecenter point) (LocalWrite point)

private theorem proxyRecenter_smooth (point : BasePoint) :
    (ProxyRecenter point).Smooth :=
  fullyRecenterHolonomicConfiguration_smooth SmoothGaugeProxy
    smoothGaugeProxy_smooth point

private theorem localTemporal_gaugeConnection_eq_proxyRecenter
    (point : BasePoint) :
    (LocalTemporal point).gaugeConnection =
      (ProxyRecenter point).gaugeConnection := by
  funext localPoint
  change
    U5.gaugeConnection
        (canonicalSpacetimeContactTranslation point localPoint) =
      SmoothGaugeProxy.gaugeConnection
        (canonicalSpacetimeContactTranslation point localPoint)
  exact congrFun current_gaugeConnection_eq_smoothGaugeProxy _

private theorem localCandidate_gaugeConnection_eq_proxyCandidate
    (point : BasePoint) :
    (LocalCandidate point).gaugeConnection =
      (ProxyCandidate point).gaugeConnection :=
  canonicalConnectionCandidate_gaugeConnection_eq_of_connection_eq
    (LocalTemporal point) (ProxyRecenter point)
    (localTemporal_gaugeConnection_eq_proxyRecenter point)
    (LocalWrite point)

private theorem localCandidate_gaugeCurvature_origin_eq_current
    (point : BasePoint) :
    holonomicGaugeCurvature (LocalCandidate point) 0 =
      holonomicGaugeCurvature U5 point := by
  calc
    holonomicGaugeCurvature (LocalCandidate point) 0 =
        holonomicGaugeCurvature (ProxyCandidate point) 0 :=
      holonomicGaugeCurvature_eq_of_connection_eq
        (LocalCandidate point) (ProxyCandidate point)
        (localCandidate_gaugeConnection_eq_proxyCandidate point) 0
    _ = holonomicGaugeCurvature (ProxyRecenter point) 0 := by
      exact
        installP286HolonomicConnectionSecondJet_gaugeCurvature_origin
          (ProxyRecenter point) (proxyRecenter_smooth point)
          (p286CanonicalDiagonalResponseSecondJet (LocalWrite point)) 1
    _ = holonomicGaugeCurvature SmoothGaugeProxy point :=
      fullyRecenterHolonomicConfiguration_gaugeCurvature_origin_unconditional
        SmoothGaugeProxy point
    _ = holonomicGaugeCurvature U5 point := by
      exact
        (holonomicGaugeCurvature_eq_of_connection_eq U5 SmoothGaugeProxy
          current_gaugeConnection_eq_smoothGaugeProxy point).symm

/-- At every occurrence, the generated quadratic P286 connection write has
the same origin curvature as the supplied global current.  Smoothness is
discharged by the equal-connection proxy above, not assumed of an arbitrary
current and not supplied as a seam receipt. -/
private theorem localAlgebraic_gaugeCurvature_origin_eq_current
    (point : BasePoint) :
    holonomicGaugeCurvature
        (completeJointGlobalP286AlgebraicCurrent Source
          (fullyRecenterHolonomicConfiguration U5 point)) 0 =
      holonomicGaugeCurvature U5 point := by
  calc
    holonomicGaugeCurvature
        (completeJointGlobalP286AlgebraicCurrent Source
          (fullyRecenterHolonomicConfiguration U5 point)) 0 =
        holonomicGaugeCurvature (LocalCandidate point) 0 := by
      apply holonomicGaugeCurvature_eq_of_connection_eq
      rfl
    _ = holonomicGaugeCurvature U5 point :=
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
        Source (fullyRecenterHolonomicConfiguration U5 point)
      ).gaugeAuxiliary 0 =
      (completeJointGlobalP286AlgebraicCurrent Source
        (fullyRecenterHolonomicConfiguration U5 point)).gaugeAuxiliary 0 := by
  funext pair
  apply p286CoordinateEquiv.injective
  have zeroSliceEquality := congrFun
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeAuxiliary_zeroSlice
      Source (fullyRecenterHolonomicConfiguration U5 point)
      (0 : StageNineSpatialPoint)) pair
  simpa only [canonical_zero,
    holonomicP286GaugeAuxiliaryCoordinate] using zeroSliceEquality

/-! ## Whole P286 primitive-field alignment -/

/-- The occurrence-diagonal connection value is the supplied `U5`
connection value.  The canonical P286 leg changes only its homogeneous
second jet at the local contact, so its point value is preserved. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gaugeConnection_eq_current :
    U6.gaugeConnection = U5.gaugeConnection := by
  funext point
  change
    (completeJointLiveElectricECFullOccurrenceContact Source U5 point
      ).gaugeConnection 0 =
      U5.gaugeConnection point
  unfold completeJointLiveElectricECFullOccurrenceContact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeConnection]
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeConnection]
  calc
    (completeJointGlobalP286AlgebraicCurrent Source
        (fullyRecenterHolonomicConfiguration U5 point)).gaugeConnection 0 =
        (completeJointGlobalTemporalCurrent Source
          (fullyRecenterHolonomicConfiguration U5 point)).gaugeConnection 0 := by
      exact canonicalJointCandidate_connection_origin_raw
        (completeJointGlobalTemporalCurrent Source
          (fullyRecenterHolonomicConfiguration U5 point))
        (diracDualFormNativeP286CanonicalGeneratedWrite Source
          (completeJointGlobalTemporalCurrent Source
            (fullyRecenterHolonomicConfiguration U5 point)))
    _ = (fullyRecenterHolonomicConfiguration U5 point).gaugeConnection 0 :=
      rfl
    _ = U5.gaugeConnection point :=
      fullyRecenterHolonomicConfiguration_gaugeConnection_origin U5 point

/-- The U6 connection therefore agrees with the already generated
constitutive settlement. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gaugeConnection_eq_settlement :
    U6.gaugeConnection = Settlement.gaugeConnection := by
  exact
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gaugeConnection_eq_current

/-- The diagonal auxiliary is the same live constitutive value as the
source/action-owned all-point settlement.  The only analytic input is the
regularity of an equal-connection representative of the already generated
fixed current. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gaugeAuxiliary_eq_settlement :
    U6.gaugeAuxiliary = Settlement.gaugeAuxiliary := by
  funext point
  change
    (completeJointLiveElectricECFullOccurrenceContact Source U5 point
      ).gaugeAuxiliary 0 =
      diracDualFormNativeConstitutiveAuxiliaryField Source U5 point
  unfold completeJointLiveElectricECFullOccurrenceContact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeAuxiliary]
  calc
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
        Source (fullyRecenterHolonomicConfiguration U5 point)
      ).gaugeAuxiliary 0 =
        (completeJointGlobalP286AlgebraicCurrent Source
          (fullyRecenterHolonomicConfiguration U5 point)
        ).gaugeAuxiliary 0 :=
      localLiveElectric_gaugeAuxiliary_origin_eq_algebraic point
    _ = diracDualFormNativeConstitutiveAuxiliaryField Source U5 point := by
      change
        formNativeP286GaugeEliminatedAuxiliaryAtBoundary
            (sourceGeneratedUnifiedCouplings Source)
            ((fullyRecenterHolonomicConfiguration U5 point).coframe 0)
            (holonomicGaugeCurvature
              (completeJointGlobalP286AlgebraicCurrent Source
                (fullyRecenterHolonomicConfiguration U5 point)) 0) =
          formNativeP286GaugeEliminatedAuxiliaryAtBoundary
            (sourceGeneratedUnifiedCouplings Source)
            (U5.coframe point)
            (holonomicGaugeCurvature U5 point)
      rw [fullyRecenterHolonomicConfiguration_coframe_origin,
        localAlgebraic_gaugeCurvature_origin_eq_current]

/-! ## Final two-channel residual verdict -/

private theorem fullOccurrence_coframe_eq_settlement :
    U6.coframe = Settlement.coframe := by
  change U6.coframe = U5.coframe
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe
      Source U5

private theorem fullOccurrence_scalar_eq_settlement :
    U6.scalar = Settlement.scalar := by
  change U6.scalar = U5.scalar
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_scalar_eq_current
      Source U5

private theorem fullOccurrence_matter_eq_settlement :
    U6.matter = Settlement.matter := by
  change U6.matter = U5.matter
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_matter_eq_current
      Source U5

private theorem fullOccurrence_conjugateMatter_eq_settlement :
    U6.conjugateMatter = Settlement.conjugateMatter := by
  change U6.conjugateMatter = U5.conjugateMatter
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_conjugateMatter_eq_current
      Source U5

private theorem fullOccurrence_p286EulerThreeForm_eq_settlement :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 U6 =
      holonomicFormNativeP286GaugeEulerThreeForm Source 0 Settlement := by
  apply holonomicFormNativeP286GaugeEulerThreeForm_eq_of_primitiveFields
  · exact fullOccurrence_coframe_eq_settlement
  · exact
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gaugeConnection_eq_settlement
  · exact
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gaugeAuxiliary_eq_settlement
  · exact fullOccurrence_scalar_eq_settlement
  · exact fullOccurrence_matter_eq_settlement
  · exact fullOccurrence_conjugateMatter_eq_settlement

/-- The first P286 channel of the same U6 actual is in its all-point
algebraic zero fiber wherever the generated coframe is nondegenerate. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_p286AuxiliaryResidual_zero
    (point : BasePoint)
    (nondegenerate : Matrix.det (U6.coframe point) ≠ 0) :
    (diracDualFormNativePointwiseJointResidual Source U6 point
      ).p286GaugeAuxiliary =
      0 := by
  have settlementNondegenerate :
      Matrix.det (Settlement.coframe point) ≠ 0 := by
    rw [← congrFun fullOccurrence_coframe_eq_settlement point]
    exact nondegenerate
  have settlementZero :=
    fixedP506L0CompleteJointLiveElectricECP286ConstitutiveSettlementActual_p286AuxiliaryResidual_zero
      point settlementNondegenerate
  have curvatureEq :
      holonomicGaugeCurvature U6 point =
        holonomicGaugeCurvature Settlement point :=
    holonomicGaugeCurvature_eq_of_connection_eq U6 Settlement
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gaugeConnection_eq_settlement
      point
  change
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings Source)
        (toContinuumPointField U6 point) =
      0
  simpa only [formNativeP286GaugeAuxiliaryEulerResidualAtBoundary,
    toContinuumPointField, curvatureEq,
    congrFun fullOccurrence_coframe_eq_settlement point,
    congrFun
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_gaugeAuxiliary_eq_settlement
      point] using settlementZero

/-- The second P286 channel on U6 is exactly the established algebraic
current read at every spacetime point. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_p286Connection_eq_algebraic
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual Source U6 point
      ).p286GaugeConnection =
      holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic point := by
  change holonomicFormNativeP286GaugeEulerThreeForm Source 0 U6 point = _
  calc
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 U6 point =
        holonomicFormNativeP286GaugeEulerThreeForm Source 0 Settlement point :=
      congrFun fullOccurrence_p286EulerThreeForm_eq_settlement point
    _ = holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic point :=
      congrFun
        fixedP506L0CompleteJointLiveElectricECP286ConstitutiveSettlementActual_p286EulerThreeForm_eq_algebraic
        point

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalP286Verdict
