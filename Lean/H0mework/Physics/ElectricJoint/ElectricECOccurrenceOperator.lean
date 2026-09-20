import H0mework.Physics.ElectricJoint.ElectricECFullOccurrenceContactOperator

/-!
# Global joint write assembled from every live-electric EC occurrence

The full-occurrence contact operator already reruns the same authoritative
five-leg mother action on the canonical recentering of one supplied current.
This module takes the diagonal primitive-field value of that one joint contact
family and thereby produces one four-dimensional
`StageNineHolonomicConfiguration`.

The constructor consumes exactly `(source, current)`.  It does not accept a
residual, support coordinate, target jet, branch, equation receipt, or
sector-local output.  In particular, gravity, P286, scalar, matter, and
adjoint fields are assembled in one write rather than promoted to independent
worlds.

The point-value laws below are definitional producer laws.  Equality of the
derived action jets remains a downstream naturality/assembly obligation; it
is not hidden in this constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceContactOperator
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineHolonomicField
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineP286GaugeConnectionVariation
open StageNineP286HolonomicSecondJetCarrier

noncomputable section

set_option autoImplicit false

/-! ## One source/current-only global joint write -/

/-- Assemble the primitive values generated at every recentered occurrence
into one global configuration.  Every field is read at the same local origin
of the same five-leg contact write. -/
def
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration where
  coframe := fun point =>
    (completeJointLiveElectricECFullOccurrenceContact
      source current point).coframe 0
  gravityConnection := fun point =>
    (completeJointLiveElectricECFullOccurrenceContact
      source current point).gravityConnection 0
  gravityAuxiliary := fun point =>
    (completeJointLiveElectricECFullOccurrenceContact
      source current point).gravityAuxiliary 0
  gravitySimplicityMultiplier := fun point =>
    (completeJointLiveElectricECFullOccurrenceContact
      source current point).gravitySimplicityMultiplier 0
  gaugeConnection := fun point =>
    (completeJointLiveElectricECFullOccurrenceContact
      source current point).gaugeConnection 0
  gaugeAuxiliary := fun point =>
    (completeJointLiveElectricECFullOccurrenceContact
      source current point).gaugeAuxiliary 0
  scalar := fun point =>
    (completeJointLiveElectricECFullOccurrenceContact
      source current point).scalar 0
  matter := fun point =>
    (completeJointLiveElectricECFullOccurrenceContact
      source current point).matter 0
  conjugateMatter := fun point =>
    (completeJointLiveElectricECFullOccurrenceContact
      source current point).conjugateMatter 0

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe_at
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      source current).coframe point =
      (completeJointLiveElectricECFullOccurrenceContact
        source current point).coframe 0 :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityConnection_at
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      source current).gravityConnection point =
      (completeJointLiveElectricECFullOccurrenceContact
        source current point).gravityConnection 0 :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityAuxiliary_at
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      source current).gravityAuxiliary point =
      (completeJointLiveElectricECFullOccurrenceContact
        source current point).gravityAuxiliary 0 :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_multiplier_at
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      source current).gravitySimplicityMultiplier point =
      (completeJointLiveElectricECFullOccurrenceContact
        source current point).gravitySimplicityMultiplier 0 :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gaugeConnection_at
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      source current).gaugeConnection point =
      (completeJointLiveElectricECFullOccurrenceContact
        source current point).gaugeConnection 0 :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gaugeAuxiliary_at
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      source current).gaugeAuxiliary point =
      (completeJointLiveElectricECFullOccurrenceContact
        source current point).gaugeAuxiliary 0 :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_scalar_at
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      source current).scalar point =
      (completeJointLiveElectricECFullOccurrenceContact
        source current point).scalar 0 :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_matter_at
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      source current).matter point =
      (completeJointLiveElectricECFullOccurrenceContact
        source current point).matter 0 :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_conjugateMatter_at
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      source current).conjugateMatter point =
      (completeJointLiveElectricECFullOccurrenceContact
        source current point).conjugateMatter 0 :=
  rfl

/-! ## Whole-field algebraic settlement -/

/-- The one joint global write preserves the supplied coframe as a whole
field.  This follows from the native coframe law of the complete five-leg
contact and canonical recentering; it is not a pointwise supplied seam. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      source current).coframe =
      current.coframe := by
  funext point
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe_at]
  unfold completeJointLiveElectricECFullOccurrenceContact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_coframe,
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_coframe_eq_existing,
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_coframe,
    fullyRecenterHolonomicConfiguration_coframe_origin]

/-- The occurrence-diagonal P286 leg changes only its local homogeneous
second jet.  Its assembled connection value is therefore exactly the
supplied whole connection field for every source/current pair. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gaugeConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      source current).gaugeConnection = current.gaugeConnection := by
  funext point
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gaugeConnection_at]
  unfold completeJointLiveElectricECFullOccurrenceContact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeConnection]
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeConnection]
  calc
    (completeJointGlobalP286AlgebraicCurrent source
        (fullyRecenterHolonomicConfiguration current point)
      ).gaugeConnection 0 =
        (completeJointGlobalTemporalCurrent source
          (fullyRecenterHolonomicConfiguration current point)
        ).gaugeConnection 0 := by
      let temporal := completeJointGlobalTemporalCurrent source
        (fullyRecenterHolonomicConfiguration current point)
      let write := diracDualFormNativeP286CanonicalGeneratedWrite source
        temporal
      funext direction
      apply p286CoordinateEquiv.injective
      change
        holonomicP286GaugeConnectionCoordinate
            (installP286HolonomicConnectionSecondJet temporal
              (p286CanonicalDiagonalResponseSecondJet write) 1)
            0 direction =
          holonomicP286GaugeConnectionCoordinate temporal 0 direction
      exact congrFun
        (installP286HolonomicConnectionSecondJet_connection_origin temporal
          (p286CanonicalDiagonalResponseSecondJet write) 1)
        direction
    _ = (fullyRecenterHolonomicConfiguration current point
          ).gaugeConnection 0 := rfl
    _ = current.gaugeConnection point :=
      fullyRecenterHolonomicConfiguration_gaugeConnection_origin current point

/-- The global auxiliary field is the computed `II+` of that same preserved
coframe.  Every point consumes the simplicity output of its native contact
leg. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      source current).gravityAuxiliary =
      fun point => physicalIIPlusBivector (current.coframe point) := by
  funext point
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityAuxiliary_at]
  unfold completeJointLiveElectricECFullOccurrenceContact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
  rw [
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_simplicity
      source
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
        source (fullyRecenterHolonomicConfiguration current point))
      0,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_coframe,
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_coframe_eq_existing,
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_coframe,
    fullyRecenterHolonomicConfiguration_coframe_origin]

/-- Consequently the complete global write closes the simplicity equation
at every spacetime point on one actual. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_simplicity
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    FormNativeGravitySimplicityEquation
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
        source current) := by
  intro point
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityAuxiliary,
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe]

/-! ## Fixed P506/L0 specialization -/

/-- The fixed positive-source specialization applies the joint global write
to the current authoritative `U5`.  It is one common generated actual;
contact is no longer an external index of this definition.  Promotion to the
authoritative successor remains a downstream zero-fiber decision. -/
def fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
    positiveSmoothUnifiedSource
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual_field_at
    (point : BasePoint) :
    ((fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual.coframe
          point,
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual.gravityConnection
          point),
      (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual.gravityAuxiliary
          point,
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual.gravitySimplicityMultiplier
          point),
      (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual.gaugeConnection
          point,
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual.gaugeAuxiliary
          point),
      (fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual.scalar
          point,
        fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual.matter
          point),
      fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual.conjugateMatter
        point) =
      (((fixedP506L0CompleteJointLiveElectricECFullOccurrenceContact
            point).coframe 0,
        (fixedP506L0CompleteJointLiveElectricECFullOccurrenceContact
            point).gravityConnection 0),
      ((fixedP506L0CompleteJointLiveElectricECFullOccurrenceContact
            point).gravityAuxiliary 0,
        (fixedP506L0CompleteJointLiveElectricECFullOccurrenceContact
            point).gravitySimplicityMultiplier 0),
      ((fixedP506L0CompleteJointLiveElectricECFullOccurrenceContact
            point).gaugeConnection 0,
        (fixedP506L0CompleteJointLiveElectricECFullOccurrenceContact
            point).gaugeAuxiliary 0),
      ((fixedP506L0CompleteJointLiveElectricECFullOccurrenceContact
            point).scalar 0,
        (fixedP506L0CompleteJointLiveElectricECFullOccurrenceContact
            point).matter 0),
      (fixedP506L0CompleteJointLiveElectricECFullOccurrenceContact
          point).conjugateMatter 0) :=
  rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
