import H0mework.Physics.JointVariation.P286CanonicalOccurrenceWriteProfile
import H0mework.Physics.JointVariation.SectionOperator
import H0mework.Physics.ElectricJoint.ElectricECOccurrenceOperator

/-!
# Complete-joint P286 occurrence second-jet global installation boundary

The complete-joint action already generates one source/current-owned P286
write at every recentered spacetime occurrence.  The local algebraic candidate
installs its canonical second jet, and the later live-electric and
Einstein--Cartan contact legs preserve that local primitive connection.

The two existing global diagonals do not assemble those local second jets into
one new primitive connection whole field.  The spacetime-section operator has
an existing public connection-preservation theorem; the full-occurrence writer
is proved connection-preserving below.  Its point-value diagonal therefore
forgets the locally installed Hessian increment.

The final section declares the exact acceptance mouth for a future whole-field
realization.  It is a property that an explicit source/current-generated
increment must prove, not an input certificate.  In particular, residual
coordinates such as a later fixed `123`/hypercharge read do not occur in the
profile or in this acceptance mouth.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointP286OccurrenceSecondJetGlobalInstallationBoundary

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeCompleteJointP286CanonicalOccurrenceWriteProfile
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineEnrichedProofFreeSource
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineHolonomicField
open StageNineP286Bianchi
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineP286ConstitutiveSecondJetResponse
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286HolonomicSecondJetCarrier
open SU7MotherLieAlgebra
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

/-! ## Authoritative occurrence provenance -/

/-- The occurrence write is exactly the inverse action-pairing image of the
origin mother-action forcing of the recentered temporal actual.  This theorem
exposes the full producer provenance without mentioning any residual read. -/
theorem completeJointP286CanonicalOccurrenceWriteProfile_eq_actionForcing
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    completeJointP286CanonicalOccurrenceWriteProfile source current point =
      p286GaugeOneFormPairingEquiv.symm
        (diracDualFormNativeP286CanonicalOriginActionForcing source
          (completeJointGlobalTemporalCurrent source
            (fullyRecenterHolonomicConfiguration current point))) :=
  rfl

/-- Applying the faithful action pairing to the generated occurrence write
recovers the authoritative mother-action forcing itself. -/
theorem completeJointP286CanonicalOccurrenceWriteProfile_pairingDual_eq_actionForcing
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    p286GaugeOneFormPairingDual
        (completeJointP286CanonicalOccurrenceWriteProfile source current point) =
      diracDualFormNativeP286CanonicalOriginActionForcing source
        (completeJointGlobalTemporalCurrent source
          (fullyRecenterHolonomicConfiguration current point)) := by
  change p286GaugeOneFormPairingEquiv
      (completeJointP286CanonicalOccurrenceWriteProfile source current point) = _
  rw [completeJointP286CanonicalOccurrenceWriteProfile_eq_actionForcing]
  exact p286GaugeOneFormPairingEquiv.apply_symm_apply _

/-! ## Exact local installation -/

/-- At every recentered occurrence, the algebraic P286 leg installs exactly
the source/current-generated occurrence second jet before recomputing the
constitutive auxiliary. -/
theorem
    completeJointGlobalP286AlgebraicCurrent_fullyRecenter_eq_installedOccurrenceSecondJet
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    completeJointGlobalP286AlgebraicCurrent source
        (fullyRecenterHolonomicConfiguration current point) =
      formNativeP286GaugeConstitutiveReadout source
        (installP286HolonomicConnectionSecondJet
          (completeJointGlobalTemporalCurrent source
            (fullyRecenterHolonomicConfiguration current point))
          (completeJointP286CanonicalOccurrenceSecondJetProfile
            source current point)
          1) :=
  rfl

/-- The later live-electric and Einstein--Cartan local legs preserve the
installed local connection whole field.  Hence the local occurrence contact
still contains the action-generated second jet. -/
theorem fullOccurrenceContact_gaugeConnection_eq_installedOccurrenceSecondJet
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (completeJointLiveElectricECFullOccurrenceContact
        source current point).gaugeConnection =
      (formNativeP286GaugeConstitutiveReadout source
        (installP286HolonomicConnectionSecondJet
          (completeJointGlobalTemporalCurrent source
            (fullyRecenterHolonomicConfiguration current point))
          (completeJointP286CanonicalOccurrenceSecondJetProfile
            source current point)
          1)).gaugeConnection := by
  unfold completeJointLiveElectricECFullOccurrenceContact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeConnection]
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeConnection]
  exact congrArg StageNineHolonomicConfiguration.gaugeConnection
    (completeJointGlobalP286AlgebraicCurrent_fullyRecenter_eq_installedOccurrenceSecondJet
      source current point)

/-! ## Existing global diagonals lose the local Hessian increment -/

/-- The full-occurrence point-value diagonal preserves the supplied primitive
P286 connection whole field.  It therefore does not transport a newly
installed occurrence-local Hessian increment into the assembled global
connection. -/
theorem fullOccurrenceGlobal_gaugeConnection_eq_current
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
        (fullyRecenterHolonomicConfiguration current point)).gaugeConnection 0 =
        (completeJointGlobalTemporalCurrent source
          (fullyRecenterHolonomicConfiguration current point)
        ).gaugeConnection 0 := by
      unfold completeJointGlobalP286AlgebraicCurrent
        diracDualFormNativeP286CanonicalGeneratedActual
        diracDualFormNativeP286CanonicalJointCandidate
        diracDualFormNativeP286CanonicalConnectionCandidate
      rw [formNativeP286GaugeConstitutiveReadout_gaugeConnection]
      funext direction
      apply p286CoordinateEquiv.injective
      exact congrFun
        (installP286HolonomicConnectionSecondJet_connection_origin
          (completeJointGlobalTemporalCurrent source
            (fullyRecenterHolonomicConfiguration current point))
          (p286CanonicalDiagonalResponseSecondJet
            (diracDualFormNativeP286CanonicalGeneratedWrite source
              (completeJointGlobalTemporalCurrent source
                (fullyRecenterHolonomicConfiguration current point))))
          1)
        direction
    _ = (fullyRecenterHolonomicConfiguration current point).gaugeConnection 0 :=
      rfl
    _ = current.gaugeConnection point :=
      fullyRecenterHolonomicConfiguration_gaugeConnection_origin current point

/-! ## Whole-field realization acceptance -/

/-- Strong canonical-representative acceptance property for one proposed
whole-field connection increment.  The increment must be twice differentiable
and its physical Hessian at every occurrence must equal the particular local
canonical-diagonal section selected at that occurrence.

This predicate is intended as a theorem conclusion about an explicit
source/current-only construction.  Supplying it as a premise would merely
move the global integrability obligation into a receipt.  It is sufficient
but not necessary for action closure: a different globally integrable Hessian
may generate the same authoritative action forcing. -/
def CompleteJointP286OccurrenceIncrementRealizesSecondJetProfile
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (increment : BasePoint → P286GaugeOneForm) : Prop :=
  ContDiff ℝ 2 increment ∧
    ∀ point outerDirection innerDirection,
      (fderiv ℝ
          (fun candidate =>
            fderiv ℝ increment candidate innerDirection)
          point) outerDirection =
        (completeJointP286CanonicalOccurrenceSecondJetProfile
          source current point).1 outerDirection innerDirection

/-- Action-jurisdiction acceptance for an explicit whole-field increment and
its explicit holonomic Hessian profile.  The Hessian need not equal the local
canonical-diagonal representative: it must be the actual second derivative
of the one global field and generate exactly the same mother-action forcing at
every occurrence.

Both the increment and profile are outputs to be constructed from the source
and current before this predicate is proved.  Neither may be supplied as a
target certificate or selected from residual support. -/
def CompleteJointP286OccurrenceIncrementRealizesActionForcing
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (increment : BasePoint → P286GaugeOneForm)
    (jetProfile : BasePoint → P286HolonomicConnectionSecondJet) : Prop :=
  ContDiff ℝ 2 increment ∧
    (∀ point outerDirection innerDirection,
      (fderiv ℝ
          (fun candidate =>
            fderiv ℝ increment candidate innerDirection)
          point) outerDirection =
        (jetProfile point).1 outerDirection innerDirection) ∧
    ∀ point,
      p286HolonomicSecondJetEulerLagrangeResponse (jetProfile point) =
        diracDualFormNativeP286CanonicalOriginActionForcing source
          (completeJointGlobalTemporalCurrent source
            (fullyRecenterHolonomicConfiguration current point))

/-- Typed zero-slice linearity question for an occurrence write profile.  Two
values of a downstream residual do not inhabit this predicate: it requires a
single spatial linear map whose value is the authoritative action write at
every point of the zero slice. -/
def CompleteJointP286OccurrenceWriteProfileZeroSliceSpatialLinear
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) : Prop :=
  ∃ spatialWrite : StageNineSpatialPoint →ₗ[ℝ] P286GaugeOneForm,
    ∀ spatialPoint,
      completeJointP286CanonicalOccurrenceWriteProfile source current
          (canonicalCauchySlicePoint 0 spatialPoint) =
        spatialWrite spatialPoint

/-- Strong global integration gate for the particular canonical-diagonal
representative.  This remains a useful sufficient target, but action closure
may instead use the action-forcing gate below. -/
def CompleteJointP286OccurrenceSecondJetProfileGloballyIntegrable
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) : Prop :=
  ∃ increment : BasePoint → P286GaugeOneForm,
    CompleteJointP286OccurrenceIncrementRealizesSecondJetProfile
      source current increment

/-- Global action-principal integration gate.  Existence is only the target
shape: a concrete source/current producer must first construct both the field
and its holonomic Hessian profile, then prove this predicate. -/
def CompleteJointP286OccurrenceActionForcingGloballyIntegrable
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) : Prop :=
  ∃ increment : BasePoint → P286GaugeOneForm,
    ∃ jetProfile : BasePoint → P286HolonomicConnectionSecondJet,
      CompleteJointP286OccurrenceIncrementRealizesActionForcing
        source current increment jetProfile

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointP286OccurrenceSecondJetGlobalInstallationBoundary
