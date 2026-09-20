import H0mework.Physics.GaugeAction.P286CanonicalDiagonalActionPrincipal
import H0mework.Physics.GaugeAction.P286GaugeYangMillsReadout
import H0mework.Physics.GaugeAction.TopologicalP286GaugeThreeFormDuality

/-!
# Dirac-dual form-native canonical P286 joint-action producer core

This module isolates the source/current-only producer used by the canonical
P286 connection write.  It first reads the complete mother-action covector of
the zero principal increment, applies the fixed nondegenerate action pairing,
installs the resulting holonomic connection second jet, and finally recomputes
the primitive auxiliary field from the live post-write curvature.

No residual carrier, support coordinate, endpoint, branch, target field, or
equation receipt enters a constructor.  Vanishing of the resulting action
covector is a downstream theorem and requires the appropriate coframe/action
normalization seam; it is deliberately not asserted by this dependency-light
core.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286HolonomicSecondJetCarrier
open StageNineTopologicalP286GaugeThreeFormDuality

noncomputable section

set_option autoImplicit false

/-- Install the canonical action-principal connection Hessian into one local
action input. -/
def diracDualFormNativeP286CanonicalConnectionCandidate
    (current : StageNineHolonomicConfiguration)
    (write : P286GaugeOneForm) : StageNineHolonomicConfiguration :=
  installP286HolonomicConnectionSecondJet current
    (p286CanonicalDiagonalResponseSecondJet write) 1

@[simp] theorem diracDualFormNativeP286CanonicalConnectionCandidate_zero
    (current : StageNineHolonomicConfiguration) :
    diracDualFormNativeP286CanonicalConnectionCandidate current 0 =
      current := by
  unfold diracDualFormNativeP286CanonicalConnectionCandidate
    installP286HolonomicConnectionSecondJet
  rw [map_zero, map_zero]
  apply StageNineHolonomicConfiguration.ext <;>
    simp [varyP286GaugeConnectionCoordinate,
      holonomicP286GaugeConnectionCoordinate]

/-- Recompute the primitive P286 auxiliary field from the live curvature of
the post-connection candidate. -/
def diracDualFormNativeP286CanonicalJointCandidate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (write : P286GaugeOneForm) : StageNineHolonomicConfiguration :=
  formNativeP286GaugeConstitutiveReadout source
    (diracDualFormNativeP286CanonicalConnectionCandidate current write)

/-- Complete W13 mother-action covector at the local origin of the candidate
family. -/
def diracDualFormNativeP286CanonicalOriginActionDual
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (write : P286GaugeOneForm) : Module.Dual ℝ P286GaugeOneForm :=
  p286GaugeThreeFormWedgeLinearDual
    (holonomicFormNativeP286GaugeEulerThreeForm source 0
      (diracDualFormNativeP286CanonicalJointCandidate source current write) 0)

/-- Authoritative action forcing before a new canonical principal increment
is installed. -/
def diracDualFormNativeP286CanonicalOriginActionForcing
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    Module.Dual ℝ P286GaugeOneForm :=
  diracDualFormNativeP286CanonicalOriginActionDual source current 0

/-- Branch-free, parameter-free canonical principal response selected by the
nondegenerate action pairing. -/
def diracDualFormNativeP286CanonicalGeneratedWrite
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) : P286GaugeOneForm :=
  p286GaugeOneFormPairingEquiv.symm
    (diracDualFormNativeP286CanonicalOriginActionForcing source current)

/-- One post-connection/post-constitutive local actual generated from the
same source and current. -/
def diracDualFormNativeP286CanonicalGeneratedActual
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  diracDualFormNativeP286CanonicalJointCandidate source current
    (diracDualFormNativeP286CanonicalGeneratedWrite source current)

@[simp] theorem diracDualFormNativeP286CanonicalGeneratedActual_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeP286CanonicalGeneratedActual source current).coframe =
      current.coframe :=
  rfl

@[simp] theorem
    diracDualFormNativeP286CanonicalGeneratedActual_gaugeConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (diracDualFormNativeP286CanonicalGeneratedActual source current
      ).gaugeConnection =
      (diracDualFormNativeP286CanonicalConnectionCandidate current
        (diracDualFormNativeP286CanonicalGeneratedWrite source current)
      ).gaugeConnection :=
  rfl

@[simp] theorem diracDualFormNativeP286CanonicalGeneratedActual_gaugeAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (diracDualFormNativeP286CanonicalGeneratedActual source current
      ).gaugeAuxiliary point =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        (current.coframe point)
        (holonomicGaugeCurvature
          (diracDualFormNativeP286CanonicalConnectionCandidate current
            (diracDualFormNativeP286CanonicalGeneratedWrite source current))
          point) :=
  rfl

/-- The charged P286 three-form depends only on the coframe, scalar value and
covariant first jet, and the primal/adjoint matter values at the occurrence.
This is a readout congruence for already generated action data; it does not
produce a response or accept an equation certificate. -/
theorem formNativeChargedGaugeThreeForm_eq_of_actionData_eq
    (source : SmoothUnifiedSource)
    (first second : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeEq : first.coframe point = second.coframe point)
    (scalarEq : first.scalar point = second.scalar point)
    (scalarCovariantDerivativeEq :
      holonomicScalarCovariantDerivative first point =
        holonomicScalarCovariantDerivative second point)
    (matterEq : first.matter point = second.matter point)
    (conjugateMatterEq :
      first.conjugateMatter point = second.conjugateMatter point) :
    formNativeChargedGaugeThreeForm source 0 point
        (toContinuumPointField first point) =
      formNativeChargedGaugeThreeForm source 0 point
        (toContinuumPointField second point) := by
  have volumeEq :
      generatedVolumeDensity (toContinuumPointField first point) =
        generatedVolumeDensity (toContinuumPointField second point) := by
    unfold generatedVolumeDensity
    simp only [toContinuumPointField]
    rw [coframeEq]
  have scalarKineticEq
      (variation : LorentzianIndex → ScalarCoordinateCarrier) :
      scalarGaugeConnectionKineticFirstVariationDensity source 0 point
          (toContinuumPointField first point) variation =
        scalarGaugeConnectionKineticFirstVariationDensity source 0 point
          (toContinuumPointField second point) variation := by
    unfold scalarGaugeConnectionKineticFirstVariationDensity
    simp only [toContinuumPointField]
    rw [coframeEq, scalarCovariantDerivativeEq]
  have scalarVariationEq (direction : P286GaugeOneForm) :
      pointwiseScalarP286GaugeConnectionVariation
          (toContinuumPointField first point) direction =
        pointwiseScalarP286GaugeConnectionVariation
          (toContinuumPointField second point) direction := by
    funext formDirection
    unfold pointwiseScalarP286GaugeConnectionVariation
    simp only [toContinuumPointField]
    rw [scalarEq]
  have matterVariationEq (direction : P286GaugeOneForm) :
      pointwiseMatterP286GaugeConnectionVariation
          (toContinuumPointField first point) direction =
        pointwiseMatterP286GaugeConnectionVariation
          (toContinuumPointField second point) direction := by
    funext formDirection
    unfold pointwiseMatterP286GaugeConnectionVariation
    simp only [toContinuumPointField]
    rw [matterEq]
  have matterKineticEq
      (variation : LorentzianIndex → DiracExteriorMatterCarrier) :
      matterGaugeConnectionFirstVariationDensity source 0 point
          (toContinuumPointField first point) variation =
        matterGaugeConnectionFirstVariationDensity source 0 point
          (toContinuumPointField second point) variation := by
    unfold matterGaugeConnectionFirstVariationDensity
      matterGaugeConnectionVariationVector matterGaugeKineticSum
    simp only [toContinuumPointField]
    rw [coframeEq, conjugateMatterEq]
  unfold formNativeChargedGaugeThreeForm
  apply congrArg p286GaugeThreeFormOfDual
  apply LinearMap.ext
  intro direction
  simp only [formNativeChargedGaugeFirstLinearMap_apply]
  unfold formNativeChargedGaugeFirstCoefficient
  rw [volumeEq, scalarVariationEq, matterVariationEq,
    scalarKineticEq, matterKineticEq]

/-- The canonical P286 action forcing depends on the supplied current only
through its primitive BF fields and the charged-current data actually read at
the common origin.  This theorem is an extensional producer seam: it neither
accepts a residual nor changes the generated write. -/
theorem
    diracDualFormNativeP286CanonicalOriginActionForcing_eq_of_actionData_eq
    (source : SmoothUnifiedSource)
    (first second : StageNineHolonomicConfiguration)
    (coframeEq : first.coframe = second.coframe)
    (gaugeConnectionEq :
      first.gaugeConnection = second.gaugeConnection)
    (scalarOriginEq : first.scalar 0 = second.scalar 0)
    (scalarCovariantDerivativeOriginEq :
      holonomicScalarCovariantDerivative first 0 =
        holonomicScalarCovariantDerivative second 0)
    (matterOriginEq : first.matter 0 = second.matter 0)
    (conjugateMatterOriginEq :
      first.conjugateMatter 0 = second.conjugateMatter 0) :
    diracDualFormNativeP286CanonicalOriginActionForcing source first =
      diracDualFormNativeP286CanonicalOriginActionForcing source second := by
  let firstCandidate :=
    diracDualFormNativeP286CanonicalJointCandidate source first 0
  let secondCandidate :=
    diracDualFormNativeP286CanonicalJointCandidate source second 0
  have candidateConnectionEq :
      firstCandidate.gaugeConnection =
        secondCandidate.gaugeConnection := by
    change
      (diracDualFormNativeP286CanonicalConnectionCandidate first 0
        ).gaugeConnection =
      (diracDualFormNativeP286CanonicalConnectionCandidate second 0
        ).gaugeConnection
    rw [diracDualFormNativeP286CanonicalConnectionCandidate_zero,
      diracDualFormNativeP286CanonicalConnectionCandidate_zero,
      gaugeConnectionEq]
  have candidateAuxiliaryEq :
      firstCandidate.gaugeAuxiliary =
        secondCandidate.gaugeAuxiliary := by
    funext point pair
    dsimp [firstCandidate, secondCandidate,
      diracDualFormNativeP286CanonicalJointCandidate,
      formNativeP286GaugeConstitutiveReadout]
    rw [diracDualFormNativeP286CanonicalConnectionCandidate_zero,
      diracDualFormNativeP286CanonicalConnectionCandidate_zero]
    rw [coframeEq]
    have curvatureEq :
        holonomicGaugeCurvature first point =
          holonomicGaugeCurvature second point := by
      unfold holonomicGaugeCurvature p286ConnectionDerivative
      rw [gaugeConnectionEq]
    rw [curvatureEq]
  have candidateCoordinateEq :
      holonomicP286GaugeAuxiliaryCoordinate firstCandidate =
        holonomicP286GaugeAuxiliaryCoordinate secondCandidate := by
    funext point pair
    unfold holonomicP286GaugeAuxiliaryCoordinate
    rw [candidateAuxiliaryEq]
  have candidateCovariantDerivativeEq :
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
          firstCandidate 0 =
        holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
          secondCandidate 0 := by
    have connectionCoordinateEq :
        holonomicP286GaugeConnectionCoordinate firstCandidate 0 =
          holonomicP286GaugeConnectionCoordinate secondCandidate 0 := by
      unfold holonomicP286GaugeConnectionCoordinate
      rw [candidateConnectionEq]
    have derivativeEq :
        p286GaugeAuxiliaryDirectionalDerivative firstCandidate 0 =
          p286GaugeAuxiliaryDirectionalDerivative secondCandidate 0 := by
      unfold p286GaugeAuxiliaryDirectionalDerivative
      rw [candidateCoordinateEq]
    unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    rw [connectionCoordinateEq, congrFun candidateCoordinateEq 0,
      derivativeEq]
  have candidateChargedEq :
      formNativeChargedGaugeThreeForm source 0 0
          (toContinuumPointField firstCandidate 0) =
        formNativeChargedGaugeThreeForm source 0 0
          (toContinuumPointField secondCandidate 0) := by
    have candidateCoframeOriginEq :
        firstCandidate.coframe 0 = secondCandidate.coframe 0 := by
      exact congrFun coframeEq 0
    have candidateScalarOriginEq :
        firstCandidate.scalar 0 = secondCandidate.scalar 0 := by
      exact scalarOriginEq
    have candidateScalarCovariantDerivativeOriginEq :
        holonomicScalarCovariantDerivative firstCandidate 0 =
          holonomicScalarCovariantDerivative secondCandidate 0 := by
      have firstCandidateEq :
          firstCandidate =
            formNativeP286GaugeConstitutiveReadout source first := by
        dsimp [firstCandidate,
          diracDualFormNativeP286CanonicalJointCandidate]
        rw [diracDualFormNativeP286CanonicalConnectionCandidate_zero]
      have secondCandidateEq :
          secondCandidate =
            formNativeP286GaugeConstitutiveReadout source second := by
        dsimp [secondCandidate,
          diracDualFormNativeP286CanonicalJointCandidate]
        rw [diracDualFormNativeP286CanonicalConnectionCandidate_zero]
      rw [firstCandidateEq, secondCandidateEq]
      change
        holonomicScalarCovariantDerivative first 0 =
          holonomicScalarCovariantDerivative second 0
      exact scalarCovariantDerivativeOriginEq
    have candidateMatterOriginEq :
        firstCandidate.matter 0 = secondCandidate.matter 0 := by
      exact matterOriginEq
    have candidateConjugateMatterOriginEq :
        firstCandidate.conjugateMatter 0 =
          secondCandidate.conjugateMatter 0 := by
      exact conjugateMatterOriginEq
    apply formNativeChargedGaugeThreeForm_eq_of_actionData_eq
    · exact candidateCoframeOriginEq
    · exact candidateScalarOriginEq
    · exact candidateScalarCovariantDerivativeOriginEq
    · exact candidateMatterOriginEq
    · exact candidateConjugateMatterOriginEq
  unfold diracDualFormNativeP286CanonicalOriginActionForcing
    diracDualFormNativeP286CanonicalOriginActionDual
  apply congrArg p286GaugeThreeFormWedgeLinearDual
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [candidateCovariantDerivativeEq, candidateChargedEq]

/-- Therefore currents with the same action data generate the same unique
canonical P286 write. -/
theorem diracDualFormNativeP286CanonicalGeneratedWrite_eq_of_actionData_eq
    (source : SmoothUnifiedSource)
    (first second : StageNineHolonomicConfiguration)
    (coframeEq : first.coframe = second.coframe)
    (gaugeConnectionEq :
      first.gaugeConnection = second.gaugeConnection)
    (scalarOriginEq : first.scalar 0 = second.scalar 0)
    (scalarCovariantDerivativeOriginEq :
      holonomicScalarCovariantDerivative first 0 =
        holonomicScalarCovariantDerivative second 0)
    (matterOriginEq : first.matter 0 = second.matter 0)
    (conjugateMatterOriginEq :
      first.conjugateMatter 0 = second.conjugateMatter 0) :
    diracDualFormNativeP286CanonicalGeneratedWrite source first =
      diracDualFormNativeP286CanonicalGeneratedWrite source second := by
  unfold diracDualFormNativeP286CanonicalGeneratedWrite
  rw [
    diracDualFormNativeP286CanonicalOriginActionForcing_eq_of_actionData_eq
      source first second coframeEq gaugeConnectionEq scalarOriginEq
      scalarCovariantDerivativeOriginEq matterOriginEq
      conjugateMatterOriginEq]

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
