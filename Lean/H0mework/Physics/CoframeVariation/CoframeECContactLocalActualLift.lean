import H0mework.Physics.CoframeVariation.CoframeECCurvatureNormalSection
import H0mework.Physics.DualVariation.FourLegCriticalLocusCorrespondence
import H0mework.Physics.CoframeVariation.IIPlusCoframeECBalance
import H0mework.Physics.GravitySource.NormalizedAffineConnectionGerm

/-!
# Occurrence-native EC action write at a nondegenerate coframe contact

This module lifts the coframe-covariant EC normal section to a primitive
holonomic connection germ at an arbitrary spacetime contact:

```text
(source, current, contact)
  -> live II+ contact field and mother-action coframe load
  -> canonical EC curvature target at current.coframe(contact)
  -> contact-centered primitive Lorentz connection
  -> live gravity reaction
  -> one exposed local actual.
```

The constructor is total and consumes only `(source, current, contact)`.
Nondegeneracy is used only by the readback theorem proving that the generated
contact lies in the zero fiber.  No residual, residual support, target,
curvature, response, coefficient, inverse witness, branch, equation, or
stationarity receipt is accepted.

The centered affine connection is the translated version of the existing
normalization-forced primitive germ.  Its proof is repeated in this
dependency-light current-action module so the old synchronized
linear-Plebanski response operator is not imported as action authority.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCoframeECContactLocalActualLift

open ProofFreeRicherAnholonomicSource
open StageNineCartanTangentSimplicityResponse
open StageNineDiracDualFormNativeCoframeECCurvatureNormalSection
open StageNineDiracDualFormNativeCoframeIntegratedVariation
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeFourLegCriticalLocusCorrespondence
open StageNineDiracDualFormNativeIIPlusCoframeECBalance
open StageNineDiracDualFormNativeIIPlusReductionLocalVariation
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineIIPlusRestriction
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineTopologicalFourFormPairing
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Dependency-light centered primitive connection -/

def coframeECContactCenteredNormalizedAffineLorentzConnectionField
    (contact : BasePoint)
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector) :
    LorentzConnectionField :=
  fun point =>
    normalizedAffineLorentzConnectionField omega0 target (point - contact)

def coframeECContactCenteredNormalizedAffineConfiguration
    (contact : BasePoint)
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector) :
    StageNineHolonomicConfiguration :=
  configurationOfLorentzConnection
    (coframeECContactCenteredNormalizedAffineLorentzConnectionField
      contact omega0 target)

@[simp] theorem
    coframeECContactCenteredNormalizedAffineLorentzConnectionField_contact
    (contact : BasePoint)
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector) :
    coframeECContactCenteredNormalizedAffineLorentzConnectionField
        contact omega0 target contact =
      omega0 := by
  simp [coframeECContactCenteredNormalizedAffineLorentzConnectionField]

private theorem coframeEC_fderiv_comp_sub_contact
    (field : BasePoint → ℝ)
    (contact : BasePoint)
    (fieldDifferentiable : DifferentiableAt ℝ field 0) :
    fderiv ℝ (fun point => field (point - contact)) contact =
      fderiv ℝ field 0 := by
  have shiftDerivative :
      HasFDerivAt (fun point : BasePoint => point - contact)
        (ContinuousLinearMap.id ℝ BasePoint) contact :=
    hasFDerivAt_sub_const contact
  have fieldDerivativeAtShiftedContact :
      HasFDerivAt field (fderiv ℝ field 0) (contact - contact) := by
    simpa using fieldDifferentiable.hasFDerivAt
  have compositeDerivative :=
    HasFDerivAt.comp (f := fun point : BasePoint => point - contact) contact
      fieldDerivativeAtShiftedContact shiftDerivative
  change
    fderiv ℝ (field ∘ fun point : BasePoint => point - contact) contact =
      fderiv ℝ field 0
  simpa only [ContinuousLinearMap.comp_id] using compositeDerivative.fderiv

theorem
    gravityConnectionDerivative_coframeECContactCentered_contact
    (contact : BasePoint)
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector)
    (derivativeDirection formDirection internalOut internalIn :
      LorentzianIndex) :
    gravityConnectionDerivative
        (coframeECContactCenteredNormalizedAffineConfiguration
          contact omega0 target)
        contact derivativeDirection formDirection internalOut internalIn =
      gravityConnectionDerivative
        (normalizedAffineConfiguration omega0 target)
        0 derivativeDirection formDirection internalOut internalIn := by
  unfold gravityConnectionDerivative
    coframeECContactCenteredNormalizedAffineConfiguration
    coframeECContactCenteredNormalizedAffineLorentzConnectionField
    configurationOfLorentzConnection
    normalizedAffineConfiguration
  change
    fderiv ℝ
      ((fun candidate =>
          normalizedAffineLorentzConnectionField omega0 target candidate
            formDirection internalOut internalIn) ∘
        fun candidate : BasePoint => candidate - contact)
      contact (coordinateDirection derivativeDirection) =
    fderiv ℝ
      (fun candidate =>
        normalizedAffineLorentzConnectionField omega0 target candidate
          formDirection internalOut internalIn)
      0 (coordinateDirection derivativeDirection)
  have componentDifferentiable :
      DifferentiableAt ℝ
        (fun candidate =>
          normalizedAffineLorentzConnectionField omega0 target candidate
            formDirection internalOut internalIn)
        0 :=
    ((normalizedAffineLorentzConnectionField_smooth omega0 target
      formDirection internalOut internalIn).differentiable
        (by simp)).differentiableAt
  exact congrArg
    (fun derivative : BasePoint →L[ℝ] ℝ =>
      derivative (coordinateDirection derivativeDirection))
    (coframeEC_fderiv_comp_sub_contact
      (fun candidate =>
        normalizedAffineLorentzConnectionField omega0 target candidate
          formDirection internalOut internalIn)
      contact componentDifferentiable)

/-- The centered primitive connection realizes the supplied target at its
contact.  In the action producer below the target is not supplied by a
caller; it is generated from `(source, current, contact)`. -/
theorem
    holonomicGravityCurvature_coframeECContactCenteredNormalizedAffine_contact
    (contact : BasePoint)
    (omega0 : PointwiseLorentzSpinConnection)
    (target : PhysicalBivector) :
    holonomicGravityCurvature
        (coframeECContactCenteredNormalizedAffineConfiguration
          contact omega0 target)
        contact =
      target := by
  calc
    holonomicGravityCurvature
        (coframeECContactCenteredNormalizedAffineConfiguration
          contact omega0 target)
        contact =
        holonomicGravityCurvature
          (normalizedAffineConfiguration omega0 target) 0 := by
      funext internalPair spacetimePair
      unfold holonomicGravityCurvature
      dsimp only
      rw [
        gravityConnectionDerivative_coframeECContactCentered_contact,
        gravityConnectionDerivative_coframeECContactCentered_contact]
      simp only [
        coframeECContactCenteredNormalizedAffineConfiguration,
        configurationOfLorentzConnection,
        coframeECContactCenteredNormalizedAffineLorentzConnectionField_contact,
        normalizedAffineConfiguration,
        normalizedAffineLorentzConnectionField_zero]
    _ = target :=
      holonomicGravityCurvature_normalizedAffineConfiguration_zero
        omega0 target

/-! ## Source/current/contact-only action data -/

/-- Recompute `B := II+(e)` before reading the current mother-action load. -/
def diracDualFormNativeCoframeECContactPreparedActual
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  restrictHolonomicConfigurationToIIPlus current

def diracDualFormNativeCoframeECContactField
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    StageNineContinuumPointField :=
  restrictContinuumPointFieldToIIPlus
    (toContinuumPointField
      (diracDualFormNativeCoframeECContactPreparedActual current)
      contact)

/-- Curvature-independent part of the current repaired mother-action
coframe covector at one actual contact. -/
def diracDualFormNativeCoframeECContactLoad
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    LorentzianCoframe →L[ℝ] ℝ :=
  coframeDiracDualECCurvatureObservation
      (current.coframe contact)
      (gravityInternalPairVarianceNormalization
        (coframeWedge (current.coframe contact))) +
    diracDualFormNativeCoframeGaugeEulerCovector source
      (diracDualFormNativeCoframeECContactField current contact) +
    diracDualFormNativeCoframeMatterEulerCovector source contact
      (diracDualFormNativeCoframeECContactField current contact)

/-- Canonical branch-free curvature target generated from the current
curvature kernel and the opposite live mother-action load. -/
def diracDualFormNativeCoframeECContactCurvatureTarget
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    PhysicalBivector :=
  coframeDiracDualECCurvatureTarget
    (current.coframe contact)
    (holonomicGravityCurvature
      (diracDualFormNativeCoframeECContactPreparedActual current)
      contact)
    (-diracDualFormNativeCoframeECContactLoad source current contact)

/-- Install the generated curvature while preserving the current primitive
connection value at the selected contact. -/
def diracDualFormNativeCoframeECContactConnectedActual
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  { diracDualFormNativeCoframeECContactPreparedActual current with
    gravityConnection :=
      coframeECContactCenteredNormalizedAffineLorentzConnectionField contact
        ((diracDualFormNativeCoframeECContactPreparedActual current
          ).gravityConnection contact)
        (diracDualFormNativeCoframeECContactCurvatureTarget
          source current contact) }

/-- Public occurrence-native write.  The live gravity reaction is recomputed
after the primitive connection and computed `II+` auxiliary are installed. -/
def sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    StageNineHolonomicConfiguration :=
  { diracDualFormNativeCoframeECContactConnectedActual
      source current contact with
    gravitySimplicityMultiplier :=
      formNativeGravityReactionField
        (diracDualFormNativeCoframeECContactConnectedActual
          source current contact) }

/-! ## Primitive fidelity and generated curvature -/

@[simp] theorem
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
      source current contact).coframe =
      current.coframe :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_auxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact point : BasePoint) :
    (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
      source current contact).gravityAuxiliary point =
      physicalIIPlusBivector (current.coframe point) :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_connection_contact
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
      source current contact).gravityConnection contact =
      current.gravityConnection contact := by
  exact
    coframeECContactCenteredNormalizedAffineLorentzConnectionField_contact
      contact
      ((diracDualFormNativeCoframeECContactPreparedActual current
        ).gravityConnection contact)
      (diracDualFormNativeCoframeECContactCurvatureTarget
        source current contact)

theorem
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_curvature_contact
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    holonomicGravityCurvature
        (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
          source current contact)
        contact =
      diracDualFormNativeCoframeECContactCurvatureTarget
        source current contact := by
  change
    holonomicGravityCurvature
      (coframeECContactCenteredNormalizedAffineConfiguration contact
        ((diracDualFormNativeCoframeECContactPreparedActual current
          ).gravityConnection contact)
        (diracDualFormNativeCoframeECContactCurvatureTarget
          source current contact))
      contact =
    diracDualFormNativeCoframeECContactCurvatureTarget
      source current contact
  exact
    holonomicGravityCurvature_coframeECContactCenteredNormalizedAffine_contact
      contact
      ((diracDualFormNativeCoframeECContactPreparedActual current
        ).gravityConnection contact)
      (diracDualFormNativeCoframeECContactCurvatureTarget
        source current contact)

/-- The primitive write realizes exactly the mother-action observation
generated from the same `(source, current, contact)`. -/
theorem
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_curvatureObservation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint)
    (nondegenerate : Matrix.det (current.coframe contact) ≠ 0) :
    coframeDiracDualECCurvatureObservation
        (current.coframe contact)
        (holonomicGravityCurvature
          (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
            source current contact)
          contact) =
      -diracDualFormNativeCoframeECContactLoad
        source current contact := by
  rw [
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_curvature_contact]
  exact coframeDiracDualECCurvatureObservation_target
    (current.coframe contact) nondegenerate _ _

/-- The write retains the complete action-invisible curvature responsibility
at the selected contact. -/
theorem
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_kernelFaithful
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint)
    (nondegenerate : Matrix.det (current.coframe contact) ≠ 0) :
    coframeDiracDualECCurvatureKernelPart
        (current.coframe contact)
        (holonomicGravityCurvature
          (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
            source current contact)
          contact) =
      coframeDiracDualECCurvatureKernelPart
        (current.coframe contact)
        (holonomicGravityCurvature
          (diracDualFormNativeCoframeECContactPreparedActual current)
          contact) := by
  rw [
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_curvature_contact]
  exact coframeDiracDualECCurvatureKernelPart_target
    (current.coframe contact) nondegenerate _ _

/-! ## Simplicity, live reaction, and same-contact load stability -/

theorem
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_simplicity
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    FormNativeGravitySimplicityEquation
      (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
        source current contact) := by
  intro point
  rfl

theorem
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_reactionSelfGenerated
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
      source current contact).gravitySimplicityMultiplier =
      formNativeGravityReactionField
        (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
          source current contact) :=
  rfl

theorem
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_auxiliaryEquation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    FormNativeGravityAuxiliaryEquation
      (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
        source current contact) := by
  exact
    (formNativeGravityAuxiliaryEquation_iff_multiplier_eq_reaction
      (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
        source current contact)).2
      (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_reactionSelfGenerated
        source current contact)

private def coframeECNonGravityContactProjection
    (field : StageNineContinuumPointField) :
    StageNineContinuumPointField :=
  { field with
    gravityCurvature := 0
    gravityAuxiliary := 0
    gravitySimplicityMultiplier := 0 }

private theorem
    diracDualFormNativeCoframeGaugeDensity_coframeECProjection
    (source : SmoothUnifiedSource)
    (field : StageNineContinuumPointField) :
    diracDualFormNativeCoframeGaugeDensity source
        (coframeECNonGravityContactProjection field) =
      diracDualFormNativeCoframeGaugeDensity source field := by
  rfl

private theorem
    diracDualFormNativeCoframeMatterDensity_coframeECProjection
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField) :
    diracDualFormNativeCoframeMatterDensity source point
        (coframeECNonGravityContactProjection field) =
      diracDualFormNativeCoframeMatterDensity source point field := by
  rfl

private theorem
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_ecProjection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    coframeECNonGravityContactProjection
        (restrictContinuumPointFieldToIIPlus
          (toContinuumPointField
            (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
              source current contact)
            contact)) =
      coframeECNonGravityContactProjection
        (diracDualFormNativeCoframeECContactField current contact) := by
  apply StageNineContinuumPointField.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · funext direction
    change
      holonomicMatterCovariantDerivative
          (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
            source current contact)
          contact direction =
        holonomicMatterCovariantDerivative
          (diracDualFormNativeCoframeECContactPreparedActual current)
          contact direction
    unfold holonomicMatterCovariantDerivative
    rw [
      sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_connection_contact]
    rfl
  · rfl

theorem
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_gaugeEuler_contact
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    diracDualFormNativeCoframeGaugeEulerCovector source
        (restrictContinuumPointFieldToIIPlus
          (toContinuumPointField
            (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
              source current contact)
            contact)) =
      diracDualFormNativeCoframeGaugeEulerCovector source
        (diracDualFormNativeCoframeECContactField current contact) := by
  let finalField :=
    restrictContinuumPointFieldToIIPlus
      (toContinuumPointField
        (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
          source current contact)
        contact)
  let contactField :=
    diracDualFormNativeCoframeECContactField current contact
  have projected :
      coframeECNonGravityContactProjection finalField =
        coframeECNonGravityContactProjection contactField :=
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_ecProjection
      source current contact
  have densityEquality :
      diracDualFormNativeCoframeGaugeDensity source finalField =
        diracDualFormNativeCoframeGaugeDensity source contactField := by
    rw [←
        diracDualFormNativeCoframeGaugeDensity_coframeECProjection
          source finalField,
      projected,
      diracDualFormNativeCoframeGaugeDensity_coframeECProjection
        source contactField]
  unfold diracDualFormNativeCoframeGaugeEulerCovector
  rw [densityEquality]
  rfl

theorem
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_matterEuler_contact
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    diracDualFormNativeCoframeMatterEulerCovector source contact
        (restrictContinuumPointFieldToIIPlus
          (toContinuumPointField
            (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
              source current contact)
            contact)) =
      diracDualFormNativeCoframeMatterEulerCovector source contact
        (diracDualFormNativeCoframeECContactField current contact) := by
  let finalField :=
    restrictContinuumPointFieldToIIPlus
      (toContinuumPointField
        (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
          source current contact)
        contact)
  let contactField :=
    diracDualFormNativeCoframeECContactField current contact
  have projected :
      coframeECNonGravityContactProjection finalField =
        coframeECNonGravityContactProjection contactField :=
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_ecProjection
      source current contact
  have densityEquality :
      diracDualFormNativeCoframeMatterDensity source contact finalField =
        diracDualFormNativeCoframeMatterDensity source contact contactField := by
    rw [←
        diracDualFormNativeCoframeMatterDensity_coframeECProjection
          source contact finalField,
      projected,
      diracDualFormNativeCoframeMatterDensity_coframeECProjection
        source contact contactField]
  unfold diracDualFormNativeCoframeMatterEulerCovector
  rw [densityEquality]
  rfl

theorem
    coframeDiracDualECCurvatureObservation_intrinsic_apply
    (coframe variation : LorentzianCoframe) :
    coframeDiracDualECCurvatureObservation coframe
        (gravityInternalPairVarianceNormalization
          (coframeWedge coframe)) variation =
      gravityTopologicalWedgeCoefficient
        (physicalIIPlusCoframeTangent coframe variation)
        (coframeWedge coframe) := by
  change
    gravityTopologicalWedgeCoefficient
        (physicalIIPlusCoframeTangent coframe variation)
        (gravityInternalPairVarianceNormalization
          (gravityInternalPairVarianceNormalization
            (coframeWedge coframe))) =
      _
  rw [gravityInternalPairVarianceNormalization_involutive]

/-! ## Same-contact EC zero fiber -/

/-- The single generated actual closes the complete reduced EC balance at
the selected nondegenerate contact. -/
theorem
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_ECBalance_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint)
    (nondegenerate : Matrix.det (current.coframe contact) ≠ 0)
    (variation : LorentzianCoframe) :
    gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent
            ((sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
              source current contact).coframe contact)
            variation)
          (gravityInternalPairVarianceNormalization
              (toContinuumPointField
                (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
                  source current contact)
                contact).gravityCurvature +
            coframeWedge
              ((sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
                source current contact).coframe contact)) +
        diracDualFormNativeCoframeGaugeEulerCovector source
          (restrictContinuumPointFieldToIIPlus
            (toContinuumPointField
              (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
                source current contact)
              contact))
          variation +
        diracDualFormNativeCoframeMatterEulerCovector source contact
          (restrictContinuumPointFieldToIIPlus
            (toContinuumPointField
              (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
                source current contact)
              contact))
          variation =
      0 := by
  rw [
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_coframe]
  rw [gravityTopologicalWedgeCoefficient_add_right]
  have curvatureObservation := congrArg
    (fun covector : LorentzianCoframe →L[ℝ] ℝ =>
      covector variation)
    (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_curvatureObservation
      source current contact nondegenerate)
  have gaugeEquality := DFunLike.congr_fun
    (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_gaugeEuler_contact
      source current contact)
    variation
  have matterEquality := DFunLike.congr_fun
    (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_matterEuler_contact
      source current contact)
    variation
  rw [show
      gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent
            (current.coframe contact) variation)
          (gravityInternalPairVarianceNormalization
            (toContinuumPointField
              (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
                source current contact)
              contact).gravityCurvature) =
        coframeDiracDualECCurvatureObservation
          (current.coframe contact)
          (holonomicGravityCurvature
            (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
              source current contact)
            contact)
          variation by
      rfl]
  rw [curvatureObservation, gaugeEquality, matterEquality]
  rw [←
    coframeDiracDualECCurvatureObservation_intrinsic_apply
      (current.coframe contact) variation]
  unfold diracDualFormNativeCoframeECContactLoad
  simp only [add_apply, neg_apply]
  abel

theorem
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_reducedFirstVariation_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint)
    (nondegenerate : Matrix.det (current.coframe contact) ≠ 0)
    (variation : LorentzianCoframe) :
    diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity
        source contact
        (toContinuumPointField
          (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
            source current contact)
          contact)
        variation =
      0 := by
  rw [
    diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_EC_balance
      source contact
      (toContinuumPointField
        (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
          source current contact)
        contact)
      (by
        change Matrix.det (current.coframe contact) ≠ 0
        exact nondegenerate)
      variation]
  exact
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_ECBalance_zero
      source current contact nondegenerate variation

/-- Simplicity and the live `delta B` reaction identify the full primitive
coframe derivative with the reduced zero-fiber readout on this same contact. -/
theorem
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_fullCoframeEuler_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (contact : BasePoint)
    (nondegenerate : Matrix.det (current.coframe contact) ≠ 0) :
    diracDualFormNativeCoframeEulerCovector source contact
        (toContinuumPointField
          (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
            source current contact)
          contact) =
      0 := by
  apply ContinuousLinearMap.ext
  intro variation
  change
    holonomicDiracDualFormNativeCoframeFirstVariationDensity source
        (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
          source current contact)
        (fun _ => variation)
        contact =
      0
  rw [←
    holonomicDiracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_full_of_equations
      source
      (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift
        source current contact)
      (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_simplicity
        source current contact)
      (sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_auxiliaryEquation
        source current contact)
      (fun _ => variation)
      contact]
  exact
    sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_reducedFirstVariation_zero
      source current contact nondegenerate variation

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCoframeECContactLocalActualLift
