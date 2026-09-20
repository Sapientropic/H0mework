import H0mework.Physics.DualVariation.FourLegCriticalLocusCorrespondence
import H0mework.Physics.IdentityGerms.CoframeHessianLocalActualLift

/-!
# Same-actual load stability after the holonomic EC Hessian write

The identity-contact Hessian write changes the primitive coframe away from
the origin, its second jet, the Lorentz-connection first jet, and hence the
actual origin curvature.  It retains the origin coframe and connection value
as well as every gauge, scalar, matter, and conjugate-matter field.

This module proves from those literal dependencies that the curvature-
independent coframe load recomputed on the output actual is unchanged.  The
ten-plus-six settlement can therefore be stated using only fields read from
the same output actual.  No stability certificate is accepted by the
constructor, and no reaction or torsion receipt from the input actual is
transported across the write.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLoadStability

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeFourLegCriticalLocusCorrespondence
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianSection
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineLinearPlebanskiCoframeActionPrincipal

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- Forget precisely the gravity coordinates not consumed by the gauge and
matter coframe densities.  This is a dependency readout, not a producer. -/
def identityECNonGravityContactProjection
    (field : StageNineContinuumPointField) : StageNineContinuumPointField :=
  { field with
    gravityCurvature := 0
    gravityAuxiliary := 0
    gravitySimplicityMultiplier := 0 }

@[simp] theorem
    diracDualFormNativeCoframeGaugeDensity_identityECNonGravityProjection
    (source : SmoothUnifiedSource)
    (field : StageNineContinuumPointField) :
    diracDualFormNativeCoframeGaugeDensity source
        (identityECNonGravityContactProjection field) =
      diracDualFormNativeCoframeGaugeDensity source field := by
  rfl

@[simp] theorem
    diracDualFormNativeCoframeMatterDensity_identityECNonGravityProjection
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField) :
    diracDualFormNativeCoframeMatterDensity source point
        (identityECNonGravityContactProjection field) =
      diracDualFormNativeCoframeMatterDensity source point field := by
  rfl

/-- The identity-contact load depends only on the non-gravity contact
projection.  This is the reusable dependency seam behind load preservation
across gravity writes; it does not authorize or construct such a write. -/
theorem diracDualFormNativeIdentityECLoad_eq_of_nonGravityProjection_eq
    (source : SmoothUnifiedSource)
    (first second : StageNineHolonomicConfiguration)
    (projected :
      identityECNonGravityContactProjection
          (diracDualFormNativeECNormalContactField first) =
        identityECNonGravityContactProjection
          (diracDualFormNativeECNormalContactField second)) :
    diracDualFormNativeIdentityECLoad source first =
      diracDualFormNativeIdentityECLoad source second := by
  let firstField := diracDualFormNativeECNormalContactField first
  let secondField := diracDualFormNativeECNormalContactField second
  have coframeEquality : firstField.coframe = secondField.coframe := by
    simpa [firstField, secondField, identityECNonGravityContactProjection]
      using congrArg
        (fun field : StageNineContinuumPointField => field.coframe) projected
  have gaugeDensityEquality :
      diracDualFormNativeCoframeGaugeDensity source firstField =
        diracDualFormNativeCoframeGaugeDensity source secondField := by
    rw [←
      diracDualFormNativeCoframeGaugeDensity_identityECNonGravityProjection
        source firstField,
      projected,
      diracDualFormNativeCoframeGaugeDensity_identityECNonGravityProjection
        source secondField]
  have matterDensityEquality :
      diracDualFormNativeCoframeMatterDensity source 0 firstField =
        diracDualFormNativeCoframeMatterDensity source 0 secondField := by
    rw [←
      diracDualFormNativeCoframeMatterDensity_identityECNonGravityProjection
        source 0 firstField,
      projected,
      diracDualFormNativeCoframeMatterDensity_identityECNonGravityProjection
        source 0 secondField]
  have gaugeEulerEquality :
      diracDualFormNativeCoframeGaugeEulerCovector source firstField =
        diracDualFormNativeCoframeGaugeEulerCovector source secondField := by
    unfold diracDualFormNativeCoframeGaugeEulerCovector
    change
      fderiv ℝ (diracDualFormNativeCoframeGaugeDensity source firstField)
          firstField.coframe =
        fderiv ℝ (diracDualFormNativeCoframeGaugeDensity source secondField)
          secondField.coframe
    rw [gaugeDensityEquality, coframeEquality]
  have matterEulerEquality :
      diracDualFormNativeCoframeMatterEulerCovector source 0 firstField =
        diracDualFormNativeCoframeMatterEulerCovector source 0 secondField := by
    unfold diracDualFormNativeCoframeMatterEulerCovector
    change
      fderiv ℝ
          (diracDualFormNativeCoframeMatterDensity source 0 firstField)
          firstField.coframe =
        fderiv ℝ
          (diracDualFormNativeCoframeMatterDensity source 0 secondField)
          secondField.coframe
    rw [matterDensityEquality, coframeEquality]
  unfold diracDualFormNativeIdentityECLoad
  rw [gaugeEulerEquality, matterEulerEquality]

theorem
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift_prepared
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    diracDualFormNativeECNormalPreparedActual
        (sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
          source current) =
      sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
        source current := by
  apply
    (restrictHolonomicConfigurationToIIPlus_eq_self_iff_diracDualFormNativeSimplicity
      _).2
  exact
    identityECHolonomicCoframeHessianIncrementLocalActualLift_simplicity
      current
      (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
        source current)

theorem
    identityECHolonomicCoframeHessianLocalActualLift_nonGravityProjection_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (currentSimplicity : FormNativeGravitySimplicityEquation current) :
    identityECNonGravityContactProjection
        (diracDualFormNativeECNormalContactField
          (sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
            source current)) =
      identityECNonGravityContactProjection
        (diracDualFormNativeECNormalContactField current) := by
  have currentPrepared :
      diracDualFormNativeECNormalPreparedActual current = current :=
    (restrictHolonomicConfigurationToIIPlus_eq_self_iff_diracDualFormNativeSimplicity
      current).2 currentSimplicity
  unfold diracDualFormNativeECNormalContactField
  rw [
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift_prepared,
    currentPrepared]
  apply StageNineContinuumPointField.ext
  · exact
      identityECHolonomicCoframeHessianIncrementLocalActualLift_coframe_origin
        current
        (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
          source current)
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
          (sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
            source current) 0 direction =
        holonomicMatterCovariantDerivative current 0 direction
    unfold holonomicMatterCovariantDerivative
    have connectionOrigin :
        (sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
            source current).gravityConnection 0 =
          current.gravityConnection 0 := by
      unfold
        sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
      exact
        identityECHolonomicCoframeHessianIncrementLocalActualLift_connection_origin
          current
          (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
            source current)
    rw [connectionOrigin]
    rfl
  · rfl

theorem
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift_gaugeEuler_stable
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (currentSimplicity : FormNativeGravitySimplicityEquation current) :
    diracDualFormNativeCoframeGaugeEulerCovector source
        (diracDualFormNativeECNormalContactField
          (sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
            source current)) =
      diracDualFormNativeCoframeGaugeEulerCovector source
        (diracDualFormNativeECNormalContactField current) := by
  let nextField := diracDualFormNativeECNormalContactField
    (sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
      source current)
  let currentField := diracDualFormNativeECNormalContactField current
  have projected :
      identityECNonGravityContactProjection nextField =
        identityECNonGravityContactProjection currentField :=
    identityECHolonomicCoframeHessianLocalActualLift_nonGravityProjection_eq
      source current currentSimplicity
  have densityEquality :
      diracDualFormNativeCoframeGaugeDensity source nextField =
        diracDualFormNativeCoframeGaugeDensity source currentField := by
    rw [←
      diracDualFormNativeCoframeGaugeDensity_identityECNonGravityProjection
        source nextField,
      projected,
      diracDualFormNativeCoframeGaugeDensity_identityECNonGravityProjection
        source currentField]
  have coframeEquality : nextField.coframe = currentField.coframe :=
    by
      simpa [identityECNonGravityContactProjection] using
        congrArg (fun field : StageNineContinuumPointField => field.coframe)
          projected
  unfold diracDualFormNativeCoframeGaugeEulerCovector
  change
    fderiv ℝ (diracDualFormNativeCoframeGaugeDensity source nextField)
        nextField.coframe =
      fderiv ℝ (diracDualFormNativeCoframeGaugeDensity source currentField)
        currentField.coframe
  rw [densityEquality, coframeEquality]

theorem
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift_matterEuler_stable
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (currentSimplicity : FormNativeGravitySimplicityEquation current) :
    diracDualFormNativeCoframeMatterEulerCovector source 0
        (diracDualFormNativeECNormalContactField
          (sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
            source current)) =
      diracDualFormNativeCoframeMatterEulerCovector source 0
        (diracDualFormNativeECNormalContactField current) := by
  let nextField := diracDualFormNativeECNormalContactField
    (sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
      source current)
  let currentField := diracDualFormNativeECNormalContactField current
  have projected :
      identityECNonGravityContactProjection nextField =
        identityECNonGravityContactProjection currentField :=
    identityECHolonomicCoframeHessianLocalActualLift_nonGravityProjection_eq
      source current currentSimplicity
  have densityEquality :
      diracDualFormNativeCoframeMatterDensity source 0 nextField =
        diracDualFormNativeCoframeMatterDensity source 0 currentField := by
    rw [←
      diracDualFormNativeCoframeMatterDensity_identityECNonGravityProjection
        source 0 nextField,
      projected,
      diracDualFormNativeCoframeMatterDensity_identityECNonGravityProjection
        source 0 currentField]
  have coframeEquality : nextField.coframe = currentField.coframe :=
    by
      simpa [identityECNonGravityContactProjection] using
        congrArg (fun field : StageNineContinuumPointField => field.coframe)
          projected
  unfold diracDualFormNativeCoframeMatterEulerCovector
  change
    fderiv ℝ (diracDualFormNativeCoframeMatterDensity source 0 nextField)
        nextField.coframe =
      fderiv ℝ
        (diracDualFormNativeCoframeMatterDensity source 0 currentField)
        currentField.coframe
  rw [densityEquality, coframeEquality]

/-- Recomputing the curvature-independent load on the generated output
returns the input load because every field it consumes agrees at the contact.
-/
theorem
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift_load_stable
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (currentSimplicity : FormNativeGravitySimplicityEquation current) :
    diracDualFormNativeIdentityECLoad source
        (sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
          source current) =
      diracDualFormNativeIdentityECLoad source current := by
  unfold diracDualFormNativeIdentityECLoad
  rw [
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift_gaugeEuler_stable
      source current currentSimplicity,
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift_matterEuler_stable
      source current currentSimplicity]

/-- Same-output form of the ten-plus-six settlement.  Both curvature and
the curvature-independent load are now reread from the generated output
actual. -/
theorem
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift_sameActual_settlement
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (currentSmooth : current.Smooth)
    (currentSimplicity : FormNativeGravitySimplicityEquation current) :
    coframeCovectorCoordinates
        (identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature
              (sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
                source current) 0) +
          diracDualFormNativeIdentityECLoad source
            (sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
              source current)) =
      identityECEtaAntisymmetricPart
        (sourceActionGeneratedIdentityECCoframeLowerOrderCoordinates
          source current) := by
  rw [
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift_load_stable
      source current currentSimplicity]
  exact
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift_currentLoad_settlement
      source current currentSmooth

end


end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLoadStability
