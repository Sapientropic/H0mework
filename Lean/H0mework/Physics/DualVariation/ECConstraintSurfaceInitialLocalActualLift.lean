import H0mework.Physics.IdentityGerms.IdentityECConstraintActionSection
import H0mework.Physics.IdentityGerms.IdentityECConstraintObservationReplacement
import H0mework.Physics.IdentityGerms.IdentityECLoad
import H0mework.Physics.Coframe.CoframeGravityGaugeRegularity
import H0mework.Physics.Exterior.GravityMultiplierAuxiliaryIntegratedVariation
import H0mework.Physics.GravitySource.NormalizedAffineConnectionGerm

/-!
# Source/action-generated EC constraint-surface initial local actual

At the identity contact, the live non-gravity coframe stress is read directly
from the repaired gauge and matter action derivatives.  The residual-linear
root turns that stress into its canonical action curvature.  A faithful
observation splice then replaces only the four Cauchy-constraint rows of the
current curvature, retaining all twelve evolution rows and the complete EC
observation kernel.

The resulting curvature is realized by the normalized affine Lorentz
connection germ while preserving the current origin connection.  The
computed `II+` auxiliary and the live gravity reaction are recomputed on the
same output actual.  The constructor consumes only `(source, current)`; it
accepts no residual, target, response, branch, equation, or receipt.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeECConstraintSurfaceInitialLocalActualLift

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCartanTangentSimplicityResponse
open StageNineCoframeGravityGaugeRegularity
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeIdentityECConstraintActionSection
open StageNineDiracDualFormNativeIdentityECConstraintObservationReplacement
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECTemporalEvolutionSection
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineGlobalIntegratedAction
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineIIPlusRestriction
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Source/current-only action data -/

/-- Live non-gravity stress read directly from the two repaired action
sectors at the prepared contact.  It is not reconstructed by subtracting an
intrinsic term from a total load. -/
def diracDualFormNativeECLiveNonGravityCoframeStress
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    LorentzianCoframe →L[ℝ] ℝ :=
  diracDualFormNativeCoframeGaugeEulerCovector source
      (diracDualFormNativeECNormalContactField current) +
    diracDualFormNativeCoframeMatterEulerCovector source 0
      (diracDualFormNativeECNormalContactField current)

/-- Canonical residual-linear action curvature generated from the live
non-gravity stress. -/
def diracDualFormNativeECConstraintActionCurvature
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) : PhysicalBivector :=
  identityDiracDualECConstraintActionSection
    (diracDualFormNativeECLiveNonGravityCoframeStress source current)

/-- Current raw curvature after recomputing the holonomic `II+` carrier. -/
def diracDualFormNativeECConstraintSurfaceCurrentCurvature
    (current : StageNineHolonomicConfiguration) : PhysicalBivector :=
  holonomicGravityCurvature
    (diracDualFormNativeECNormalPreparedActual current) 0

/-- Replace only the four constraint observations by the action-generated
ones, preserving the current evolution observations and full EC kernel. -/
def diracDualFormNativeECConstraintSurfaceCurvatureTarget
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) : PhysicalBivector :=
  identityDiracDualECConstraintReplacementCurvatureTarget
    (diracDualFormNativeECConstraintSurfaceCurrentCurvature current)
    (diracDualFormNativeECConstraintActionCurvature source current)

/-! ## Primitive connection and synchronized actual -/

/-- Realize the action-generated constraint-surface curvature while keeping
the current origin connection value. -/
def diracDualFormNativeECConstraintSurfaceConnectedActual
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { diracDualFormNativeECNormalPreparedActual current with
    gravityConnection := normalizedAffineLorentzConnectionField
      ((diracDualFormNativeECNormalPreparedActual current).gravityConnection 0)
      (diracDualFormNativeECConstraintSurfaceCurvatureTarget source current) }

/-- Public source/current-only initial-data write.  The live reaction is
recomputed after installing the generated connection on the same actual. -/
def sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { diracDualFormNativeECConstraintSurfaceConnectedActual source current with
    gravitySimplicityMultiplier :=
      formNativeGravityReactionField
        (diracDualFormNativeECConstraintSurfaceConnectedActual source current) }

/-! ## Primitive-field fidelity and curvature realization -/

@[simp] theorem
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
      source current).coframe = current.coframe :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_auxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
      source current).gravityAuxiliary point =
      physicalIIPlusBivector (current.coframe point) :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_connection_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
      source current).gravityConnection 0 =
      current.gravityConnection 0 := by
  exact normalizedAffineLorentzConnectionField_zero _ _

theorem
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_curvature_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    holonomicGravityCurvature
        (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
          source current) 0 =
      diracDualFormNativeECConstraintSurfaceCurvatureTarget source current := by
  change
    holonomicGravityCurvature
        (normalizedAffineConfiguration
          ((diracDualFormNativeECNormalPreparedActual current
            ).gravityConnection 0)
          (diracDualFormNativeECConstraintSurfaceCurvatureTarget source current))
        0 =
      diracDualFormNativeECConstraintSurfaceCurvatureTarget source current
  exact holonomicGravityCurvature_normalizedAffineConfiguration_zero _ _

/-! ## Faithful EC observation replacement -/

theorem
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_evolutionObservation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    identityDiracDualECTemporalEvolutionObservation
        (holonomicGravityCurvature
          (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
            source current) 0) =
      identityDiracDualECTemporalEvolutionObservation
        (diracDualFormNativeECConstraintSurfaceCurrentCurvature current) := by
  rw [
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_curvature_zero]
  exact
    identityDiracDualECTemporalEvolutionObservation_constraintReplacementTarget
      _ _

theorem
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_constraintObservation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    identityDiracDualECConstraintObservation
        (holonomicGravityCurvature
          (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
            source current) 0) =
      identityDiracDualECConstraintObservation
        (diracDualFormNativeECConstraintActionCurvature source current) := by
  rw [
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_curvature_zero]
  exact identityDiracDualECConstraintObservation_constraintReplacementTarget _ _

theorem
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_kernelFaithful
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    identityDiracDualECCurvatureKernelPart
        (holonomicGravityCurvature
          (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
            source current) 0) =
      identityDiracDualECCurvatureKernelPart
        (diracDualFormNativeECConstraintSurfaceCurrentCurvature current) := by
  rw [
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_curvature_zero]
  exact
    identityDiracDualECCurvatureKernelPart_constraintReplacementTarget _ _

/-- The initial-data write preserves the six-dimensional electric-kernel
responsibility of the prepared current.  It does not claim equality of all
eighteen raw temporal curvature coordinates. -/
theorem
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_electricKernelFaithful
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    identityDiracDualECTemporalEvolutionKernelPart
        (identityECTemporalCurvatureCoordinatesOf
          (holonomicGravityCurvature
            (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
              source current) 0)) =
      identityDiracDualECTemporalEvolutionKernelPart
        (identityECTemporalCurvatureCoordinatesOf
          (diracDualFormNativeECConstraintSurfaceCurrentCurvature current)) := by
  rw [
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_curvature_zero]
  exact
    identityDiracDualECTemporalEvolutionKernelPart_constraintReplacementTarget
      _ _

/-! ## Geometry and reaction producer soundness -/

theorem
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_simplicity
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    FormNativeGravitySimplicityEquation
      (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
        source current) := by
  intro point
  rfl

theorem diracDualFormNativeECConstraintSurfaceConnectedActual_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth) :
    (diracDualFormNativeECConstraintSurfaceConnectedActual source current
      ).Smooth := by
  have preparedSmooth :
      (diracDualFormNativeECNormalPreparedActual current).Smooth :=
    restrictHolonomicConfigurationToIIPlus_smooth current smooth
  rcases preparedSmooth with
    ⟨coframeSmooth, _connectionSmooth, auxiliarySmooth, multiplierSmooth,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩
  exact
    ⟨coframeSmooth, normalizedAffineLorentzConnectionField_smooth _ _,
      auxiliarySmooth, multiplierSmooth, gaugeConnectionSmooth,
      gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩

theorem
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth) :
    (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
      source current).Smooth := by
  let connected :=
    diracDualFormNativeECConstraintSurfaceConnectedActual source current
  have connectedSmooth : connected.Smooth :=
    diracDualFormNativeECConstraintSurfaceConnectedActual_smooth
      source current smooth
  have dualAuxiliarySmooth : ContDiff ℝ ∞ fun point =>
      gravityInternalDualEquiv (connected.gravityAuxiliary point) :=
    holonomicGravityInternalDualAuxiliary_contDiff connected connectedSmooth
  have curvatureSmooth : ContDiff ℝ ∞ fun point =>
      holonomicContravariantGravityCurvature connected point := by
    apply contDiff_pi'
    intro internalPair
    apply contDiff_pi'
    intro spacetimePair
    exact contDiff_const.mul
      (holonomicGravityCurvature_component_contDiff connected connectedSmooth
        internalPair spacetimePair)
  have reactionSmooth : ContDiff ℝ ∞
      (formNativeGravityReactionField connected) :=
    dualAuxiliarySmooth.sub curvatureSmooth
  rcases connectedSmooth with
    ⟨coframeSmooth, connectionSmooth, auxiliarySmooth, _multiplierSmooth,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩
  exact
    ⟨coframeSmooth, connectionSmooth, auxiliarySmooth,
      fun internalPair spacetimePair =>
        contDiff_pi.mp (contDiff_pi.mp reactionSmooth internalPair)
          spacetimePair,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩

theorem
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_nondegenerate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate) :
    (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
      source current).Nondegenerate := by
  intro point
  exact nondegenerate point

theorem
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_lorentzAdmissible
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (admissible : GravityConnectionLorentzAdmissible current) :
    GravityConnectionLorentzAdmissible
      (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
        source current) := by
  intro point
  exact normalizedAffineLorentzConnectionField_lorentzSkew _ _
    (admissible 0) point

theorem
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_reactionSelfGenerated
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
      source current).gravitySimplicityMultiplier =
      formNativeGravityReactionField
        (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
          source current) := by
  rfl

theorem
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_auxiliaryEquation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    FormNativeGravityAuxiliaryEquation
      (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
        source current) := by
  exact
    (formNativeGravityAuxiliaryEquation_iff_multiplier_eq_reaction
      (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
        source current)).2
      (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_reactionSelfGenerated
        source current)

/-! ## Same-output non-gravity reads -/

/-- Forget precisely the gravity coordinates ignored by the gauge and matter
coframe action densities.  This is a proof projection, not a producer. -/
private def ecConstraintSurfaceNonGravityContactProjection
    (field : StageNineContinuumPointField) : StageNineContinuumPointField :=
  { field with
    gravityCurvature := 0
    gravityAuxiliary := 0
    gravitySimplicityMultiplier := 0 }

private theorem
    diracDualFormNativeCoframeGaugeDensity_ecConstraintSurfaceProjection
    (source : SmoothUnifiedSource)
    (field : StageNineContinuumPointField) :
    diracDualFormNativeCoframeGaugeDensity source
        (ecConstraintSurfaceNonGravityContactProjection field) =
      diracDualFormNativeCoframeGaugeDensity source field := by
  rfl

private theorem
    diracDualFormNativeCoframeMatterDensity_ecConstraintSurfaceProjection
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField) :
    diracDualFormNativeCoframeMatterDensity source point
        (ecConstraintSurfaceNonGravityContactProjection field) =
      diracDualFormNativeCoframeMatterDensity source point field := by
  rfl

private theorem
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_ecProjection_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    ecConstraintSurfaceNonGravityContactProjection
        (diracDualFormNativeECNormalContactField
          (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
            source current)) =
      ecConstraintSurfaceNonGravityContactProjection
        (diracDualFormNativeECNormalContactField current) := by
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
          (diracDualFormNativeECNormalPreparedActual
            (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
              source current)) 0 direction =
        holonomicMatterCovariantDerivative
          (diracDualFormNativeECNormalPreparedActual current) 0 direction
    unfold holonomicMatterCovariantDerivative
    rw [show
      (diracDualFormNativeECNormalPreparedActual
          (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
            source current)).gravityConnection 0 =
        current.gravityConnection 0 by
      change
        (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
          source current).gravityConnection 0 = current.gravityConnection 0
      exact
        sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_connection_zero
          source current]
    rfl
  · rfl

theorem
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_gaugeEuler_stable
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    diracDualFormNativeCoframeGaugeEulerCovector source
        (diracDualFormNativeECNormalContactField
          (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
            source current)) =
      diracDualFormNativeCoframeGaugeEulerCovector source
        (diracDualFormNativeECNormalContactField current) := by
  let finalField := diracDualFormNativeECNormalContactField
    (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
      source current)
  let currentField := diracDualFormNativeECNormalContactField current
  have projected :
      ecConstraintSurfaceNonGravityContactProjection finalField =
        ecConstraintSurfaceNonGravityContactProjection currentField :=
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_ecProjection_zero
      source current
  have densityEquality :
      diracDualFormNativeCoframeGaugeDensity source finalField =
        diracDualFormNativeCoframeGaugeDensity source currentField := by
    rw [←
      diracDualFormNativeCoframeGaugeDensity_ecConstraintSurfaceProjection
        source finalField,
      projected,
      diracDualFormNativeCoframeGaugeDensity_ecConstraintSurfaceProjection
        source currentField]
  unfold diracDualFormNativeCoframeGaugeEulerCovector
  rw [densityEquality]
  rfl

theorem
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_matterEuler_stable
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    diracDualFormNativeCoframeMatterEulerCovector source 0
        (diracDualFormNativeECNormalContactField
          (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
            source current)) =
      diracDualFormNativeCoframeMatterEulerCovector source 0
        (diracDualFormNativeECNormalContactField current) := by
  let finalField := diracDualFormNativeECNormalContactField
    (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
      source current)
  let currentField := diracDualFormNativeECNormalContactField current
  have projected :
      ecConstraintSurfaceNonGravityContactProjection finalField =
        ecConstraintSurfaceNonGravityContactProjection currentField :=
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_ecProjection_zero
      source current
  have densityEquality :
      diracDualFormNativeCoframeMatterDensity source 0 finalField =
        diracDualFormNativeCoframeMatterDensity source 0 currentField := by
    rw [←
      diracDualFormNativeCoframeMatterDensity_ecConstraintSurfaceProjection
        source 0 finalField,
      projected,
      diracDualFormNativeCoframeMatterDensity_ecConstraintSurfaceProjection
        source 0 currentField]
  unfold diracDualFormNativeCoframeMatterEulerCovector
  rw [densityEquality]
  rfl

theorem
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_liveStress_stable
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    diracDualFormNativeECLiveNonGravityCoframeStress source
        (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
          source current) =
      diracDualFormNativeECLiveNonGravityCoframeStress source current := by
  unfold diracDualFormNativeECLiveNonGravityCoframeStress
  rw [
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_gaugeEuler_stable,
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_matterEuler_stable]

theorem
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_load_stable
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    diracDualFormNativeIdentityECLoad source
        (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
          source current) =
      diracDualFormNativeIdentityECLoad source current := by
  unfold diracDualFormNativeIdentityECLoad
  rw [
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_gaugeEuler_stable,
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_matterEuler_stable]

/-! ## Same-output four-row constraint closure -/

/-- The same output actual lies on the complete four-dimensional EC Cauchy
constraint surface.  The identity is read back from the generated curvature
and the recomputed output load; it is not supplied to the constructor. -/
theorem
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_constraintBalance
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    identityDiracDualECConstraintObservation
          (holonomicGravityCurvature
            (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
              source current) 0) +
        identityECConstraintCoordinatesOfCovector
          (diracDualFormNativeIdentityECLoad source
            (sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
              source current)) =
      0 := by
  rw [
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_constraintObservation,
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_load_stable]
  funext row
  change
    identityDiracDualECCurvatureObservation
          (diracDualFormNativeECConstraintActionCurvature source current)
          (coframeCoordinateDirection row 0) +
        diracDualFormNativeIdentityECLoad source current
          (coframeCoordinateDirection row 0) =
      0
  have actionBalance :=
    identityDiracDualECConstraintActionSection_balance_apply
      (diracDualFormNativeECLiveNonGravityCoframeStress source current)
      (coframeCoordinateDirection row 0)
  simp [diracDualFormNativeECConstraintActionCurvature,
    diracDualFormNativeIdentityECLoad,
    diracDualFormNativeECLiveNonGravityCoframeStress,
    identityDiracDualECIntrinsicIIPlusObservation] at actionBalance ⊢
  linarith

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeECConstraintSurfaceInitialLocalActualLift
