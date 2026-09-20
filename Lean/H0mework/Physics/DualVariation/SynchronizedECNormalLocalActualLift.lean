import H0mework.Physics.CartanAction.CartanReactionLocalActualLift
import H0mework.Physics.DualVariation.FourLegCriticalLocusCorrespondence
import H0mework.Physics.IdentityGerms.IdentityECCurvatureNormalSection
import H0mework.Physics.IdentityGerms.IdentityECLoad
import H0mework.Physics.CoframeVariation.IIPlusCoframeECBalance
import H0mework.Physics.CoframeVariation.IIPlusCoframePointwiseEquation
import H0mework.Physics.GravitySource.NormalizedAffineConnectionGerm
import H0mework.Physics.Dirac.GeneratedMatterSpinActionUpdate

/-!
# Synchronized identity-contact EC normal local actual

After the Cartan connection and live gravity reaction writes, the repaired
coframe equation still reads a nonzero curvature-dependent coefficient.  At
the identity contact this module uses the action-normalized EC section to
generate precisely the observed curvature component required by the same
repaired action.  The current curvature's complete unobserved kernel part is
transported unchanged.

The generated curvature is realized by the normalized affine Lorentz
connection germ while preserving the current connection value at the
origin.  The `II+` auxiliary and the unique live reaction are then recomputed
in one exposed actual.  The constructor consumes only a source and a current;
it accepts no residual, target curvature, response, coefficient, inverse,
branch, equation, or stationarity receipt.

The jurisdiction is deliberately local: the affine field realizes the
generated curvature and the Cartan value at the origin.  No neighborhood
Cartan equation, global integral curve, or global EC solution is claimed.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCartanAffineConnectionActualization
open StageNineCartanTorsionThreeFormCoordinates
open StageNineCartanTangentSimplicityResponse
open StageNineCoframeFirstJet
open StageNineCoframeGravityGaugeRegularity
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionLocalActualLift
open StageNineDiracDualFormNativeCoframeIntegratedVariation
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeFourLegCriticalLocusCorrespondence
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIIPlusCoframeECBalance
open StageNineDiracDualFormNativeIIPlusCoframePointwiseEquation
open StageNineDiracDualFormNativeIIPlusReductionLocalVariation
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeLorentzTorsionSpinEquation
open StageNineFormNativeMatterSpinThreeForm
open StageNineGlobalIntegratedAction
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineIIPlusRestriction
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceGeneratedMatterSpinActionUpdate
open StageNineTopologicalFourFormPairing
open StageNineTopologicalLorentzThreeFormDuality
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Source/current-only synchronized write -/

/-- The unique branch-free raw curvature target.  It preserves the current
action-normal kernel and installs the observation opposite to the remaining
live load. -/
def diracDualFormNativeECNormalCurvatureTarget
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) : PhysicalBivector :=
  identityDiracDualECCurvatureTarget
    (holonomicGravityCurvature
      (diracDualFormNativeECNormalPreparedActual current) 0)
    (-diracDualFormNativeIdentityECLoad source current)

/-- Realize the generated curvature by a primitive connection germ while
preserving the current origin connection value. -/
def diracDualFormNativeECNormalConnectedActual
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { diracDualFormNativeECNormalPreparedActual current with
    gravityConnection := normalizedAffineLorentzConnectionField
      ((diracDualFormNativeECNormalPreparedActual current).gravityConnection 0)
      (diracDualFormNativeECNormalCurvatureTarget source current) }

/-- Public synchronized write: `B := II+(e)`, the generated connection germ,
and the live action reaction are installed together. -/
def sourceActionGeneratedDiracDualECNormalLocalActualLift
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { diracDualFormNativeECNormalConnectedActual source current with
    gravitySimplicityMultiplier :=
      formNativeGravityReactionField
        (diracDualFormNativeECNormalConnectedActual source current) }

/-! ## Primitive-field fidelity and realized curvature -/

@[simp] theorem sourceActionGeneratedDiracDualECNormalLocalActualLift_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualECNormalLocalActualLift source current).coframe =
      current.coframe :=
  rfl

@[simp] theorem sourceActionGeneratedDiracDualECNormalLocalActualLift_auxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualECNormalLocalActualLift source current
      ).gravityAuxiliary point =
      physicalIIPlusBivector (current.coframe point) :=
  rfl

@[simp] theorem sourceActionGeneratedDiracDualECNormalLocalActualLift_connection_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualECNormalLocalActualLift source current
      ).gravityConnection 0 =
      current.gravityConnection 0 := by
  exact normalizedAffineLorentzConnectionField_zero _ _

theorem sourceActionGeneratedDiracDualECNormalLocalActualLift_curvature_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    holonomicGravityCurvature
        (sourceActionGeneratedDiracDualECNormalLocalActualLift source current) 0 =
      diracDualFormNativeECNormalCurvatureTarget source current := by
  change
    holonomicGravityCurvature
        (normalizedAffineConfiguration
          ((diracDualFormNativeECNormalPreparedActual current)
            |>.gravityConnection 0)
          (diracDualFormNativeECNormalCurvatureTarget source current)) 0 =
      diracDualFormNativeECNormalCurvatureTarget source current
  exact holonomicGravityCurvature_normalizedAffineConfiguration_zero _ _

/-- The same actual realizes exactly the action-generated EC observation. -/
theorem
    sourceActionGeneratedDiracDualECNormalLocalActualLift_curvatureObservation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    identityDiracDualECCurvatureObservation
        (holonomicGravityCurvature
          (sourceActionGeneratedDiracDualECNormalLocalActualLift source current)
          0) =
      -diracDualFormNativeIdentityECLoad source current := by
  rw [sourceActionGeneratedDiracDualECNormalLocalActualLift_curvature_zero]
  exact identityDiracDualECCurvatureObservation_target _ _

/-- The write cannot silently erase the current curvature's unobserved
responsibility. -/
theorem sourceActionGeneratedDiracDualECNormalLocalActualLift_kernelFaithful
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    identityDiracDualECCurvatureKernelPart
        (holonomicGravityCurvature
          (sourceActionGeneratedDiracDualECNormalLocalActualLift source current)
          0) =
      identityDiracDualECCurvatureKernelPart
        (holonomicGravityCurvature
          (diracDualFormNativeECNormalPreparedActual current) 0) := by
  rw [sourceActionGeneratedDiracDualECNormalLocalActualLift_curvature_zero]
  exact identityDiracDualECCurvatureKernelPart_target _ _

/-- No second curvature branch can realize the same requested observation
while preserving the same current kernel responsibility. -/
theorem sourceActionGeneratedDiracDualECNormalLocalActualLift_curvature_unique
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (candidate : PhysicalBivector)
    (hObservation :
      identityDiracDualECCurvatureObservation candidate =
        -diracDualFormNativeIdentityECLoad source current)
    (hKernel :
      identityDiracDualECCurvatureKernelPart candidate =
        identityDiracDualECCurvatureKernelPart
          (holonomicGravityCurvature
            (diracDualFormNativeECNormalPreparedActual current) 0)) :
    candidate =
      holonomicGravityCurvature
        (sourceActionGeneratedDiracDualECNormalLocalActualLift source current)
        0 := by
  rw [sourceActionGeneratedDiracDualECNormalLocalActualLift_curvature_zero]
  exact identityDiracDualECCurvatureTarget_unique _ _ _
    hObservation hKernel

/-! ## Geometry, regularity, and producer soundness -/

theorem sourceActionGeneratedDiracDualECNormalLocalActualLift_simplicity
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    FormNativeGravitySimplicityEquation
      (sourceActionGeneratedDiracDualECNormalLocalActualLift source current) := by
  intro point
  rfl

theorem sourceActionGeneratedDiracDualECNormalConnectedActual_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth) :
    (diracDualFormNativeECNormalConnectedActual source current).Smooth := by
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

theorem sourceActionGeneratedDiracDualECNormalLocalActualLift_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth) :
    (sourceActionGeneratedDiracDualECNormalLocalActualLift source current).Smooth := by
  let connected := diracDualFormNativeECNormalConnectedActual source current
  have connectedSmooth : connected.Smooth :=
    sourceActionGeneratedDiracDualECNormalConnectedActual_smooth
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

theorem sourceActionGeneratedDiracDualECNormalLocalActualLift_nondegenerate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate) :
    (sourceActionGeneratedDiracDualECNormalLocalActualLift source current
      ).Nondegenerate := by
  intro point
  exact nondegenerate point

theorem sourceActionGeneratedDiracDualECNormalLocalActualLift_lorentzAdmissible
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (admissible : GravityConnectionLorentzAdmissible current) :
    GravityConnectionLorentzAdmissible
      (sourceActionGeneratedDiracDualECNormalLocalActualLift source current) := by
  intro point
  exact normalizedAffineLorentzConnectionField_lorentzSkew _ _
    (admissible 0) point

/-- Recomputing the live reaction after installation returns exactly the
installed field.  This is producer soundness for the `delta B` write. -/
theorem
    sourceActionGeneratedDiracDualECNormalLocalActualLift_reactionSelfGenerated
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualECNormalLocalActualLift source current
        ).gravitySimplicityMultiplier =
      formNativeGravityReactionField
        (sourceActionGeneratedDiracDualECNormalLocalActualLift source current) := by
  rfl

theorem
    sourceActionGeneratedDiracDualECNormalLocalActualLift_auxiliaryEquation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    FormNativeGravityAuxiliaryEquation
      (sourceActionGeneratedDiracDualECNormalLocalActualLift source current) := by
  exact
    (formNativeGravityAuxiliaryEquation_iff_multiplier_eq_reaction
      (sourceActionGeneratedDiracDualECNormalLocalActualLift source current)).2
      (sourceActionGeneratedDiracDualECNormalLocalActualLift_reactionSelfGenerated
        source current)

/-! ## Preserved Cartan contact -/

theorem
    sourceActionGeneratedDiracDualECNormalLocalActualLift_connectionSelfGenerated_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (selfGenerated :
      current.gravityConnection 0 =
        diracDualFormNativeActionCartanConnectionAt source current 0) :
    (sourceActionGeneratedDiracDualECNormalLocalActualLift source current
        ).gravityConnection 0 =
      diracDualFormNativeActionCartanConnectionAt source
        (sourceActionGeneratedDiracDualECNormalLocalActualLift source current)
        0 := by
  let final :=
    sourceActionGeneratedDiracDualECNormalLocalActualLift source current
  calc
    final.gravityConnection 0 = current.gravityConnection 0 :=
      sourceActionGeneratedDiracDualECNormalLocalActualLift_connection_zero
        source current
    _ = diracDualFormNativeActionCartanConnectionAt source current 0 :=
      selfGenerated
    _ = diracDualFormNativeActionCartanConnectionAt source final 0 := by
      unfold diracDualFormNativeActionCartanConnectionAt
        diracDualFormNativeActionCartanContorsionAt
        diracDualFormNativeActionCartanTorsionAt
      rw [diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
        source current final 0 rfl rfl rfl]
      rfl

theorem
    sourceActionGeneratedDiracDualECNormalLocalActualLift_typedTorsionSpin_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (selfGenerated :
      current.gravityConnection 0 =
        diracDualFormNativeActionCartanConnectionAt source current 0) :
    cartanTorsionThreeForm
        ((sourceActionGeneratedDiracDualECNormalLocalActualLift source current
          ).coframe 0)
        (actualPointwiseCartanTorsionTwoForm
          (holonomicCoframeFirstJetAt
            (sourceActionGeneratedDiracDualECNormalLocalActualLift source current
              ).coframe 0)
          ((sourceActionGeneratedDiracDualECNormalLocalActualLift source current
            ).gravityConnection 0)) =
      diracDualFormNativeActionSpinResponseAt source
        (sourceActionGeneratedDiracDualECNormalLocalActualLift source current)
        0 := by
  rw [sourceActionGeneratedDiracDualECNormalLocalActualLift_connectionSelfGenerated_zero
    source current selfGenerated]
  exact diracDualFormNativeActionCartanConnectionAt_generates_spinResponse
    source (sourceActionGeneratedDiracDualECNormalLocalActualLift source current)
      0 nondegenerate

/-- Only the shared origin contact is asserted; the affine germ is not
claimed to be the Cartan producer away from the origin. -/
theorem
    sourceActionGeneratedDiracDualECNormalLocalActualLift_torsionSpin_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (selfGenerated :
      current.gravityConnection 0 =
        diracDualFormNativeActionCartanConnectionAt source current 0) :
    internalBivectorDualThreeForm
        (torsionCoframeWedgeThreeForm
          ((sourceActionGeneratedDiracDualECNormalLocalActualLift source current
            ).coframe 0)
          (pointwiseCartanTorsion
            (holonomicCoframeFirstJetAt
              (sourceActionGeneratedDiracDualECNormalLocalActualLift
                source current).coframe 0)
            ((sourceActionGeneratedDiracDualECNormalLocalActualLift
              source current).gravityConnection 0))) =
      formNativePhysicalSpinCurrentThreeForm source 0 0
        (toContinuumPointField
          (restrictHolonomicConfigurationToIIPlus
            (sourceActionGeneratedDiracDualECNormalLocalActualLift
              source current)) 0) := by
  rw [← cartanTorsionThreeForm_actualPointwiseCartanTorsionTwoForm]
  exact
    sourceActionGeneratedDiracDualECNormalLocalActualLift_typedTorsionSpin_zero
      source current nondegenerate selfGenerated

/-! ## Same-contact non-gravity seam -/

/-- Forget exactly the three gravity slots not read by the gauge or matter
coframe densities.  This is a local proof device, not a quotient producer. -/
private def ecNonGravityContactProjection
    (field : StageNineContinuumPointField) : StageNineContinuumPointField :=
  { field with
    gravityCurvature := 0
    gravityAuxiliary := 0
    gravitySimplicityMultiplier := 0 }

private theorem diracDualFormNativeCoframeGaugeDensity_ecProjection
    (source : SmoothUnifiedSource)
    (field : StageNineContinuumPointField) :
    diracDualFormNativeCoframeGaugeDensity source
        (ecNonGravityContactProjection field) =
      diracDualFormNativeCoframeGaugeDensity source field := by
  rfl

private theorem diracDualFormNativeCoframeMatterDensity_ecProjection
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField) :
    diracDualFormNativeCoframeMatterDensity source point
        (ecNonGravityContactProjection field) =
      diracDualFormNativeCoframeMatterDensity source point field := by
  rfl

/-- At the origin the final actual and the load-reading contact have the same
complete non-gravity point field.  The only non-definitional component is the
matter covariant derivative, whose connection value is preserved by the
normalized affine germ. -/
private theorem sourceActionGeneratedDiracDualECNormalLocalActualLift_ecProjection_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    ecNonGravityContactProjection
        (restrictContinuumPointFieldToIIPlus
          (toContinuumPointField
            (sourceActionGeneratedDiracDualECNormalLocalActualLift
              source current) 0)) =
      ecNonGravityContactProjection
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
          (sourceActionGeneratedDiracDualECNormalLocalActualLift
            source current) 0 direction =
        holonomicMatterCovariantDerivative
          (diracDualFormNativeECNormalPreparedActual current) 0 direction
    unfold holonomicMatterCovariantDerivative
    rw [sourceActionGeneratedDiracDualECNormalLocalActualLift_connection_zero]
    rfl
  · rfl

theorem sourceActionGeneratedDiracDualECNormalLocalActualLift_gaugeEuler_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    diracDualFormNativeCoframeGaugeEulerCovector source
        (restrictContinuumPointFieldToIIPlus
          (toContinuumPointField
            (sourceActionGeneratedDiracDualECNormalLocalActualLift
              source current) 0)) =
      diracDualFormNativeCoframeGaugeEulerCovector source
        (diracDualFormNativeECNormalContactField current) := by
  let finalField :=
    restrictContinuumPointFieldToIIPlus
      (toContinuumPointField
        (sourceActionGeneratedDiracDualECNormalLocalActualLift source current) 0)
  let contactField := diracDualFormNativeECNormalContactField current
  have projected :
      ecNonGravityContactProjection finalField =
        ecNonGravityContactProjection contactField :=
    sourceActionGeneratedDiracDualECNormalLocalActualLift_ecProjection_zero
      source current
  have densityEquality :
      diracDualFormNativeCoframeGaugeDensity source finalField =
        diracDualFormNativeCoframeGaugeDensity source contactField := by
    rw [← diracDualFormNativeCoframeGaugeDensity_ecProjection source finalField,
      projected,
      diracDualFormNativeCoframeGaugeDensity_ecProjection source contactField]
  unfold diracDualFormNativeCoframeGaugeEulerCovector
  rw [densityEquality]
  rfl

theorem sourceActionGeneratedDiracDualECNormalLocalActualLift_matterEuler_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    diracDualFormNativeCoframeMatterEulerCovector source 0
        (restrictContinuumPointFieldToIIPlus
          (toContinuumPointField
            (sourceActionGeneratedDiracDualECNormalLocalActualLift
              source current) 0)) =
      diracDualFormNativeCoframeMatterEulerCovector source 0
        (diracDualFormNativeECNormalContactField current) := by
  let finalField :=
    restrictContinuumPointFieldToIIPlus
      (toContinuumPointField
        (sourceActionGeneratedDiracDualECNormalLocalActualLift source current) 0)
  let contactField := diracDualFormNativeECNormalContactField current
  have projected :
      ecNonGravityContactProjection finalField =
        ecNonGravityContactProjection contactField :=
    sourceActionGeneratedDiracDualECNormalLocalActualLift_ecProjection_zero
      source current
  have densityEquality :
      diracDualFormNativeCoframeMatterDensity source 0 finalField =
        diracDualFormNativeCoframeMatterDensity source 0 contactField := by
    rw [← diracDualFormNativeCoframeMatterDensity_ecProjection
        source 0 finalField,
      projected,
      diracDualFormNativeCoframeMatterDensity_ecProjection
        source 0 contactField]
  unfold diracDualFormNativeCoframeMatterEulerCovector
  rw [densityEquality]
  rfl

/-! ## Origin EC closure -/

theorem identityDiracDualECCurvatureObservation_intrinsic_apply
    (variation : LorentzianCoframe) :
    identityDiracDualECCurvatureObservation
        (gravityInternalPairVarianceNormalization
          (coframeWedge (1 : LorentzianCoframe))) variation =
      gravityTopologicalWedgeCoefficient
        (physicalIIPlusCoframeTangent (1 : LorentzianCoframe) variation)
        (coframeWedge (1 : LorentzianCoframe)) := by
  change
    gravityTopologicalWedgeCoefficient
        (physicalIIPlusCoframeTangent (1 : LorentzianCoframe) variation)
        (gravityInternalPairVarianceNormalization
          (gravityInternalPairVarianceNormalization
            (coframeWedge (1 : LorentzianCoframe)))) = _
  rw [gravityInternalPairVarianceNormalization_involutive]

/-- The one final actual satisfies the complete repaired EC coefficient at
the shared identity contact.  This is validation of the action-generated
curvature write, not a separately supplied constraint certificate. -/
theorem sourceActionGeneratedDiracDualECNormalLocalActualLift_ECBalance_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (coframeOne : current.coframe 0 = 1)
    (variation : LorentzianCoframe) :
    gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent
            ((sourceActionGeneratedDiracDualECNormalLocalActualLift
              source current).coframe 0) variation)
          (gravityInternalPairVarianceNormalization
              (toContinuumPointField
                (sourceActionGeneratedDiracDualECNormalLocalActualLift
                  source current) 0).gravityCurvature +
            coframeWedge
              ((sourceActionGeneratedDiracDualECNormalLocalActualLift
                source current).coframe 0)) +
        diracDualFormNativeCoframeGaugeEulerCovector source
          (restrictContinuumPointFieldToIIPlus
            (toContinuumPointField
              (sourceActionGeneratedDiracDualECNormalLocalActualLift
                source current) 0)) variation +
        diracDualFormNativeCoframeMatterEulerCovector source 0
          (restrictContinuumPointFieldToIIPlus
            (toContinuumPointField
              (sourceActionGeneratedDiracDualECNormalLocalActualLift
                source current) 0)) variation = 0 := by
  rw [sourceActionGeneratedDiracDualECNormalLocalActualLift_coframe,
    coframeOne]
  rw [gravityTopologicalWedgeCoefficient_add_right]
  have curvatureObservation := congrArg
    (fun covector : LorentzianCoframe →L[ℝ] ℝ => covector variation)
    (sourceActionGeneratedDiracDualECNormalLocalActualLift_curvatureObservation
      source current)
  have gaugeEquality := DFunLike.congr_fun
    (sourceActionGeneratedDiracDualECNormalLocalActualLift_gaugeEuler_zero
      source current) variation
  have matterEquality := DFunLike.congr_fun
    (sourceActionGeneratedDiracDualECNormalLocalActualLift_matterEuler_zero
      source current) variation
  rw [show
      gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent (1 : LorentzianCoframe) variation)
          (gravityInternalPairVarianceNormalization
            (toContinuumPointField
              (sourceActionGeneratedDiracDualECNormalLocalActualLift
                source current) 0).gravityCurvature) =
        identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature
            (sourceActionGeneratedDiracDualECNormalLocalActualLift
              source current) 0) variation by
      rfl]
  rw [curvatureObservation, gaugeEquality, matterEquality]
  rw [← identityDiracDualECCurvatureObservation_intrinsic_apply variation]
  unfold diracDualFormNativeIdentityECLoad
  simp only [add_apply, neg_apply]
  abel

theorem
    sourceActionGeneratedDiracDualECNormalLocalActualLift_reducedFirstVariation_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (coframeOne : current.coframe 0 = 1)
    (variation : LorentzianCoframe) :
    diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity source 0
        (toContinuumPointField
          (sourceActionGeneratedDiracDualECNormalLocalActualLift
            source current) 0) variation = 0 := by
  rw [diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_EC_balance
    source 0
      (toContinuumPointField
        (sourceActionGeneratedDiracDualECNormalLocalActualLift source current)
        0)
      (by
        change Matrix.det (current.coframe 0) ≠ 0
        rw [coframeOne]
        norm_num)
      variation]
  exact
    sourceActionGeneratedDiracDualECNormalLocalActualLift_ECBalance_zero
      source current coframeOne variation

theorem
    sourceActionGeneratedDiracDualECNormalLocalActualLift_reducedEuler_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (coframeOne : current.coframe 0 = 1) :
    diracDualFormNativeIIPlusReducedCoframeEulerCovector source
        (sourceActionGeneratedDiracDualECNormalLocalActualLift source current)
        0 = 0 := by
  apply ContinuousLinearMap.ext
  intro variation
  rw [diracDualFormNativeIIPlusReducedCoframeEulerCovector_apply
    source
      (sourceActionGeneratedDiracDualECNormalLocalActualLift source current)
      (sourceActionGeneratedDiracDualECNormalLocalActualLift_smooth
        source current smooth)
      (sourceActionGeneratedDiracDualECNormalLocalActualLift_nondegenerate
        source current nondegenerate)
      0 variation]
  exact
    sourceActionGeneratedDiracDualECNormalLocalActualLift_reducedFirstVariation_zero
      source current coframeOne variation

/-- Simplicity and the live `delta B` equation identify the full primitive
coframe derivative with the reduced EC derivative on this same actual. -/
theorem
    sourceActionGeneratedDiracDualECNormalLocalActualLift_fullCoframeEuler_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (coframeOne : current.coframe 0 = 1) :
    diracDualFormNativeCoframeEulerCovector source 0
        (toContinuumPointField
          (sourceActionGeneratedDiracDualECNormalLocalActualLift
            source current) 0) = 0 := by
  apply ContinuousLinearMap.ext
  intro variation
  change
    holonomicDiracDualFormNativeCoframeFirstVariationDensity source
        (sourceActionGeneratedDiracDualECNormalLocalActualLift source current)
        (fun _ => variation) 0 = 0
  rw [←
    holonomicDiracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_full_of_equations
      source
      (sourceActionGeneratedDiracDualECNormalLocalActualLift source current)
      (sourceActionGeneratedDiracDualECNormalLocalActualLift_simplicity
        source current)
      (sourceActionGeneratedDiracDualECNormalLocalActualLift_auxiliaryEquation
        source current)
      (fun _ => variation) 0]
  exact
    sourceActionGeneratedDiracDualECNormalLocalActualLift_reducedFirstVariation_zero
      source current coframeOne variation

/-! ## Positive P506/L0 specialization -/

def positiveDiracDualECNormalInputActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionLocalActualLift
    positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0

def positiveDiracDualECNormalLocalActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualECNormalLocalActualLift
    positiveSmoothUnifiedSource positiveDiracDualECNormalInputActual

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
