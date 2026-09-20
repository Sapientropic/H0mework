import H0mework.Physics.DualVariation.ECCauchyConnectionLocalActualLift
import H0mework.Physics.DualVariation.ECConstraintSurfaceInitialLocalActualLift
import H0mework.Physics.DualVariation.FourLegCriticalLocusCorrespondence
import H0mework.Physics.CoframeVariation.IIPlusCoframeECBalance

/-!
# Source/action-generated full EC Cauchy local actual

The repaired-root Cauchy development has two complementary action writes.
The first writes the twelve spatial-column evolution observations while
transporting the four constraint rows.  The second takes that output as its
current, retains those twelve observations, and writes the four constraint
rows from the live residual-linear action section.

Their composition consumes only `(source, current)`.  The final actual is
therefore a branch-free, same-contact realization of all sixteen
identity-contact Einstein--Cartan coframe rows.  Both balances below are
producer-soundness for the action equations used by the two writes; they are
not advertised as independent constraints.  The complete six-dimensional
electric-kernel responsibility is transported through both writes.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeECFullCauchyLocalActualLift

open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCartanAffineConnectionActualization
open StageNineCartanTorsionThreeFormCoordinates
open StageNineCartanTangentSimplicityResponse
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCoframeIntegratedVariation
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeECCauchyConnectionLocalActualLift
open StageNineDiracDualFormNativeECConstraintSurfaceInitialLocalActualLift
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECTemporalEvolutionSection
open StageNineDiracDualFormNativeFourLegCriticalLocusCorrespondence
open StageNineDiracDualFormNativeIIPlusCoframeECBalance
open StageNineDiracDualFormNativeIIPlusReductionLocalVariation
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeMatterSpinThreeForm
open StageNineGlobalIntegratedAction
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineIIPlusRestriction
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineTopologicalFourFormPairing
open StageNineTopologicalLorentzThreeFormDuality

noncomputable section

set_option autoImplicit false

/-! ## Source/current-only joint write -/

/-- The action-generated evolution current consumed by the constraint write. -/
def diracDualFormNativeECEvolutionWrittenCurrent
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
    source current

/-- Compose the complementary evolution and constraint writes on one actual.
No target, response, residual, branch, equation, or receipt is accepted. -/
def sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift
    source (diracDualFormNativeECEvolutionWrittenCurrent source current)

private theorem
    diracDualFormNativeECConstraintSurfaceCurrentCurvature_eq_curvature
    (current : StageNineHolonomicConfiguration) :
    diracDualFormNativeECConstraintSurfaceCurrentCurvature current =
      holonomicGravityCurvature current 0 :=
  rfl

/-! ## Primitive-field and regularity transport -/

@[simp] theorem sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift source current
      ).coframe = current.coframe :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift source current
      ).gaugeConnection = current.gaugeConnection :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift source current
      ).gaugeAuxiliary = current.gaugeAuxiliary :=
  rfl

@[simp] theorem sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_scalar
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift source current
      ).scalar = current.scalar :=
  rfl

@[simp] theorem sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_matter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift source current
      ).matter = current.matter :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_conjugateMatter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift source current
      ).conjugateMatter = current.conjugateMatter :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_connection_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift source current
      ).gravityConnection 0 = current.gravityConnection 0 := by
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift,
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_connection_zero]
  exact
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_connection_zero
      source current

theorem sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth) :
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift source current
      ).Smooth := by
  apply
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_smooth
  exact
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_smooth
      source current smooth

theorem sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_nondegenerate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate) :
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift source current
      ).Nondegenerate := by
  apply
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_nondegenerate
  exact
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_nondegenerate
      source current nondegenerate

theorem
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_lorentzAdmissible
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (admissible : GravityConnectionLorentzAdmissible current) :
    GravityConnectionLorentzAdmissible
      (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
        source current) := by
  apply
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_lorentzAdmissible
  exact
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_lorentzAdmissible
      source current admissible

theorem sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_simplicity
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    FormNativeGravitySimplicityEquation
      (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
        source current) :=
  sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_simplicity
    source (diracDualFormNativeECEvolutionWrittenCurrent source current)

theorem
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_reactionSelfGenerated
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift source current
      ).gravitySimplicityMultiplier =
      formNativeGravityReactionField
        (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
          source current) :=
  sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_reactionSelfGenerated
    source (diracDualFormNativeECEvolutionWrittenCurrent source current)

theorem
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_auxiliaryEquation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    FormNativeGravityAuxiliaryEquation
      (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
        source current) :=
  sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_auxiliaryEquation
    source (diracDualFormNativeECEvolutionWrittenCurrent source current)

/-! ## Contact Cartan producer preservation -/

/-- Both connection writes preserve the source/action-generated Cartan
connection at the common contact.  This is producer soundness at `0`, not a
whole-pointwise propagation claim. -/
theorem
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_connectionSelfGenerated_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (selfGenerated :
      current.gravityConnection 0 =
        diracDualFormNativeActionCartanConnectionAt source current 0) :
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
        source current).gravityConnection 0 =
      diracDualFormNativeActionCartanConnectionAt source
        (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
          source current) 0 := by
  let evolved := diracDualFormNativeECEvolutionWrittenCurrent source current
  let final :=
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift source current
  have evolvedSelfGenerated :
      evolved.gravityConnection 0 =
        diracDualFormNativeActionCartanConnectionAt source evolved 0 :=
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_connectionSelfGenerated_zero
      source current selfGenerated
  calc
    final.gravityConnection 0 = evolved.gravityConnection 0 :=
      sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_connection_zero
        source evolved
    _ = diracDualFormNativeActionCartanConnectionAt source evolved 0 :=
      evolvedSelfGenerated
    _ = diracDualFormNativeActionCartanConnectionAt source final 0 := by
      unfold diracDualFormNativeActionCartanConnectionAt
        diracDualFormNativeActionCartanContorsionAt
        diracDualFormNativeActionCartanTorsionAt
      rw [diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
        source evolved final 0 rfl rfl rfl]
      rfl

/-- Typed torsion--spin producer readback on the same final contact. -/
theorem
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_typedTorsionSpin_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (selfGenerated :
      current.gravityConnection 0 =
        diracDualFormNativeActionCartanConnectionAt source current 0) :
    cartanTorsionThreeForm
        ((sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
          source current).coframe 0)
        (actualPointwiseCartanTorsionTwoForm
          (holonomicCoframeFirstJetAt
            (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
              source current).coframe 0)
          ((sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
            source current).gravityConnection 0)) =
      diracDualFormNativeActionSpinResponseAt source
        (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
          source current) 0 := by
  rw [
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_connectionSelfGenerated_zero
      source current selfGenerated]
  exact diracDualFormNativeActionCartanConnectionAt_generates_spinResponse
    source
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift source current)
    0 (by simpa using nondegenerate)

/-- Physical three-form presentation of the same contact Cartan equation. -/
theorem
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_torsionSpin_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : Matrix.det (current.coframe 0) ≠ 0)
    (selfGenerated :
      current.gravityConnection 0 =
        diracDualFormNativeActionCartanConnectionAt source current 0) :
    internalBivectorDualThreeForm
        (torsionCoframeWedgeThreeForm
          ((sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
            source current).coframe 0)
          (pointwiseCartanTorsion
            (holonomicCoframeFirstJetAt
              (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
                source current).coframe 0)
            ((sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
              source current).gravityConnection 0))) =
      formNativePhysicalSpinCurrentThreeForm source 0 0
        (toContinuumPointField
          (restrictHolonomicConfigurationToIIPlus
            (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
              source current)) 0) := by
  rw [← cartanTorsionThreeForm_actualPointwiseCartanTorsionTwoForm]
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_typedTorsionSpin_zero
      source current nondegenerate selfGenerated

/-! ## Same-output simultaneous Cauchy closure -/

/-- The twelve action evolution rows remain zero after the four-row
constraint write, with the load recomputed on the final actual. -/
theorem
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_evolutionBalance
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    identityDiracDualECTemporalEvolutionObservation
          (holonomicGravityCurvature
            (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
              source current) 0) +
        identityECSpatialCoframeCoordinatesOfCovector
          (diracDualFormNativeIdentityECLoad source
            (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
              source current)) =
      0 := by
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift,
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_evolutionObservation,
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_load_stable,
    diracDualFormNativeECConstraintSurfaceCurrentCurvature_eq_curvature]
  exact
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_outputEvolutionBalance
      source current

/-- The four action constraint rows vanish on that same final actual. -/
theorem
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_constraintBalance
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    identityDiracDualECConstraintObservation
          (holonomicGravityCurvature
            (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
              source current) 0) +
        identityECConstraintCoordinatesOfCovector
          (diracDualFormNativeIdentityECLoad source
            (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
              source current)) =
      0 :=
  sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_constraintBalance
    source (diracDualFormNativeECEvolutionWrittenCurrent source current)

/-- Fixed endpoint for this checkpoint: all sixteen identity-contact EC
Cauchy rows close on one source/action-generated actual. -/
theorem
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_simultaneousBalance
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (identityDiracDualECTemporalEvolutionObservation
            (holonomicGravityCurvature
              (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
                source current) 0) +
          identityECSpatialCoframeCoordinatesOfCovector
            (diracDualFormNativeIdentityECLoad source
              (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
                source current)) =
        0) ∧
      (identityDiracDualECConstraintObservation
            (holonomicGravityCurvature
              (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
                source current) 0) +
          identityECConstraintCoordinatesOfCovector
            (diracDualFormNativeIdentityECLoad source
              (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
                source current)) =
        0) :=
  ⟨sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_evolutionBalance
      source current,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_constraintBalance
      source current⟩

/-! ## Full coframe readback

The two complementary action writes above already generate every identity
contact coframe row.  The following theorems only reassemble those rows into
the authoritative repaired-root coframe covector and then use the generated
simplicity and auxiliary equations to return from the computed `II+`
restriction to the full primitive variation. -/

theorem
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_EC_covector_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature
            (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
              source current) 0) +
        diracDualFormNativeIdentityECLoad source
          (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
            source current) =
      0 := by
  rcases
      sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_simultaneousBalance
        source current with
    ⟨evolution, constraint⟩
  apply (coframeCovector_eq_iff_coordinateDirections _ _).2
  intro row column
  fin_cases column
  · have coordinate := congrFun constraint row
    simpa [identityDiracDualECConstraintObservation,
      identityECConstraintCoordinatesOfCovector] using coordinate
  · have coordinate := congrFun (congrFun evolution row) 0
    simpa [identityDiracDualECTemporalEvolutionObservation,
      identityECSpatialCoframeCoordinatesOfCovector] using coordinate
  · have coordinate := congrFun (congrFun evolution row) 1
    simpa [identityDiracDualECTemporalEvolutionObservation,
      identityECSpatialCoframeCoordinatesOfCovector] using coordinate
  · have coordinate := congrFun (congrFun evolution row) 2
    simpa [identityDiracDualECTemporalEvolutionObservation,
      identityECSpatialCoframeCoordinatesOfCovector] using coordinate

private theorem
    identityDiracDualECCurvatureObservation_intrinsic_apply_fullCauchy
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
            (coframeWedge (1 : LorentzianCoframe)))) =
      _
  rw [gravityInternalPairVarianceNormalization_involutive]

private theorem
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_ECNormalContactField_eq_restrict
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    diracDualFormNativeECNormalContactField
        (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
          source current) =
      restrictContinuumPointFieldToIIPlus
        (toContinuumPointField
          (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
            source current) 0) := by
  unfold diracDualFormNativeECNormalContactField
    diracDualFormNativeECNormalPreparedActual
  rw [
    (restrictHolonomicConfigurationToIIPlus_eq_self_iff_diracDualFormNativeSimplicity
      (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
        source current)).2
      (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_simplicity
        source current)]

theorem
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_ECBalance_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (coframeOne : current.coframe 0 = 1)
    (variation : LorentzianCoframe) :
    gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent
            ((sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
              source current).coframe 0) variation)
          (gravityInternalPairVarianceNormalization
              (toContinuumPointField
                (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
                  source current) 0).gravityCurvature +
            coframeWedge
              ((sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
                source current).coframe 0)) +
        diracDualFormNativeCoframeGaugeEulerCovector source
          (restrictContinuumPointFieldToIIPlus
            (toContinuumPointField
              (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
                source current) 0)) variation +
        diracDualFormNativeCoframeMatterEulerCovector source 0
          (restrictContinuumPointFieldToIIPlus
            (toContinuumPointField
              (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
                source current) 0)) variation =
      0 := by
  have balance := congrArg
    (fun covector : LorentzianCoframe →L[ℝ] ℝ => covector variation)
    (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_EC_covector_zero
      source current)
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_coframe,
    coframeOne]
  rw [gravityTopologicalWedgeCoefficient_add_right]
  rw [show
      gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent
            (1 : LorentzianCoframe) variation)
          (gravityInternalPairVarianceNormalization
            (toContinuumPointField
              (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
                source current) 0).gravityCurvature) =
        identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature
            (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
              source current) 0) variation by
      rfl]
  rw [←
    identityDiracDualECCurvatureObservation_intrinsic_apply_fullCauchy
      variation]
  unfold diracDualFormNativeIdentityECLoad at balance
  rw [
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_ECNormalContactField_eq_restrict
      source current] at balance
  simpa only [add_apply, zero_apply, add_assoc] using balance

theorem
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_reducedFirstVariation_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (coframeOne : current.coframe 0 = 1)
    (variation : LorentzianCoframe) :
    diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity source 0
        (toContinuumPointField
          (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
            source current) 0) variation =
      0 := by
  rw [
    diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_EC_balance
      source 0
      (toContinuumPointField
        (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
          source current) 0)
      (by
        change Matrix.det (current.coframe 0) ≠ 0
        rw [coframeOne]
        norm_num)
      variation]
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_ECBalance_zero
      source current coframeOne variation

theorem
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_fullCoframeEuler_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (coframeOne : current.coframe 0 = 1) :
    diracDualFormNativeCoframeEulerCovector source 0
        (toContinuumPointField
          (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
            source current) 0) =
      0 := by
  apply ContinuousLinearMap.ext
  intro variation
  change
    holonomicDiracDualFormNativeCoframeFirstVariationDensity source
        (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
          source current)
        (fun _ => variation) 0 =
      0
  rw [←
    holonomicDiracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_full_of_equations
      source
      (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
        source current)
      (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_simplicity
        source current)
      (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_auxiliaryEquation
        source current)
      (fun _ => variation) 0]
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_reducedFirstVariation_zero
      source current coframeOne variation

/-! ## Responsibility transport -/

/-- Neither complementary write erases the six-dimensional electric-kernel
responsibility carried by the input current. -/
theorem
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_electricKernel
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    identityDiracDualECTemporalEvolutionKernelPart
        (identityECTemporalCurvatureCoordinatesOf
          (holonomicGravityCurvature
            (sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
              source current) 0)) =
      identityDiracDualECTemporalEvolutionKernelPart
        (identityECTemporalCurvatureCoordinatesOf
          (diracDualFormNativeECCauchyCurrentCurvature current)) := by
  rw [sourceActionGeneratedDiracDualECFullCauchyLocalActualLift,
    sourceActionGeneratedDiracDualECConstraintSurfaceInitialLocalActualLift_electricKernelFaithful,
    diracDualFormNativeECConstraintSurfaceCurrentCurvature_eq_curvature]
  exact
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_electricKernel
      source current

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeECFullCauchyLocalActualLift
