import H0mework.Physics.CartanAction.CartanReactionLocalActualLiftRegression
import H0mework.Physics.DualVariation.ECCauchyConnectionLocalActualLift

/-!
# Regression for the repaired-root EC Cauchy connection write

The fixed exact P506/L0 source specializes the generic temporal evolution
producer at the live KIN-8 Cartan/reaction actual.  The output is smooth,
nondegenerate, Lorentz admissible, simple, reaction-settled, and retains the
same Cartan/torsion--spin contact.  Its twelve spatial-column EC rows close by
producer soundness.

The four temporal-column rows are deliberately not accepted by the
constructor.  Their complete residual is transported from the current
actual and remains the independent Cauchy-constraint readout.  Consequently
this checkpoint is an honest evolution write, not a snapshot theorem that
hides the Hamiltonian constraint inside a freely chosen 36-coordinate
curvature target.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeECCauchyConnectionLocalActualLiftRegression

open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineCanonicalCauchyState
open StageNineCartanTangentSimplicityResponse
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLiftRegression
open StageNineDiracDualFormNativeCartanGravityAuxiliaryObstructionRegression
open StageNineDiracDualFormNativeCartanReactionLocalActualLiftRegression
open StageNineDiracDualFormNativeECCauchyConnectionLocalActualLift
open StageNineDiracDualFormNativeIdentityECTemporalEvolutionSection
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineGlobalIntegratedAction
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineJointActionLocalActualLift
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceGeneratedMatterSpinActionUpdate

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Fixed P506/L0 specialization of the source/current-only Cauchy write. -/
def positiveDiracDualECCauchyConnectionLocalActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
    positiveSmoothUnifiedSource positiveDiracDualCartanReactionLocalActual

theorem positiveDiracDualECCauchyCurrentCurvature_eq_connectionOnly :
    diracDualFormNativeECCauchyCurrentCurvature
        positiveDiracDualCartanReactionLocalActual =
      holonomicGravityCurvature
        positiveDiracDualCartanConnectionLocalActual 0 := by
  rfl

theorem positiveDiracDualECCauchyConnectionLocalActual_smooth :
    positiveDiracDualECCauchyConnectionLocalActual.Smooth :=
  sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_smooth
    positiveSmoothUnifiedSource positiveDiracDualCartanReactionLocalActual
    positiveDiracDualCartanReactionLocalActual_smooth

theorem positiveDiracDualECCauchyConnectionLocalActual_nondegenerate :
    positiveDiracDualECCauchyConnectionLocalActual.Nondegenerate :=
  sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_nondegenerate
    positiveSmoothUnifiedSource positiveDiracDualCartanReactionLocalActual
    positiveDiracDualCartanReactionLocalActual_nondegenerate

theorem positiveDiracDualECCauchyConnectionLocalActual_lorentzAdmissible :
    GravityConnectionLorentzAdmissible
      positiveDiracDualECCauchyConnectionLocalActual :=
  sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_lorentzAdmissible
    positiveSmoothUnifiedSource positiveDiracDualCartanReactionLocalActual
    positiveDiracDualCartanReactionLocalActual_lorentzAdmissible

theorem positiveDiracDualECCauchyConnectionLocalActual_simplicity :
    FormNativeGravitySimplicityEquation
      positiveDiracDualECCauchyConnectionLocalActual :=
  sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_simplicity
    positiveSmoothUnifiedSource positiveDiracDualCartanReactionLocalActual

theorem positiveDiracDualECCauchyConnectionLocalActual_auxiliaryEquation :
    FormNativeGravityAuxiliaryEquation
      positiveDiracDualECCauchyConnectionLocalActual :=
  sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_auxiliaryEquation
    positiveSmoothUnifiedSource positiveDiracDualCartanReactionLocalActual

theorem positiveDiracDualECCauchyConnectionLocalActual_connection_zero :
    positiveDiracDualECCauchyConnectionLocalActual.gravityConnection 0 =
      positiveDiracDualCartanReactionLocalActual.gravityConnection 0 :=
  sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_connection_zero
    positiveSmoothUnifiedSource positiveDiracDualCartanReactionLocalActual

theorem positiveDiracDualECCauchyConnectionLocalActual_connectionSelfGenerated_zero :
    positiveDiracDualECCauchyConnectionLocalActual.gravityConnection 0 =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        positiveDiracDualECCauchyConnectionLocalActual 0 := by
  exact
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_connectionSelfGenerated_zero
      positiveSmoothUnifiedSource positiveDiracDualCartanReactionLocalActual
      (positiveDiracDualCartanReactionLocalActual_connection_selfGenerated 0)

private theorem positiveDiracDualCartanReactionLocalActual_coframe_one :
    positiveDiracDualCartanReactionLocalActual.coframe 0 = 1 := by
  change positiveSourceTargetMatterCauchyState.coframe 0 = 1
  change positivePhaseProbeCauchyState.coframe 0 = 1
  rw [positivePhaseProbeCauchyState_eq_normalForm]
  rfl

theorem positiveDiracDualECCauchyConnectionLocalActual_torsionSpin_zero :
    internalBivectorDualThreeForm
        (torsionCoframeWedgeThreeForm
          (positiveDiracDualECCauchyConnectionLocalActual.coframe 0)
          (pointwiseCartanTorsion
            (holonomicCoframeFirstJetAt
              positiveDiracDualECCauchyConnectionLocalActual.coframe 0)
            (positiveDiracDualECCauchyConnectionLocalActual.gravityConnection
              0))) =
      formNativePhysicalSpinCurrentThreeForm positiveSmoothUnifiedSource 0 0
        (toContinuumPointField
          (restrictHolonomicConfigurationToIIPlus
            positiveDiracDualECCauchyConnectionLocalActual) 0) := by
  exact
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_torsionSpin_zero
      positiveSmoothUnifiedSource positiveDiracDualCartanReactionLocalActual
      (by
        rw [positiveDiracDualCartanReactionLocalActual_coframe_one]
        norm_num)
      (positiveDiracDualCartanReactionLocalActual_connection_selfGenerated 0)

theorem positiveDiracDualECCauchyConnectionLocalActual_evolutionBalance :
    identityDiracDualECTemporalEvolutionObservation
          (holonomicGravityCurvature
            positiveDiracDualECCauchyConnectionLocalActual 0) +
        identityECSpatialCoframeCoordinatesOfCovector
          (diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
            positiveDiracDualCartanReactionLocalActual) =
      0 :=
  sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_evolutionBalance
    positiveSmoothUnifiedSource positiveDiracDualCartanReactionLocalActual

/-- The same twelve evolution rows remain closed when the non-gravity load is
read back from the output actual itself.  This is the live read-after-write
regression; it is producer soundness, not an independent Cauchy constraint. -/
theorem positiveDiracDualECCauchyConnectionLocalActual_outputEvolutionBalance :
    identityDiracDualECTemporalEvolutionObservation
          (holonomicGravityCurvature
            positiveDiracDualECCauchyConnectionLocalActual 0) +
        identityECSpatialCoframeCoordinatesOfCovector
          (diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
            positiveDiracDualECCauchyConnectionLocalActual) =
      0 :=
  sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_outputEvolutionBalance
    positiveSmoothUnifiedSource positiveDiracDualCartanReactionLocalActual

theorem positiveDiracDualECCauchyConnectionLocalActual_constraintResidual :
    identityDiracDualECConstraintObservation
          (holonomicGravityCurvature
            positiveDiracDualECCauchyConnectionLocalActual 0) +
        identityECConstraintCoordinatesOfCovector
          (diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
            positiveDiracDualCartanReactionLocalActual) =
      identityDiracDualECConstraintObservation
          (diracDualFormNativeECCauchyCurrentCurvature
            positiveDiracDualCartanReactionLocalActual) +
        identityECConstraintCoordinatesOfCovector
          (diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
            positiveDiracDualCartanReactionLocalActual) :=
  sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_constraintResidual
    positiveSmoothUnifiedSource positiveDiracDualCartanReactionLocalActual

/-- The independent constraint read is transported even after the live load
is recomputed on the output actual. -/
theorem positiveDiracDualECCauchyConnectionLocalActual_outputConstraintResidual :
    identityDiracDualECConstraintObservation
          (holonomicGravityCurvature
            positiveDiracDualECCauchyConnectionLocalActual 0) +
        identityECConstraintCoordinatesOfCovector
          (diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
            positiveDiracDualECCauchyConnectionLocalActual) =
      identityDiracDualECConstraintObservation
          (diracDualFormNativeECCauchyCurrentCurvature
            positiveDiracDualCartanReactionLocalActual) +
        identityECConstraintCoordinatesOfCovector
          (diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
            positiveDiracDualCartanReactionLocalActual) :=
  sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_outputConstraintResidual
    positiveSmoothUnifiedSource positiveDiracDualCartanReactionLocalActual

theorem positiveDiracDualECCauchyConnectionLocalActual_directRegression :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
        canonicalP506SourceAffineL0ObservableLineageReference ∧
      positiveDiracDualECCauchyConnectionLocalActual.Smooth ∧
      positiveDiracDualECCauchyConnectionLocalActual.Nondegenerate ∧
      GravityConnectionLorentzAdmissible
        positiveDiracDualECCauchyConnectionLocalActual ∧
      FormNativeGravitySimplicityEquation
        positiveDiracDualECCauchyConnectionLocalActual ∧
      FormNativeGravityAuxiliaryEquation
        positiveDiracDualECCauchyConnectionLocalActual ∧
      positiveDiracDualECCauchyConnectionLocalActual.gravityConnection 0 =
        diracDualFormNativeActionCartanConnectionAt
          positiveSmoothUnifiedSource
          positiveDiracDualECCauchyConnectionLocalActual 0 ∧
      identityDiracDualECTemporalEvolutionObservation
            (holonomicGravityCurvature
              positiveDiracDualECCauchyConnectionLocalActual 0) +
          identityECSpatialCoframeCoordinatesOfCovector
            (diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
              positiveDiracDualECCauchyConnectionLocalActual) =
        0 := by
  exact
    ⟨positiveSmoothUnifiedSource_generates_exactP506L0Lineage,
      positiveDiracDualECCauchyConnectionLocalActual_smooth,
      positiveDiracDualECCauchyConnectionLocalActual_nondegenerate,
      positiveDiracDualECCauchyConnectionLocalActual_lorentzAdmissible,
      positiveDiracDualECCauchyConnectionLocalActual_simplicity,
      positiveDiracDualECCauchyConnectionLocalActual_auxiliaryEquation,
      positiveDiracDualECCauchyConnectionLocalActual_connectionSelfGenerated_zero,
      positiveDiracDualECCauchyConnectionLocalActual_outputEvolutionBalance⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeECCauchyConnectionLocalActualLiftRegression
