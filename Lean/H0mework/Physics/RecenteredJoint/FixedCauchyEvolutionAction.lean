import H0mework.Physics.DualVariation.ECCauchyConnectionLocalActualLift
import H0mework.Physics.RecenteredJoint.FixedRestart
import H0mework.Physics.RepairedAction.ActionSpatialSectionOperator

/-!
# Fixed canonical section: post-Cartan Cauchy-evolution action

The fixed P506/L0 canonical section already carries the source/current-owned
Cartan connection and live reaction.  At every canonical spatial occurrence
this module next performs the existing repaired matter and constitutive
writes, then applies the KIN-10 Einstein--Cartan evolution write.  KIN-10
changes only the temporal row of the Lorentz first jet and preserves all
spatial rows of the live current.

The generated contact family is read on its physical-time axes to form one
four-dimensional section.  Every constructor consumes only the fixed source
and current.  No residual coordinate, support, branch, target field,
equation receipt, or zero-fiber witness is accepted.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanCauchyEvolutionAction

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeECCauchyConnectionLocalActualLift
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanRestart
open StageNineDiracDualFormNativeIdentityECTemporalEvolutionSection
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineP286ActionCauchySplit

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

private abbrev CartanSectionCurrent : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual

/-- Repaired matter and live constitutive fields generated from the same
spatially recentered Cartan current before the EC evolution write. -/
def fixedP506L0P286CanonicalRecenteredSectionCartanEvolutionPreparedCurrent
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  diracDualFormNativeRepairedConstitutiveWrittenCurrent
    positiveSmoothUnifiedSource
    (spatiallyRecenterHolonomicConfiguration CartanSectionCurrent space)

/-- The KIN-10 source/action-generated evolution actual at one matching
spatial contact. -/
def fixedP506L0P286CanonicalRecenteredSectionCartanCauchyEvolutionContactActual
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift
    positiveSmoothUnifiedSource
    (fixedP506L0P286CanonicalRecenteredSectionCartanEvolutionPreparedCurrent
      space)

/-- One four-dimensional evolution successor assembled from the generated
contact family. -/
def fixedP506L0P286CanonicalRecenteredSectionCartanCauchyEvolutionActual :
    StageNineHolonomicConfiguration :=
  spatialContactTimeAxisDiagonal
    fixedP506L0P286CanonicalRecenteredSectionCartanCauchyEvolutionContactActual

@[simp] theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanEvolutionPreparedCurrent_gravityConnection
    (space : StageNineSpatialPoint) :
    (fixedP506L0P286CanonicalRecenteredSectionCartanEvolutionPreparedCurrent
      space).gravityConnection =
      (spatiallyRecenterHolonomicConfiguration CartanSectionCurrent space
        ).gravityConnection :=
  rfl

@[simp] theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanCauchyEvolutionActual_gravityConnection_slice
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    fixedP506L0P286CanonicalRecenteredSectionCartanCauchyEvolutionActual.gravityConnection
        (canonicalCauchySlicePoint time space) =
      (fixedP506L0P286CanonicalRecenteredSectionCartanCauchyEvolutionContactActual
        space).gravityConnection (canonicalCauchySlicePoint time 0) := by
  simp [fixedP506L0P286CanonicalRecenteredSectionCartanCauchyEvolutionActual,
    spatialContactTimeAxisDiagonal]

/-- At time zero the generated section retains the literal global Cartan
connection value at the same source occurrence. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanCauchyEvolutionActual_gravityConnection_zeroSlice
    (space : StageNineSpatialPoint) :
    fixedP506L0P286CanonicalRecenteredSectionCartanCauchyEvolutionActual.gravityConnection
        (canonicalCauchySlicePoint 0 space) =
      CartanSectionCurrent.gravityConnection
        (canonicalCauchySlicePoint 0 space) := by
  rw [
    fixedP506L0P286CanonicalRecenteredSectionCartanCauchyEvolutionActual_gravityConnection_slice]
  rw [show canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 by
    apply PiLp.ext
    intro direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]]
  unfold
    fixedP506L0P286CanonicalRecenteredSectionCartanCauchyEvolutionContactActual
  rw [
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_connection_zero]
  change
    CartanSectionCurrent.gravityConnection
        (canonicalSpatialContactTranslation space 0) = _
  rw [show canonicalSpatialContactTranslation space 0 =
      canonicalCauchySlicePoint 0 space by
    simpa only [show canonicalCauchySlicePoint 0
        (0 : StageNineSpatialPoint) = 0 by
      apply PiLp.ext
      intro direction
      fin_cases direction <;>
        simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
          Fin.sum_univ_three]] using
      canonicalSpatialContactTranslation_timeAxis space (0 : ℝ)]

/-- Each generated matching contact already closes all twelve EC evolution
rows with the load recomputed on that same output actual. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanCauchyEvolutionContactActual_outputEvolutionBalance
    (space : StageNineSpatialPoint) :
    identityDiracDualECTemporalEvolutionObservation
          (holonomicGravityCurvature
            (fixedP506L0P286CanonicalRecenteredSectionCartanCauchyEvolutionContactActual
              space) 0) +
        identityECSpatialCoframeCoordinatesOfCovector
          (diracDualFormNativeIdentityECLoad positiveSmoothUnifiedSource
            (fixedP506L0P286CanonicalRecenteredSectionCartanCauchyEvolutionContactActual
              space)) =
      0 := by
  exact
    sourceActionGeneratedDiracDualECCauchyConnectionLocalActualLift_outputEvolutionBalance
      positiveSmoothUnifiedSource
      (fixedP506L0P286CanonicalRecenteredSectionCartanEvolutionPreparedCurrent
        space)

/-- The fixed P506/L0 lineage remains the source authority for the generated
evolution section; no source coordinate is added by the action write. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanCauchyEvolutionActual_exactLineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference :=
  fixedP506FormNativeJointActionSolvedSuccessor_exactLineage

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanCauchyEvolutionAction
