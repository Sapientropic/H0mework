import H0mework.Physics.RecenteredJoint.FixedRestart
import H0mework.Physics.RepairedAction.ActionSpatialSectionOperator

/-!
# Fixed canonical section: post-Cartan full joint action

The fixed P506/L0 canonical P286 section already has one global,
source/current-generated Cartan successor.  This module feeds that actual
directly into the existing repaired matter, live-constitutive, and full
Einstein--Cartan action chain at every canonical spatial contact, then
assembles the generated contact family into one four-dimensional section.

Both the contact family and the section consume only the fixed source and the
already generated global current.  No residual coordinate, support branch,
target field, equation receipt, or zero-fiber witness enters either
constructor.  Complete residual substitution remains downstream.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanFullJointAction

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanRestart
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

private abbrev CartanSectionCurrent : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual

private abbrev PrimitiveDiagonalCurrent : StageNineHolonomicConfiguration :=
  positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual

/-! ## Same-source full-joint producer -/

/-- The repaired matter, live constitutive, and full EC response recomputed
from the one global Cartan current at a canonical spatial contact. -/
def fixedP506L0P286CanonicalRecenteredSectionCartanFullJointContactActual
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
    positiveSmoothUnifiedSource
    (spatiallyRecenterHolonomicConfiguration CartanSectionCurrent space)

/-- One four-dimensional common successor assembled from the action-generated
contact family. -/
def fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual :
    StageNineHolonomicConfiguration :=
  spatialContactTimeAxisDiagonal
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointContactActual

/-- The named successor is exactly the existing source/current-only repaired
full-joint spatial operator specialized to the global Cartan current. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual_eq_actionOperator :
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual =
      diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
        positiveSmoothUnifiedSource CartanSectionCurrent :=
  by
    unfold
      fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual
      fixedP506L0P286CanonicalRecenteredSectionCartanFullJointContactActual
      diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator
    rfl

/-- At the canonical zero contact the same global current is consumed
directly; no distinct local-current witness is selected. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointContactActual_zero :
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointContactActual 0 =
      diracDualFormNativeRepairedConstitutiveJointActionResponseOperator
        positiveSmoothUnifiedSource CartanSectionCurrent := by
  simp only [
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointContactActual,
    spatiallyRecenterHolonomicConfiguration_zero]

/-! ## Global primitive responsibility -/

/-- The full-joint tail preserves the three primitive fields it is not
authorized to rewrite.  In particular the P286 connection remains the one
already selected by the canonical mother-action producer. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual_preservedPrimitives :
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual.coframe =
        CartanSectionCurrent.coframe ∧
      fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual.gaugeConnection =
        CartanSectionCurrent.gaugeConnection ∧
      fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual.scalar =
        CartanSectionCurrent.scalar := by
  rw [
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual_eq_actionOperator]
  exact
    ⟨diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_coframe
        positiveSmoothUnifiedSource CartanSectionCurrent,
      diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_gaugeConnection
        positiveSmoothUnifiedSource CartanSectionCurrent,
      diracDualFormNativeRepairedConstitutiveJointActionSpatialSectionOperator_scalar
        positiveSmoothUnifiedSource CartanSectionCurrent⟩

/-- The common successor keeps the explicit KIN-16 global coframe, rather
than only agreeing at one contact or on one time axis. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual_coframe_eq_primitiveDiagonal :
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual.coframe =
      PrimitiveDiagonalCurrent.coframe := by
  calc
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual.coframe =
        CartanSectionCurrent.coframe :=
      fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual_preservedPrimitives.1
    _ = PrimitiveDiagonalCurrent.coframe := by
      rw [fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual_coframe]
      exact
        fixedP506L0P286CanonicalRecenteredSectionActual_coframe_eq_primitiveDiagonal

/-- Direct fixed-lineage regularity of the retained global coframe. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual_coframe_contDiff :
    ContDiff ℝ ∞
      fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual.coframe := by
  rw [
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual_coframe_eq_primitiveDiagonal]
  apply contDiff_pi'
  intro internal
  apply contDiff_pi'
  intro coordinate
  exact
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual_smooth.1
      internal coordinate

/-- The real point domain of the common successor, read from its retained
coframe only after the source/action construction has completed. -/
def fixedP506L0P286CanonicalRecenteredSectionCartanFullJointNondegenerateDomain :
    Set BasePoint :=
  { point |
    Matrix.det
      (fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual.coframe
        point) ≠ 0 }

theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointNondegenerateDomain_eq_cartan :
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointNondegenerateDomain =
      fixedP506L0P286CanonicalRecenteredSectionCartanRestartNondegenerateDomain := by
  ext point
  simp only [
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointNondegenerateDomain,
    fixedP506L0P286CanonicalRecenteredSectionCartanRestartNondegenerateDomain,
    Set.mem_setOf_eq]
  rw [
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual_preservedPrimitives.1]

/-- The generated common domain is inhabited by the fixed P506/L0 origin. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJoint_zero_mem_nondegenerateDomain :
    0 ∈
      fixedP506L0P286CanonicalRecenteredSectionCartanFullJointNondegenerateDomain := by
  rw [
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointNondegenerateDomain_eq_cartan]
  exact
    fixedP506L0P286CanonicalRecenteredSectionCartanRestart_zero_mem_nondegenerateDomain

/-- The physical source side remains the exact fixed P506/L0 lineage.  The
full-joint operator adds no source datum or branch receipt. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanFullJointActual_exactLineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference :=
  fixedP506FormNativeJointActionSolvedSuccessor_exactLineage

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanFullJointAction
