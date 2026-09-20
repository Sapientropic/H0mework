import H0mework.Physics.CartanAction.CartanConnectionActualizationRegression
import H0mework.Physics.CartanAction.CartanConnectionLocalActualLift
import H0mework.Physics.Dirac.GeneratedMatterSpinActionUpdate

/-!
# Regressions for the repaired-action local Cartan connection

The fixed P506/L0 source is specialized through the generic local producer.
At the origin the result agrees with the previously checked pointwise
connection, while globally it is now a smooth primitive connection field and
obeys the raw torsion--spin equation at every point.

The pure Levi--Civita connection on the same origin coframe remains the
negative control: it has zero Cartan response and cannot reproduce the
nonzero action-generated W13 current.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanConnectionLocalActualLiftRegression

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionActualizationRegression
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeLorentzTorsionSpinEquation
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineSourceGeneratedMatterSpinActionUpdate

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Positive P506/L0 specialization of the pointwise-recomputed local
connection producer. -/
def positiveDiracDualCartanConnectionLocalActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
    positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0

private theorem positiveSourceTargetMatterCauchyState_coframe_nondegenerate :
    Matrix.det (positiveSourceTargetMatterCauchyState.coframe 0) ≠ 0 := by
  exact positiveSourceTargetMatterActual_nondegenerate 0

theorem positiveDiracDualCartanConnectionLocalActual_smooth :
    positiveDiracDualCartanConnectionLocalActual.Smooth := by
  exact sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_smooth
    positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0
    positiveSourceTargetMatterCauchyState_coframe_nondegenerate

theorem positiveDiracDualCartanConnectionLocalActual_nondegenerate :
    positiveDiracDualCartanConnectionLocalActual.Nondegenerate := by
  exact
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_nondegenerate
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0
      positiveSourceTargetMatterCauchyState_coframe_nondegenerate

theorem positiveDiracDualCartanConnectionLocalActual_simplicity :
    FormNativeGravitySimplicityEquation
      positiveDiracDualCartanConnectionLocalActual := by
  exact
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_simplicity
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0

theorem positiveDiracDualCartanConnectionLocalActual_lorentzAdmissible :
    GravityConnectionLorentzAdmissible
      positiveDiracDualCartanConnectionLocalActual := by
  exact
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_lorentzAdmissible
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0
      positiveSourceTargetMatterCauchyState_coframe_nondegenerate

theorem positiveDiracDualCartanConnectionLocalActual_torsionSpinEquation :
    FormNativeIIPlusTorsionSpinEquation positiveSmoothUnifiedSource
      positiveDiracDualCartanConnectionLocalActual := by
  exact
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_torsionSpinEquation
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0
      positiveSourceTargetMatterCauchyState_coframe_nondegenerate

theorem positiveDiracDualCartanConnectionLocalActual_selfGenerated
    (point : BasePoint) :
    positiveDiracDualCartanConnectionLocalActual.gravityConnection point =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        positiveDiracDualCartanConnectionLocalActual point := by
  exact
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_connection_selfGenerated
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0 point

theorem positiveDiracDualCartanConnectionLocalActual_originConnection :
    positiveDiracDualCartanConnectionLocalActual.gravityConnection 0 =
      fixedActionCartanConnection := by
  rfl

theorem positiveDiracDualCartanConnectionLocalActual_originResponse :
    diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
        positiveDiracDualCartanConnectionLocalActual 0 =
      fixedActionSpinResponse := by
  exact
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_spinResponse_eq_base
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0 0

/-- Same-source negative regression lifted to the generated local actual:
its origin connection is genuinely different from the pure Levi--Civita
lookalike that erases the nonzero W13 response. -/
theorem positiveDiracDualCartanConnectionLocalActual_origin_ne_leviCivita :
    positiveDiracDualCartanConnectionLocalActual.gravityConnection 0 ≠
      fixedCoframeJet.lorentzSpinConnection := by
  rw [positiveDiracDualCartanConnectionLocalActual_originConnection]
  exact fixedActionCartanConnection_ne_leviCivita

/-- Bundled positive/negative checkpoint.  The prior matter actual remains a
separate source/action output; changing the connection invalidates its old
connection-dependent receipts rather than silently transporting them. -/
theorem positiveDiracDualCartanConnectionLocalActual_directRegression :
    PositiveSourceGeneratedMatterSpinActionUpdateLaw
        positiveSourceTargetMatterActual ∧
      positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
        canonicalP506SourceAffineL0ObservableLineageReference ∧
      positiveDiracDualCartanConnectionLocalActual.Smooth ∧
      positiveDiracDualCartanConnectionLocalActual.Nondegenerate ∧
      FormNativeGravitySimplicityEquation
        positiveDiracDualCartanConnectionLocalActual ∧
      GravityConnectionLorentzAdmissible
        positiveDiracDualCartanConnectionLocalActual ∧
      FormNativeIIPlusTorsionSpinEquation positiveSmoothUnifiedSource
        positiveDiracDualCartanConnectionLocalActual ∧
      (∀ point,
        positiveDiracDualCartanConnectionLocalActual.gravityConnection point =
          diracDualFormNativeActionCartanConnectionAt
            positiveSmoothUnifiedSource
            positiveDiracDualCartanConnectionLocalActual point) ∧
      diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
          positiveDiracDualCartanConnectionLocalActual 0 =
        fixedActionSpinResponse ∧
      fixedActionSpinResponse ≠ 0 ∧
      positiveDiracDualCartanConnectionLocalActual.gravityConnection 0 ≠
        fixedCoframeJet.lorentzSpinConnection := by
  exact
    ⟨positiveSourceGeneratedMatterSpinActionUpdate_realizes_C3h107,
      positiveSmoothUnifiedSource_generates_exactP506L0Lineage,
      positiveDiracDualCartanConnectionLocalActual_smooth,
      positiveDiracDualCartanConnectionLocalActual_nondegenerate,
      positiveDiracDualCartanConnectionLocalActual_simplicity,
      positiveDiracDualCartanConnectionLocalActual_lorentzAdmissible,
      positiveDiracDualCartanConnectionLocalActual_torsionSpinEquation,
      positiveDiracDualCartanConnectionLocalActual_selfGenerated,
      positiveDiracDualCartanConnectionLocalActual_originResponse,
      fixedActionSpinResponse_ne_zero,
      positiveDiracDualCartanConnectionLocalActual_origin_ne_leviCivita⟩

end


end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanConnectionLocalActualLiftRegression
