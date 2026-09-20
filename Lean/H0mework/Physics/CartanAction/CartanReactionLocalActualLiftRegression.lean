import H0mework.Physics.CartanAction.CartanGravityAuxiliaryObstructionRegression
import H0mework.Physics.CartanAction.CartanReactionLocalActualLift

/-!
# Regression for the live Cartan gravity reaction write

The positive P506/L0 specialization first keeps the KIN-7 changed-read trace

```text
Cartan connection write -> delta B(01,31) = -1/16,
```

then installs the unique live reaction computed from the same `B` and
derived curvature.  The new multiplier coordinate is `+1/16`, and the whole
`delta B` field vanishes by producer soundness.  The constructor never reads
either displayed coordinate.

This is an actual/write epoch under the same mother action and hash.  It does
not yet close the coframe Euler equation, global integrability, or full
stationarity.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanReactionLocalActualLiftRegression

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionActualizationRegression
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanConnectionLocalActualLiftRegression
open StageNineDiracDualFormNativeCartanGravityAuxiliaryObstructionRegression
open StageNineDiracDualFormNativeCartanReactionLocalActualLift
open StageNineDiracDualFormNativeIIPlusCoframeECBalance
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeLorentzTorsionSpinEquation
open StageNineGlobalIntegratedAction
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineJointActionLocalActualLift
open StageNineSourceGeneratedMatterSpinActionUpdate

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

/-- Positive P506/L0 specialization of the no-free-parameter KIN-8 reaction
installer. -/
def positiveDiracDualCartanReactionLocalActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionLocalActualLift
    positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0

private theorem positiveSourceTargetMatterCauchyState_coframe_nondegenerate :
    Matrix.det (positiveSourceTargetMatterCauchyState.coframe 0) ≠ 0 := by
  exact positiveSourceTargetMatterActual_nondegenerate 0

theorem positiveDiracDualCartanReactionLocalActual_smooth :
    positiveDiracDualCartanReactionLocalActual.Smooth := by
  exact sourceActionGeneratedDiracDualCartanReactionLocalActualLift_smooth
    positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0
    positiveSourceTargetMatterCauchyState_coframe_nondegenerate

theorem positiveDiracDualCartanReactionLocalActual_nondegenerate :
    positiveDiracDualCartanReactionLocalActual.Nondegenerate := by
  exact
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_nondegenerate
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0
      positiveSourceTargetMatterCauchyState_coframe_nondegenerate

theorem positiveDiracDualCartanReactionLocalActual_simplicity :
    FormNativeGravitySimplicityEquation
      positiveDiracDualCartanReactionLocalActual := by
  exact sourceActionGeneratedDiracDualCartanReactionLocalActualLift_simplicity
    positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0

theorem positiveDiracDualCartanReactionLocalActual_lorentzAdmissible :
    GravityConnectionLorentzAdmissible
      positiveDiracDualCartanReactionLocalActual := by
  exact
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_lorentzAdmissible
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0
      positiveSourceTargetMatterCauchyState_coframe_nondegenerate

theorem positiveDiracDualCartanReactionLocalActual_connection_selfGenerated
    (point : BasePoint) :
    positiveDiracDualCartanReactionLocalActual.gravityConnection point =
      diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
        positiveDiracDualCartanReactionLocalActual point := by
  exact
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_connection_selfGenerated
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0 point

theorem positiveDiracDualCartanReactionLocalActual_torsionSpinEquation :
    FormNativeIIPlusTorsionSpinEquation positiveSmoothUnifiedSource
      positiveDiracDualCartanReactionLocalActual := by
  exact
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_torsionSpinEquation
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0
      positiveSourceTargetMatterCauchyState_coframe_nondegenerate

theorem positiveDiracDualCartanReactionLocalActual_reaction_selfGenerated :
    positiveDiracDualCartanReactionLocalActual.gravitySimplicityMultiplier =
      formNativeGravityReactionField
        positiveDiracDualCartanReactionLocalActual := by
  exact
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_reaction_selfGenerated
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0

/-- Whole-field `delta B = 0` after the reaction write.  This is explicitly
producer soundness, since the write was defined by this action zero fiber. -/
theorem positiveDiracDualCartanReactionLocalActual_auxiliaryEquation :
    FormNativeGravityAuxiliaryEquation
      positiveDiracDualCartanReactionLocalActual := by
  exact
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_auxiliaryEquation
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0

private theorem positiveDiracDualCartanReactionLocalActual_coframe_one
    (point : BasePoint) :
    positiveDiracDualCartanReactionLocalActual.coframe point = 1 := by
  change positiveSourceTargetMatterCauchyState.coframe 0 = 1
  change positivePhaseProbeCauchyState.coframe 0 = 1
  rw [positivePhaseProbeCauchyState_eq_normalForm]
  rfl

/-- Convention-locked readout of the actual installed reaction.  It is
computed from the live field formula, not supplied to the installer. -/
theorem positiveDiracDualCartanReactionLocalActual_multiplier_zero_four :
    positiveDiracDualCartanReactionLocalActual.gravitySimplicityMultiplier
        0 0 4 = (1 / 16 : ℝ) := by
  change
    (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0).gravitySimplicityMultiplier
        0 0 4 = _
  rw [sourceActionGeneratedDiracDualCartanReactionLocalActualLift_multiplier]
  unfold sourceActionGeneratedDiracDualCartanReactionField
  unfold formNativeGravityReactionField
  have baseCurvature :
      holonomicContravariantGravityCurvature
          (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
            positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0)
          0 0 4 = -(1 / 16 : ℝ) :=
    positiveDiracDualCartanConnection_contravariantCurvature_zero_four
  have baseCoframeOne :
      (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
        positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0).coframe
          0 = 1 :=
    positiveDiracDualCartanReactionLocalActual_coframe_one 0
  rw [sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_simplicity
        positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0 0,
    gravityInternalDualEquiv_physicalIIPlusBivector_eq_neg_coframeWedge]
  change
    -(coframeWedge
        ((sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
          positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0).coframe
            0) 0 4) -
      holonomicContravariantGravityCurvature
        (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
          positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0)
        0 0 4 = _
  rw [baseCurvature, baseCoframeOne]
  norm_num [coframeWedge, pairFirst, pairSecond, Matrix.one_apply]
  simp +decide

/-- The live reaction write genuinely changes the KIN-6 actual; it does not
rename the rejected connection-only endpoint. -/
theorem positiveDiracDualCartanReactionLocalActual_ne_connectionOnly :
    positiveDiracDualCartanReactionLocalActual ≠
      positiveDiracDualCartanConnectionLocalActual := by
  intro equality
  apply positiveDiracDualCartanConnection_not_auxiliaryEquation
  rw [← equality]
  exact positiveDiracDualCartanReactionLocalActual_auxiliaryEquation

/-- Positive/negative checkpoint for the first two read-after-write edges.
The old nonzero residual remains a trace; the new whole-field zero is only
the soundness of the unique reaction write. -/
theorem positiveDiracDualCartanReactionLocalActual_directRegression :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
        canonicalP506SourceAffineL0ObservableLineageReference ∧
      positiveDiracDualCartanReactionLocalActual.Smooth ∧
      positiveDiracDualCartanReactionLocalActual.Nondegenerate ∧
      FormNativeGravitySimplicityEquation
        positiveDiracDualCartanReactionLocalActual ∧
      GravityConnectionLorentzAdmissible
        positiveDiracDualCartanReactionLocalActual ∧
      FormNativeIIPlusTorsionSpinEquation positiveSmoothUnifiedSource
        positiveDiracDualCartanReactionLocalActual ∧
      (∀ point,
        positiveDiracDualCartanReactionLocalActual.gravityConnection point =
          diracDualFormNativeActionCartanConnectionAt
            positiveSmoothUnifiedSource
            positiveDiracDualCartanReactionLocalActual point) ∧
      positiveDiracDualCartanReactionLocalActual.gravitySimplicityMultiplier =
        formNativeGravityReactionField
          positiveDiracDualCartanReactionLocalActual ∧
      FormNativeGravityAuxiliaryEquation
        positiveDiracDualCartanReactionLocalActual ∧
      positiveDiracDualCartanReactionLocalActual.gravitySimplicityMultiplier
          0 0 4 = (1 / 16 : ℝ) ∧
      holonomicFormNativeGravityAuxiliaryEulerResidual
          positiveDiracDualCartanConnectionLocalActual 0 0 4 =
        -(1 / 16 : ℝ) ∧
      ¬FormNativeGravityAuxiliaryEquation
        positiveDiracDualCartanConnectionLocalActual ∧
      positiveDiracDualCartanReactionLocalActual ≠
        positiveDiracDualCartanConnectionLocalActual := by
  exact
    ⟨positiveSmoothUnifiedSource_generates_exactP506L0Lineage,
      positiveDiracDualCartanReactionLocalActual_smooth,
      positiveDiracDualCartanReactionLocalActual_nondegenerate,
      positiveDiracDualCartanReactionLocalActual_simplicity,
      positiveDiracDualCartanReactionLocalActual_lorentzAdmissible,
      positiveDiracDualCartanReactionLocalActual_torsionSpinEquation,
      positiveDiracDualCartanReactionLocalActual_connection_selfGenerated,
      positiveDiracDualCartanReactionLocalActual_reaction_selfGenerated,
      positiveDiracDualCartanReactionLocalActual_auxiliaryEquation,
      positiveDiracDualCartanReactionLocalActual_multiplier_zero_four,
      positiveDiracDualCartanConnection_auxiliaryResidual_zero_four,
      positiveDiracDualCartanConnection_not_auxiliaryEquation,
      positiveDiracDualCartanReactionLocalActual_ne_connectionOnly⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanReactionLocalActualLiftRegression
