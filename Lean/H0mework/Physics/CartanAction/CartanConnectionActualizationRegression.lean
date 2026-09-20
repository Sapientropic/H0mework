import H0mework.Physics.CartanAction.CartanConnectionActualization
import H0mework.Physics.DualVariation.SpinTorsionAcceptance
import H0mework.Physics.Dirac.GeneratedMatterSpinActionUpdate

/-!
# Regressions for the repaired-action Cartan connection producer

The positive source already generates the P506/L0 matter actual and the exact
Lorentz matter coefficient `1/2`.  The repaired physical-current convention
therefore generates W13 evaluation `-1/2`; KIN-3/KIN-2/KIN-4 install it as a
non-Levi--Civita Lorentz connection whose literal Cartan response is the same
internally generated current.

The negative control retains the same source, coframe jet, point, and matter
actual but discards the generated contorsion.  Its pure Levi--Civita response
is zero and cannot reproduce the nonzero action current.  Thus the control
tests the producer seam rather than changing an ansatz coefficient or target.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanConnectionActualizationRegression

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineCartanAffineConnectionActualization
open StageNineCartanTorsionThreeFormCoordinates
open StageNineCartanTorsionThreeFormEquiv
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeSpinTorsionAcceptance
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLorentzActionCanonicalPairUpdate
open StageNineLorentzConnectionVariation
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceGeneratedMatterSpinActionUpdate
open StageNineTopologicalLorentzThreeFormDuality

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

def fixedSpinDirection : LorentzBivectorOneForm :=
  canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1)

def fixedActionSpinResponse : PhysicalBivectorThreeForm :=
  diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
    positiveSourceTargetMatterActual 0

def fixedCoframeJet : PointwiseLorentzianCoframeJet :=
  holonomicCoframeFirstJetAt positiveSourceTargetMatterActual.coframe 0

def fixedActionCartanConnection : PointwiseLorentzSpinConnection :=
  diracDualFormNativeActionCartanConnectionAt positiveSmoothUnifiedSource
    positiveSourceTargetMatterActual 0

/-- Independent sign/readout lock: the source-produced coefficient `+1/2`
becomes the physical W13 current `-1/2`. -/
theorem fixedActionSpinResponse_evaluation_eq_neg_half :
    lorentzThreeFormWedgeContinuousDual fixedActionSpinResponse
        fixedSpinDirection = -(1 / 2 : ℝ) := by
  rw [fixedActionSpinResponse, fixedSpinDirection,
    diracDualFormNativeActionSpinResponseAt_evaluation]
  rw [formNativeLorentzMatterFirstCoefficient_restrictToIIPlus]
  rw [←
    lorentzMatterSpinSourceCoefficient_eq_formNativeLorentzMatterFirstCoefficient]
  rw [positiveSourceTargetMatterActual_matterSpin_eq_half]

theorem fixedActionSpinResponse_ne_zero : fixedActionSpinResponse ≠ 0 := by
  intro responseZero
  have evaluationZero := congrArg
    (fun response : PhysicalBivectorThreeForm =>
      lorentzThreeFormWedgeContinuousDual response fixedSpinDirection)
    responseZero
  rw [fixedActionSpinResponse_evaluation_eq_neg_half] at evaluationZero
  simp [lorentzThreeFormWedgeContinuousDual_apply,
    lorentzOneFormThreeFormWedgeCoefficient] at evaluationZero

/-- Positive producer regression on the exact source-owned P506/L0 matter
actual. -/
theorem fixedActionCartanConnection_generates_spinResponse :
    cartanTorsionThreeForm
        (positiveSourceTargetMatterActual.coframe 0)
        (actualPointwiseCartanTorsionTwoForm fixedCoframeJet
          fixedActionCartanConnection) =
      fixedActionSpinResponse := by
  exact diracDualFormNativeActionCartanConnectionAt_generates_spinResponse
    positiveSmoothUnifiedSource positiveSourceTargetMatterActual 0
    (positiveSourceTargetMatterActual_nondegenerate 0)

theorem fixedLeviCivitaCartanResponse_eq_zero :
    cartanTorsionThreeForm
        (positiveSourceTargetMatterActual.coframe 0)
        (actualPointwiseCartanTorsionTwoForm fixedCoframeJet
          fixedCoframeJet.lorentzSpinConnection) = 0 := by
  rw [actualPointwiseCartanTorsionTwoForm_lorentzSpinConnection_eq_zero
    fixedCoframeJet (positiveSourceTargetMatterActual_nondegenerate 0)]
  exact (cartanTorsionThreeForm_eq_zero_iff
    (positiveSourceTargetMatterActual.coframe 0)
    (positiveSourceTargetMatterActual_nondegenerate 0) 0).2 rfl

/-- Same-source negative control: the pure Levi--Civita lookalike cannot absorb
the nonzero matter spin response. -/
theorem fixedLeviCivita_rejects_actionSpinResponse :
    cartanTorsionThreeForm
        (positiveSourceTargetMatterActual.coframe 0)
        (actualPointwiseCartanTorsionTwoForm fixedCoframeJet
          fixedCoframeJet.lorentzSpinConnection) ≠
      fixedActionSpinResponse := by
  rw [fixedLeviCivitaCartanResponse_eq_zero]
  exact Ne.symm fixedActionSpinResponse_ne_zero

theorem fixedActionCartanConnection_ne_leviCivita :
    fixedActionCartanConnection ≠ fixedCoframeJet.lorentzSpinConnection := by
  intro connectionEquality
  have generated := fixedActionCartanConnection_generates_spinResponse
  rw [connectionEquality, fixedLeviCivitaCartanResponse_eq_zero] at generated
  exact fixedActionSpinResponse_ne_zero generated.symm

/-- Bundled checkpoint: lineage and the prior action-owned actual remain
outputs, while the new connection is certified by positive and negative
literal Cartan response tests. -/
theorem fixedActionCartanConnection_directRegression :
    PositiveSourceGeneratedMatterSpinActionUpdateLaw
        positiveSourceTargetMatterActual ∧
      positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
        canonicalP506SourceAffineL0ObservableLineageReference ∧
      lorentzThreeFormWedgeContinuousDual fixedActionSpinResponse
          fixedSpinDirection = -(1 / 2 : ℝ) ∧
      fixedActionSpinResponse ≠ 0 ∧
      cartanTorsionThreeForm
          (positiveSourceTargetMatterActual.coframe 0)
          (actualPointwiseCartanTorsionTwoForm fixedCoframeJet
            fixedActionCartanConnection) =
        fixedActionSpinResponse ∧
      cartanTorsionThreeForm
          (positiveSourceTargetMatterActual.coframe 0)
          (actualPointwiseCartanTorsionTwoForm fixedCoframeJet
            fixedCoframeJet.lorentzSpinConnection) ≠
        fixedActionSpinResponse ∧
      fixedActionCartanConnection ≠ fixedCoframeJet.lorentzSpinConnection := by
  exact
    ⟨positiveSourceGeneratedMatterSpinActionUpdate_realizes_C3h107,
      positiveSmoothUnifiedSource_generates_exactP506L0Lineage,
      fixedActionSpinResponse_evaluation_eq_neg_half,
      fixedActionSpinResponse_ne_zero,
      fixedActionCartanConnection_generates_spinResponse,
      fixedLeviCivita_rejects_actionSpinResponse,
      fixedActionCartanConnection_ne_leviCivita⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanConnectionActualizationRegression
