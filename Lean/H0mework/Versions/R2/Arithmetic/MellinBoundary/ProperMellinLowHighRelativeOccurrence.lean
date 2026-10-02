import H0mework.Versions.R2.Arithmetic.MellinBoundary.StageZeroLowHighResidualNoGo
import H0mework.Foundation.Source.AdditiveTraceFold

/-!
# Same-zero proper Mellin low/high relative occurrence

The relative face is generated directly from the existing analytic
occurrence and projects to `zeroObservationReadoutOccurrence`.  Its dependent
payload stores only the transported nontriviality proof; selected low,
J-generated high, reversal low, and the explicit residual are canonical
readouts of that proof-indexed face.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex MeasureTheory Set
open QRich
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open RootedAccountedUnfolding

noncomputable section

/-- Minimal dependent carrier.  An arbitrary historical zero payload cannot
be assigned nontriviality; the private face is generated only while mapping
the source analytic occurrence together with the fixed observation proof. -/
structure ProperMellinLowHighRelativeFaceAt
    (zero : GeneratedZeroObservationPayload) : Type where
  private mk ::
  nontrivial :
    ¬ ∃ n : Nat, zero.2.coordinate = -2 * (n + 1)

namespace ProperMellinLowHighRelativeFaceAt

def generate
    (zero : GeneratedZeroObservationPayload)
    (nontrivial :
      ¬ ∃ n : Nat, zero.2.coordinate = -2 * (n + 1)) :
    ProperMellinLowHighRelativeFaceAt zero :=
  ⟨nontrivial⟩

def selectedLow
    {zero : GeneratedZeroObservationPayload}
    (face : ProperMellinLowHighRelativeFaceAt zero) : PositiveMellinL1 :=
  selectedStageZeroProperMellinL1 zero.2 face.nontrivial

def generatedHigh
    {zero : GeneratedZeroObservationPayload}
    (face : ProperMellinLowHighRelativeFaceAt zero) : PositiveMellinL1 :=
  positiveMellinL1StarInversion face.selectedLow

def reversalLow
    {zero : GeneratedZeroObservationPayload}
    (face : ProperMellinLowHighRelativeFaceAt zero) : PositiveMellinL1 :=
  reversalStageZeroProperMellinL1 zero.2 face.nontrivial

def residual
    {zero : GeneratedZeroObservationPayload}
    (face : ProperMellinLowHighRelativeFaceAt zero) : PositiveMellinL1 :=
  face.generatedHigh - face.reversalLow

@[simp] theorem generatedHigh_eq
    {zero : GeneratedZeroObservationPayload}
    (face : ProperMellinLowHighRelativeFaceAt zero) :
    face.generatedHigh = positiveMellinL1StarInversion face.selectedLow :=
  rfl

@[simp] theorem residual_eq
    {zero : GeneratedZeroObservationPayload}
    (face : ProperMellinLowHighRelativeFaceAt zero) :
    face.residual =
      positiveMellinL1StageZeroStarInversionResidual
        zero.2 face.nontrivial :=
  rfl

theorem residual_ne_zero
    {zero : GeneratedZeroObservationPayload}
    (face : ProperMellinLowHighRelativeFaceAt zero) :
    face.residual ≠ 0 := by
  rw [residual_eq]
  exact positiveMellinL1StageZeroStarInversionResidual_ne_zero
    zero.2 face.nontrivial

theorem residual_coordinate
    {zero : GeneratedZeroObservationPayload}
    (face : ProperMellinLowHighRelativeFaceAt zero) :
    (∫ t : ℝ in stageZeroLowWindow, (face.residual : ℝ → ℂ) t) =
      -(blockQRichSuccessorScale 0 : ℂ) ^
        (-(coordinateReversal zero.2.coordinate / 2)) := by
  rw [residual_eq]
  exact positiveMellinL1StageZeroStarInversionResidual_coordinate
    zero.2 face.nontrivial

end ProperMellinLowHighRelativeFaceAt

abbrev ProperMellinLowHighRelativePayload :=
  Σ zero : GeneratedZeroObservationPayload,
    ProperMellinLowHighRelativeFaceAt zero

def zeroOwnedProperMellinLowHighRelativeOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    RootedAccountedUnfolding ProperMellinLowHighRelativePayload :=
  generatedRiemannAnalyticContinuationOccurrence.map fun analytic =>
    let zero : GeneratedZeroObservationPayload :=
      ⟨analytic, observation.transport analytic.1⟩
    let transportedNontrivial :
        ¬ ∃ n : Nat, zero.2.coordinate = -2 * (n + 1) := by
      rintro ⟨n, equality⟩
      apply nontrivial
      refine ⟨n, ?_⟩
      change observation.coordinate = -2 * (n + 1) at equality
      exact equality
    ⟨zero, ProperMellinLowHighRelativeFaceAt.generate
      zero transportedNontrivial⟩

theorem zeroOwnedProperMellinLowHighRelativeOccurrence_projects
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (zeroOwnedProperMellinLowHighRelativeOccurrence
        observation nontrivial).map Sigma.fst =
      zeroObservationReadoutOccurrence observation := by
  rw [zeroOwnedProperMellinLowHighRelativeOccurrence,
    zeroObservationReadoutOccurrence,
    RootedAccountedUnfolding.map_map]
  rfl

@[simp] theorem zeroOwnedProperMellinLowHighRelativeOccurrence_root_coordinate
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (zeroOwnedProperMellinLowHighRelativeOccurrence
      observation nontrivial).root.1.2.coordinate =
        observation.coordinate :=
  rfl

theorem zeroOwnedProperMellinLowHighRelativeOccurrence_root_residual_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (zeroOwnedProperMellinLowHighRelativeOccurrence
      observation nontrivial).root.2.residual =
        positiveMellinL1StageZeroStarInversionResidual
          (zeroObservationReadoutOccurrence observation).root.2
          (zeroOwnedProperMellinLowHighRelativeOccurrence
            observation nontrivial).root.2.nontrivial := by
  rfl

theorem zeroOwnedProperMellinLowHighRelativeOccurrence_root_four_face_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    let face := (zeroOwnedProperMellinLowHighRelativeOccurrence
      observation nontrivial).root.2
    face.generatedHigh = positiveMellinL1StarInversion face.selectedLow ∧
      face.residual = face.generatedHigh - face.reversalLow ∧
      face.residual ≠ 0 := by
  dsimp only
  exact ⟨rfl, rfl,
    (zeroOwnedProperMellinLowHighRelativeOccurrence
      observation nontrivial).root.2.residual_ne_zero⟩

theorem zeroOwnedProperMellinLowHighRelativeOccurrence_root_residual_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (zeroOwnedProperMellinLowHighRelativeOccurrence
      observation nontrivial).root.2.residual ≠ 0 :=
  (zeroOwnedProperMellinLowHighRelativeOccurrence
    observation nontrivial).root.2.residual_ne_zero

theorem zeroOwnedProperMellinLowHighRelativeOccurrence_root_residual_coordinate
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (∫ t : ℝ in stageZeroLowWindow,
        ((zeroOwnedProperMellinLowHighRelativeOccurrence
          observation nontrivial).root.2.residual : ℝ → ℂ) t) =
      -(blockQRichSuccessorScale 0 : ℂ) ^
        (-(coordinateReversal observation.coordinate / 2)) := by
  simpa using
    (zeroOwnedProperMellinLowHighRelativeOccurrence
      observation nontrivial).root.2.residual_coordinate

def properMellinLowHighResidualWeight
    (payload : ProperMellinLowHighRelativePayload) : PositiveMellinL1 :=
  payload.2.residual

def properMellinLowHighResidualTraceReadout
    (occurrence :
      RootedAccountedUnfolding ProperMellinLowHighRelativePayload) :
    PositiveMellinL1 :=
  RootedAccountedUnfolding.traceSum
    properMellinLowHighResidualWeight occurrence

/-- The complete relative residual readout is the unique fold of the same
rooted occurrence; no second evaluator or root is introduced. -/
theorem properMellinLowHighResidualTraceReadout_eq_fold
    (occurrence :
      RootedAccountedUnfolding ProperMellinLowHighRelativePayload) :
    properMellinLowHighResidualTraceReadout occurrence =
      occurrence.fold (RootedAccountedUnfolding.additiveFoldAlgebra
        properMellinLowHighResidualWeight) :=
  RootedAccountedUnfolding.traceSum_eq_fold
    properMellinLowHighResidualWeight occurrence

theorem zeroOwnedProperMellinLowHighRelativeOccurrence_fold_unique_consumer
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    properMellinLowHighResidualTraceReadout
        (zeroOwnedProperMellinLowHighRelativeOccurrence
          observation nontrivial) =
      (zeroOwnedProperMellinLowHighRelativeOccurrence
        observation nontrivial).fold
        (RootedAccountedUnfolding.additiveFoldAlgebra
          properMellinLowHighResidualWeight) :=
  properMellinLowHighResidualTraceReadout_eq_fold _

end
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
