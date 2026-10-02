import H0mework.Versions.R2.Realization.Completion.HistoryInstallation

/-!
# Determinant disposition from a source-complete history

The history settlement computes whether a complete cofinal presented carrier
reaches a finite residual-zero stage.  Only on that generated compact branch
does the existing perfect-complex kernel derive a finite-free two-term
presentation, determinant line, and intrinsic unit torsor.  Otherwise the
history residual-coordinate kernel emits the explicit representation
coordinate.

This face joins those downstream readouts without adding a finite,
perfect, determinant, or unit premise.  It is the generic base contract
needed by domain consumers: every source-complete carrier receives a total
disposition, while finite determinant eligibility is earned by a
source-generated bounded branch.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalHistoryDeterminantDisposition

open CofinalHistorySettlement
open CofinalHistorySettlement.RootGeneratedCofinalHistoryAt
open CofinalHistorySettlementFace
open CofinalHistorySettlementFace.RootGeneratedCofinalHistorySettlementStepAt
open CofinalHistoryResidualCoordinate
open PerfectComplexDeterminantProjection

noncomputable section

universe u w

variable {Root : Type w} {Generator : Type u}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {seedOccurrence : RootedAccountedUnfolding
  (PresentedRelationEventAt Generator)}
variable {continuationOccurrence : RootedAccountedUnfolding
  (PresentedRelationEventAt Generator →
    RootedAccountedUnfolding (PresentedRelationEventAt Generator))}

/-! ## Total source-generated disposition -/

inductive DeterminantDispositionOutcome
    (history : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence) : Type (max u w + 1) where
  | determinant
      (trace : GeneratedHistoricalCompactnessAt history)
      (readout : GeneratedCompactPerfectReadoutAt history trace)
      (calculation : RootGeneratedFourTermPerfectCalculationAt
        readout.determinantProjection)
      (state : RootGeneratedFourTermPerfectDeterminantStateAt
        readout.determinantProjection calculation)
  | residual
      (coordinate : GeneratedPresentedResidualCoordinateAt history)

noncomputable def settleWithDeterminant
    (history : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence) :
    DeterminantDispositionOutcome history := by
  cases history.settle with
  | inl positive =>
      rcases positive with ⟨trace, readout⟩
      exact .determinant trace readout readout.perfectCalculation
        readout.determinantState
  | inr obstruction =>
      exact .residual (persistentCoordinate obstruction)

theorem disposition_is_total
    (history : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence) :
    Nonempty (DeterminantDispositionOutcome history) :=
  ⟨settleWithDeterminant history⟩

theorem residual_coordinate_of_persistent
    (history : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence)
    (persistent : ∀ stage, ¬ history.CompactAt stage) :
    ∃ coordinate : GeneratedPresentedResidualCoordinateAt history,
      coordinate.coordinate ≠ 0 ∧
      coordinate.representative ∉
        LinearMap.range
          (history.stagePresentedToCompletion coordinate.stage) := by
  obtain ⟨obstruction⟩ := history.persistentObstruction_exists persistent
  let coordinate := persistentCoordinate obstruction
  exact ⟨coordinate, coordinate.coordinate_ne_zero,
    coordinate.representative_outside_source_range⟩

/-! ## Exact root-facing alias -/

namespace RootGeneratedCofinalHistorySettlementStepAt

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {root : SourceNativeLivingRootClosure N V}
variable {recognition : SourceNativeCofinalHistoryRecognitionAt root}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}

abbrev DeterminantDispositionOutcome
    (step : RootGeneratedCofinalHistorySettlementStepAt
      recognition visit) :=
  CofinalHistoryDeterminantDisposition.DeterminantDispositionOutcome step.history

def determinantDisposition
    (step : RootGeneratedCofinalHistorySettlementStepAt
      recognition visit) :
    CofinalHistoryDeterminantDisposition.DeterminantDispositionOutcome step.history :=
  CofinalHistoryDeterminantDisposition.settleWithDeterminant step.history

theorem determinantDisposition_is_total
    (step : RootGeneratedCofinalHistorySettlementStepAt
      recognition visit) :
    Nonempty
      (CofinalHistoryDeterminantDisposition.DeterminantDispositionOutcome step.history) :=
  ⟨determinantDisposition step⟩

end RootGeneratedCofinalHistorySettlementStepAt

end
end CofinalHistoryDeterminantDisposition
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
