import H0mework.Versions.R2.Arithmetic.Goldbach.FirstResidualProvenanceFlux
import H0mework.Versions.R2.Arithmetic.FockResponsibility.OccurrenceHistory

/-!
# Goldbach provenance flux as an occurrence-sensitive recurrence

The existing first-residual projected loop drives both coordinates of the
state below.  Its full path produces the returned occurrence; the same path
erases every visited finite structural key.  When the source classifier emits
the first channel again at the returned split, the result is therefore the
occurrence responsibility's projection-recurrence residual, not an invented
second budget or an "already consumed occurrence" token.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFockOperationalProvenanceRecurrence

open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticGlobalGoldbachDisposition
open CanonicalUnitArithmeticOperationalFactorDecayProducer
open CanonicalUnitArithmeticOperationalFirstResidualConsumer
open CanonicalUnitArithmeticOperationalFirstResidualProducer
open CanonicalUnitArithmeticOperationalFirstResidualProvenanceFluxProducer
open CanonicalUnitArithmeticOperationalGoldbachRuntime
open ParticleWaveFockAtomicProcess
open ParticleWaveFockOccurrenceHistoryResponsibility
open ParticleWaveFockOccurrencePhysicalProcess
open ParticleWaveFockOccurrenceResponsibility
open SourceGeneratedFiniteEffectiveBranchingReachability
open SourceGeneratedFiniteEventIndexedProvenanceFlux
open SourceGeneratedFiniteEventIndexedResidualProcess

noncomputable section

noncomputable local instance structuralKeyDecidableEq (index : Nat) :
    DecidableEq (FactorDecayStructuralChannelKeyAt index) :=
  Classical.decEq _

private theorem append_events
    {P : SourceGeneratedFiniteEventIndexedResidualProcess.Process}
    {source middle target : P.State}
    (front : GeneratedPathAt P source middle)
    (back : GeneratedPathAt P middle target) :
    (SourceGeneratedFiniteEventIndexedProvenanceFlux.append front back).events =
      front.events ++ back.events := by
  induction back with
  | nil => simp [SourceGeneratedFiniteEventIndexedProvenanceFlux.append,
      GeneratedPathAt.events]
  | snoc prior event inductionHypothesis =>
      simp only [SourceGeneratedFiniteEventIndexedProvenanceFlux.append,
        GeneratedPathAt.events, inductionHypothesis, List.append_assoc]

def recurrentStructuralKey (failure : FirstResidualOccurrence) :
    FactorDecayStructuralChannelKeyAt failure.index :=
  ⟨fluxBase failure, fluxChannel failure⟩

theorem recurrentStructuralKey_visited
    (failure : FirstResidualOccurrence) :
    recurrentStructuralKey failure ∈ (projectedLoop failure).events := by
  rw [projectedLoop, append_events]
  apply List.mem_append_left
  simp [fluxFirstLeg, recurrentStructuralKey,
    GeneratedPathAt.oneStep, GeneratedPathAt.events]

/-- Exact returned occurrence and exact observer inventory obtained by
folding the same projected loop. -/
def returnedHistoryState (failure : FirstResidualOccurrence) :
    ParticleWaveFockOccurrenceResponsibility.State failure.index :=
  stateAfterPath (projectedLoop failure)

@[simp] theorem returnedHistoryState_occurrence_state
    (failure : FirstResidualOccurrence) :
    (returnedHistoryState failure).1.occurrence.state = fluxBase failure :=
  rfl

theorem returnedHistoryState_occurrence_eq_flux
    (failure : FirstResidualOccurrence) :
    (returnedHistoryState failure).1.occurrence =
      (provenanceFlux failure).returned := by
  exact (provenanceFlux failure).returned_eq.symm

theorem recurrentStructuralKey_absent
    (failure : FirstResidualOccurrence) :
    recurrentStructuralKey failure ∉ (returnedHistoryState failure).2 :=
  visitedKey_absent_from_stateAfterPath (projectedLoop failure)
    (recurrentStructuralKey failure)
    (recurrentStructuralKey_visited failure)

/-- The returned projected state is still classified by the same exact
source channel; only its full occurrence is newer. -/
def recurrentActualIncidence (failure : FirstResidualOccurrence) :
    ActualOccurrenceFactorDecayAt (returnedHistoryState failure).1 := by
  generalize dynamics_eq :
    generateDynamics (returnedHistoryState failure).1.physicalCurrent = dynamics
  cases dynamics with
  | terminal generated species =>
      have terminalClassifier := generated.classifier_eq
      change (fullFactorDecayLaw failure.index).classify (fluxBase failure) =
        .inl generated.terminal at terminalClassifier
      rw [fluxRepairClassifier_eq failure] at terminalClassifier
      cases terminalClassifier
  | step generated effect =>
      exact generateActualIncidence
        (returnedHistoryState failure).1 generated effect dynamics_eq

theorem recurrentActualIncidence_channel_eq
    (failure : FirstResidualOccurrence) :
    (recurrentActualIncidence failure).step.channel = fluxChannel failure := by
  have generatedClassifier :=
    (recurrentActualIncidence failure).step.classifier_eq
  change fullPhysicalFactorDecayClassify (fluxBase failure) =
    .inr (recurrentActualIncidence failure).step.selected at generatedClassifier
  have selectionEq := Sum.inr.inj
    (generatedClassifier.symm.trans (fluxPhysicalClassifier_eq failure))
  exact congrArg PhysicalProgressChannelAt.channel selectionEq

theorem recurrentActualIncidence_structuralKey_eq
    (failure : FirstResidualOccurrence) :
    (recurrentActualIncidence failure).structuralKey =
      recurrentStructuralKey failure := by
  rw [(recurrentActualIncidence failure).structuralKey_is_projection,
    recurrentActualIncidence_channel_eq]
  rfl

/-- Source-generated recurrence residual after the actual projected return.
The observer inventory is not refreshed. -/
def projectionRecurrenceResidual (failure : FirstResidualOccurrence) :
    ProjectionRecurrenceResidualAt (returnedHistoryState failure) := by
  let actual := recurrentActualIncidence failure
  exact ProjectionRecurrenceResidualAt.ofActual actual (by
    rw [recurrentActualIncidence_structuralKey_eq]
    exact recurrentStructuralKey_absent failure)

/-- The total occurrence-responsibility compiler is forced into its
projection-recurrence constructor on the path-generated returned state. -/
theorem generatedDisposition_is_projectionRecurrence
    (failure : FirstResidualOccurrence) :
    ∃ residual : ProjectionRecurrenceResidualAt (returnedHistoryState failure),
      ParticleWaveFockOccurrenceResponsibility.generateDisposition
          (returnedHistoryState failure) =
        .projectionRecurrence residual := by
  cases disposition_eq :
      ParticleWaveFockOccurrenceResponsibility.generateDisposition
        (returnedHistoryState failure) with
  | terminal settled =>
      have terminalClassifier := settled.generated.classifier_eq
      change (fullFactorDecayLaw failure.index).classify (fluxBase failure) =
        .inl settled.generated.terminal at terminalClassifier
      rw [fluxRepairClassifier_eq failure] at terminalClassifier
      cases terminalClassifier
  | payment paid =>
      have generatedClassifier := paid.actual.step.classifier_eq
      change fullPhysicalFactorDecayClassify (fluxBase failure) =
        .inr paid.actual.step.selected at generatedClassifier
      have selectionEq := Sum.inr.inj
        (generatedClassifier.symm.trans (fluxPhysicalClassifier_eq failure))
      have channel_eq : paid.actual.step.channel = fluxChannel failure :=
        congrArg PhysicalProgressChannelAt.channel selectionEq
      have key_eq : paid.structuralKey = recurrentStructuralKey failure := by
        rw [paid.structuralKey_eq,
          paid.actual.structuralKey_is_projection, channel_eq]
        rfl
      exact False.elim
        (recurrentStructuralKey_absent failure (key_eq ▸ paid.present))
  | projectionRecurrence residual => exact ⟨residual, rfl⟩

/-- Existing root provenance pointers and the path-generated recurrence are
one dependent package.  This does not yet install a new residual ledger row. -/
structure RootGeneratedOperationalProjectionRecurrenceAt
    (failure : FirstResidualOccurrence) : Type 7 where
  private mk ::
  flux : RootGeneratedOperationalFirstResidualProvenanceFluxAt failure
  flux_eq : flux = generate failure
  historyState : ParticleWaveFockOccurrenceResponsibility.State failure.index
  historyState_eq : historyState = returnedHistoryState failure
  occurrence_heq :
    HEq historyState.1.occurrence (provenanceFlux failure).returned
  recurrence : ProjectionRecurrenceResidualAt historyState
  recurrence_eq : HEq recurrence (projectionRecurrenceResidual failure)
  generatedDisposition :
    ∃ residual : ProjectionRecurrenceResidualAt historyState,
      ParticleWaveFockOccurrenceResponsibility.generateDisposition historyState =
        .projectionRecurrence residual
  sourceOccurrence :
    (runtimePayload (failureDepth failure)).sourceOccurrence =
      (runtimeAt (failureDepth failure)).emittedOccurrence
  wholeLedger :
    HEq (runtimeAt (failureDepth failure)).tick.generated.wholeLedgerWriteBack
      ((runtimeAt (failureDepth failure)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (runtimeAt (failureDepth failure)).current.visit.current)
  generatedNext :
    (runtimeAt (failureDepth failure)).tick.nextCurrent =
      runtimeFacade.process.stateAt
        (runtimeFacade.process.successor
          (runtimeAt (failureDepth failure)).state)

noncomputable def generateRooted
    (failure : FirstResidualOccurrence) :
    RootGeneratedOperationalProjectionRecurrenceAt failure :=
  { flux := generate failure
    flux_eq := rfl
    historyState := returnedHistoryState failure
    historyState_eq := rfl
    occurrence_heq := heq_of_eq
      (returnedHistoryState_occurrence_eq_flux failure)
    recurrence := projectionRecurrenceResidual failure
    recurrence_eq := HEq.rfl
    generatedDisposition :=
      generatedDisposition_is_projectionRecurrence failure
    sourceOccurrence := (generate failure).sourceOccurrence
    wholeLedger := (generate failure).wholeLedger
    generatedNext := (generate failure).generatedNext }

end

end ParticleWaveFockOperationalProvenanceRecurrence
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
