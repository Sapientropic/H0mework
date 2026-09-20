import H0mework.Realization.SourceComparison.RawSource
import H0mework.Foundation.Cofinal.ProductiveHistory

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RawGeneratedRoot

universe u v
variable (D : Dynamics.{u})

/-- The entire raw event fibre, including events other than the actual emitter. -/
def eventPresentation (state : D.State) :
    ConstructivePresentation (D.EventAt state)
      ((root D).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt state) where
  forward := fun event => ⟨state, ⟨event, rfl⟩⟩
  backward := fun occurrence => occurrence.2.event
  backward_forward := fun _ => rfl
  forward_backward := by
    rintro ⟨support, event, same⟩
    cases same
    rfl

def generatedSuccessor {state : D.State} (event : D.EventAt state) :
    SourceNativeLedgerGeneratedSuccessorAt ((eventPresentation D state).forward event)
      ((ledgerCompiler D).compile ((eventPresentation D state).forward event)) :=
  PUnit.unit

theorem generated_target {state : D.State} (event : D.EventAt state) :
    (generatedSuccessor D event).targetCurrent = D.update event := rfl

theorem generated_emitter {state : D.State} (event : D.EventAt state) :
    (generatedSuccessor D event).targetOccurrence = emitted D (D.update event) := rfl

theorem generated_ledger {state : D.State} (event : D.EventAt state) :
    (generatedSuccessor D event).ledgerEvolution.destination (entry D state) =
      ⟨entry D (D.update event), .transferred event rfl rfl (Nat.le_refl _)⟩ := rfl

theorem observed_event (state : D.State) (event : D.EventAt state) :
    (projectionLaw D).project PUnit.unit ((eventPresentation D state).forward event) PUnit.unit =
      (⟨state, event⟩ : Sigma D.EventAt) := rfl

theorem every_dependent_consumer {state : D.State} (event : D.EventAt state)
    {Result : D.EventAt state → Sort v} (consume : (value : D.EventAt state) → Result value) :
    HEq (consume ((eventPresentation D state).backward ((eventPresentation D state).forward event)))
      (consume event) := HEq.rfl

def currentAt (index : Nat) : D.State :=
  Nat.rec D.initial (fun _ state => D.update (D.emit state)) index

def history : ProductiveFiniteRootHistoryAt (root D).toAuthoritativeRoot.toLedgerRoot where
  currentAt := currentAt D
  initial_eq := rfl
  next_eq := fun _ => rfl

def visitAt (index : Nat) : GroundedFaithfulRealization.Visit (root D) :=
  .finite ((history D).visitAt index)

theorem visit_current (index : Nat) : (visitAt D index).current = currentAt D index :=
  (history D).visitAt_current index

theorem raw_history_unique
    (other : ProductiveFiniteRootHistoryAt (root D).toAuthoritativeRoot.toLedgerRoot)
    (index : Nat) : other.currentAt index = currentAt D index :=
  other.currentAt_eq (history D) index

theorem next_current (visit : GroundedFaithfulRealization.Visit (root D)) :
    (root D).generatedNextCurrentAt visit =
      ⟨vocabulary D, (root D).toAuthoritativeRoot,
        visit.next (next := D.update (D.emit visit.current)) rfl⟩ :=
  (root D).generatedNextCurrentAt_eq_nativeWriteBranch visit (D.emit visit.current) rfl
    (emitted D (D.update (D.emit visit.current)))
    (patch D (emitted D visit.current)).toLedgerWriteEvolution rfl rfl

/-- Every raw generator receives a full-fibre representation with its actual
update, row transfer, and unique faithful execution. No root or realization
certificate is an input. -/
theorem every_raw_dynamics_realized :
    (∀ state, (eventPresentation D state).forward (D.emit state) = (root D).emitted state) ∧
    (∀ state event,
      (eventPresentation D state).backward ((eventPresentation D state).forward event) = event ∧
      (generatedSuccessor D event).targetCurrent = D.update event ∧
      (generatedSuccessor D event).ledgerEvolution.destination (entry D state) =
        ⟨entry D (D.update event), .transferred event rfl rfl (Nat.le_refl _)⟩) ∧
    (∀ state occurrence,
      (eventPresentation D state).forward ((eventPresentation D state).backward occurrence) = occurrence) ∧
    (∀ index, (visitAt D index).current = currentAt D index) ∧
    (∀ visit : GroundedFaithfulRealization.Visit (root D),
      (root D).generatedNextCurrentAt visit =
        ⟨vocabulary D, (root D).toAuthoritativeRoot,
          visit.next (next := D.update (D.emit visit.current)) rfl⟩) ∧
    TotalReality.TotalRealityAt (RootTotalReality.semantics (root D).toAuthoritativeRoot) ∧
    (∀ (other : CausalCore.Process (root D).toAnswerNextCausalWorld)
        (_faithful : CausalCore.FaithfulRealization (root D).toAnswerNextCausalWorld other),
      ∃ comparison : CausalCore.ProcessCommutingPresentation (realization D).1 other,
        ∀ candidate : CausalCore.ProcessCommutingPresentation (realization D).1 other,
        ∀ current event, (candidate.eventPresentation current).toFun event =
          (comparison.eventPresentation current).toFun event) := by
  refine ⟨fun _ => rfl, fun _ event => ⟨rfl, generated_target D event, generated_ledger D event⟩,
    fun state => (eventPresentation D state).forward_backward,
    visit_current D, next_current D, RootTotalReality.isTotal _, ?_⟩
  intro other faithful
  exact GroundedFaithfulRealization.source_generates_unique_comparison (realization D).2 faithful

end RawGeneratedRoot
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
