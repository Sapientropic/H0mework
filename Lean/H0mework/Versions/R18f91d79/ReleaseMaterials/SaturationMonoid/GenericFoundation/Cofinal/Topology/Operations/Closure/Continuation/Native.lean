import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Continuation.Payment
import H0mework.Realization.Operations.Execution.Relations.History.Append
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Relations.Consumer

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree

open SourceOperationEffects SourceOperationExecution SourceOperationPaidRelations SourceOperationCompletion
open CofinalHistorySettlement CofinalHistoryTransition

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
variable {S : Type u} {Value Var : S → Type u} [∀ s, AddCommGroup (Value s)] {sort : S}
variable (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
  Raw (Value := Value) (Var := Var) (sort := sort))
variable (runtime : Runtime old origin reader)

local notation "sourceState" => runtimeCurrent old origin reader runtime
local notation "nextStateAt" => runtimeCurrent old origin reader runtime.tick.next
local notation "sourceOccurrence" => RootedAccountedUnfolding.zero runtime.emittedOccurrence
local notation "nextOccurrence" => RootedAccountedUnfolding.zero runtime.tick.next.emittedOccurrence

/-- The actual paid update appends precisely the boundary between its two source endpoints. -/
theorem active_tick_terminal_relation (active : 0 < remaining sourceState.1) :
    words nextStateAt.2 = words sourceState.2 ++
      [Finsupp.single sourceState.1 1 - Finsupp.single nextStateAt.1 1] := by
  rw [tick_math old origin reader runtime]
  unfold nextState targetOf
  cases selected : action old origin reader sourceState with
  | inl settled =>
    have zero := (law old origin reader).settlement_budget_zero settled
    change remaining sourceState.1 = 0 at zero
    exact False.elim ((Nat.ne_of_gt active) zero)
  | inr generated =>
    rcases generated with ⟨target, write⟩
    cases write with
    | paid step => exact words_append sourceState.2 (Trace.single step)

theorem tick_paid_prefix : words sourceState.2 <+: words nextStateAt.2 := by
  by_cases active : 0 < remaining sourceState.1
  · exact ⟨_, (active_tick_terminal_relation old origin reader runtime active).symm⟩
  · rw [tick_math old origin reader runtime,
      Completion.next_state_of_zero old origin reader sourceState (Nat.eq_zero_of_not_pos active)]

/-- The installed relation face at this actual tick generates its canonical continuation. -/
def cofinalTickTransition : GeneratedTransition (Relations.history old origin reader runtime)
    (Relations.history old origin reader runtime.tick.next) :=
  continuationTransition sourceOccurrence nextOccurrence (tick_paid_prefix old origin reader runtime)

theorem cofinal_tick_completion (p : Nat.Primes) (value : (Relations.history old origin reader runtime).CompletionCarrier) :
    let mapped := continuationTransition sourceOccurrence nextOccurrence
      (interpreted_prefix p (tick_paid_prefix old origin reader runtime))
    completionEquiv nextOccurrence p nextStateAt.2
        ((cofinalTickTransition old origin reader runtime).completionMap _ _ value) =
      mapped.completionMap _ _ (completionEquiv sourceOccurrence p sourceState.2 value) :=
  continuation_completion sourceOccurrence nextOccurrence p (tick_paid_prefix old origin reader runtime) value

/-- The source occurrence that pays the fresh relation is the occurrence of the existing whole write. -/
theorem cofinal_tick_terminal_extension (active : 0 < remaining sourceState.1) :
    type_of% (continuation_terminal sourceOccurrence nextOccurrence
      (active_tick_terminal_relation old origin reader runtime active)) ∧
      type_of% (tick_ledger old origin reader runtime) :=
  ⟨continuation_terminal sourceOccurrence nextOccurrence
    (active_tick_terminal_relation old origin reader runtime active), tick_ledger old origin reader runtime⟩

end RootGeneratedDebtActivationJointSource.OwnerFree
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
