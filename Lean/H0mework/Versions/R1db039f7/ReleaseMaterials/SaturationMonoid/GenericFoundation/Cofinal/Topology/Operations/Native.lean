import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Trace
import H0mework.Realization.Operations.Execution.Relations.History.Append
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Completion

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree

open SourceOperationEffects SourceOperationExecution SourceOperationPaidRelations

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
  Raw (Value := Value) (Var := Var) (sort := sort))

/-- The original active payment appends its own relation word, both before and after interpretation. -/
theorem cofinal_active_tick_words (runtime : Runtime old origin reader) (p : Nat.Primes)
    (active : 0 < remaining (runtimeCurrent old origin reader runtime).1) :
    let prior := (runtimeCurrent old origin reader runtime).2
    let next := (runtimeCurrent old origin reader runtime.tick.next).2
    ∃ word, words next = words prior ++ [word] ∧
      words (SourceOperationCompletion.trace p next) =
        words (SourceOperationCompletion.trace p prior) ++ [SourceOperationCompletion.wordMap p sort word] := by
  have written : ∃ word, words (runtimeCurrent old origin reader runtime.tick.next).2 =
      words (runtimeCurrent old origin reader runtime).2 ++ [word] := by
    rw [tick_math old origin reader runtime]
    unfold nextState targetOf
    cases selected : action old origin reader (runtimeCurrent old origin reader runtime) with
    | inl settled =>
      have zero := (law old origin reader).settlement_budget_zero settled
      change remaining (runtimeCurrent old origin reader runtime).1 = 0 at zero
      exact False.elim ((Nat.ne_of_gt active) zero)
    | inr paid =>
      rcases paid with ⟨target, advance⟩
      cases advance with
      | paid step =>
        dsimp only [SourceOperationExecutionDebt.advance]
        exact ⟨_, words_append _ (Trace.single step)⟩
  obtain ⟨word, written⟩ := written
  refine ⟨word, written, ?_⟩
  simp only [SourceOperationCompletion.trace_words, written, List.map_append, List.map_cons, List.map_nil]

end RootGeneratedDebtActivationJointSource.OwnerFree
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
