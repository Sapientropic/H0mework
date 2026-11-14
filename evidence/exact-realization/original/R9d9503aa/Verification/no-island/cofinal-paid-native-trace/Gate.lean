import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Native.TopologyTrace
import SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.CofinalBilinear

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CP745Independent

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationPaidRelations
open SourceOperationCompletion

section Trace
variable {S : Type u} {V X : S → Type u} [∀ s, AddCommGroup (V s)] {s : S}

private def original_expression_retains_value_effect_and_remaining
    (p : Nat.Primes) (term : Expr V X s) (old increment : Env V X) :=
  And.intro (expression_eval p term old) <|
    And.intro (expression_effect p term old increment) (expression_remaining p term)

private def actual_paid_trace_preserves_ordered_slots_and_length
    (p : Nat.Primes) {old : Env V X} {before after : Expr V X s}
    (paid : Trace old before after) (i : Fin (words paid).length) :=
  And.intro (trace_length p paid) <|
    And.intro (trace_words p paid) (trace_word_at p paid i)

private def each_original_formal_word_has_the_same_full_old_effect_pair
    (p : Nat.Primes) (old increment : Env V X) (word : Formal ℤ V X s) :=
  SourceOperationCompletion.inventory_read p old increment word

end Trace

private theorem a_single_appended_paid_word_changes_length {A : Type u} {before after : List A}
    {word : A} (paid : after = before ++ [word]) : after ≠ before := by
  intro erased
  have length := congrArg List.length (erased.symm.trans paid)
  simp only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add] at length
  omega

end CP745Independent

namespace RootGeneratedDebtActivationJointSource.OwnerFree.CP745Independent

open SourceOperationEffects SourceOperationExecution SourceOperationPaidRelations

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
  Raw (Value := Value) (Var := Var) (sort := sort))

private def the_original_active_tick_appends_one_word_in_both_views
    (runtime : Runtime old origin reader) (p : Nat.Primes)
    (active : 0 < remaining (runtimeCurrent old origin reader runtime).1) :=
  cofinal_active_tick_words old origin reader runtime p active

private theorem erasing_the_real_active_payment_changes_the_original_and_completed_trace
    (runtime : Runtime old origin reader) (p : Nat.Primes)
    (active : 0 < remaining (runtimeCurrent old origin reader runtime).1) :
    let prior := (runtimeCurrent old origin reader runtime).2
    let next := (runtimeCurrent old origin reader runtime.tick.next).2
    words next ≠ words prior ∧
      words (SourceOperationCompletion.trace p next) ≠ words (SourceOperationCompletion.trace p prior) := by
  obtain ⟨_,written,completed⟩ := cofinal_active_tick_words old origin reader runtime p active
  exact ⟨ConstructiveRoot.CP745Independent.a_single_appended_paid_word_changes_length written,
    ConstructiveRoot.CP745Independent.a_single_appended_paid_word_changes_length completed⟩

end RootGeneratedDebtActivationJointSource.OwnerFree.CP745Independent
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

namespace CanonicalUnitArithmeticRoot.CP745Independent

private def the_separate_native_runtime_keeps_sibling_and_dependent_whole
    (runtime : LivingRuntimeState runtimeFacade.process) (p : Nat.Primes) :=
  actual_native_bilinear_completion runtime p

end CanonicalUnitArithmeticRoot.CP745Independent

namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyTrace.CP745Independent

open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source

private def the_fixed_target_paid_tick_appends_and_reads_the_same_complete_word
    (depth count : Nat) (within : count < sourceFuel (R.source depth (emitted depth))) (p : Nat.Primes) :=
  actual_actor_cofinal_paid_tick depth count within p

private def the_fixed_target_terminal_consumes_the_original_receipt_and_disposition
    (depth : Nat) (p : Nat.Primes) :=
  actual_actor_cofinal_terminal depth p

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.TopologyTrace.CP745Independent

#eval IO.println "CP745_CONTROL + original_expression_retains_value_effect_and_remaining"
#eval IO.println "CP745_CONTROL + actual_paid_trace_preserves_ordered_slots_and_length"
#eval IO.println "CP745_CONTROL + each_original_formal_word_has_the_same_full_old_effect_pair"
#eval IO.println "CP745_CONTROL + fixed_target_paid_tick_terminal_and_separate_native_whole"
#eval IO.println "CP745_CONTROL - erasing_the_real_active_payment_changes_the_original_and_completed_trace"
#eval IO.println "CP745_GATE_PASS positive=4 negative=1"

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
