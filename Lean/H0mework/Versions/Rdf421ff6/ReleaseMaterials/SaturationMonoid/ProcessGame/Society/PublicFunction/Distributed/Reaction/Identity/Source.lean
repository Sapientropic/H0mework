import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Identity.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Identity

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (seed : Machine Party Good Port Technology Instrument) (feasible : seed.code.feasible seed.reference)

abbrev reference : Program seed.code := ⟨seed.reference, seed.reference_generated⟩
abbrev history : OriginalHistory seed.code := ⟨seed.history, seed.original⟩
abbrev table := restrict seed.code seed.opponent

def selection : Selection seed.code (reference seed) :=
  match compile seed.code (reference seed) with
  | .selected chosen => chosen
  | .blocked rejected => False.elim (feasible_original_cannot_be_blocked seed.code (reference seed) feasible rejected)

def original := machine seed.code (reference seed) (history seed) (table seed)
def replacement := machine seed.code (selection seed feasible).policy.policy (history seed) (table seed)

/-- The same joint restriction is used by both roots. The physical response
is exactly the response to the original history-adaptive opponent. -/
theorem canonical_source_emits_the_original_opponent_response (program : Program seed.code) :
    ((machine seed.code program (history seed) (table seed)).actualExecution seed.history.length).submitted =
      (execution seed.code program.val seed.history seed.opponent).word := by
  have actual := (machine seed.code program (history seed) (table seed)).actual_reaction_word_and_next program.val rfl
  have same := one_restriction_preserves_every_continuation seed.code program.val program.property
    seed.history seed.original seed.opponent seed.code.eventLimit [] (by simp) (by simp)
  change trace seed.code program.val seed.history (respond seed.code (table seed)) =
    trace seed.code program.val seed.history seed.opponent at same
  have word : ((machine seed.code program (history seed) (table seed)).actualExecution seed.history.length).submitted =
      (execution seed.code program.val seed.history (respond seed.code (table seed))).word := actual.1
  exact word.trans (by simp only [execution, same])

theorem actual_native_profiles_are_equal :
    profile seed.code (selection seed feasible).policy.policy (history seed) (table seed) =
      profile seed.code (reference seed) (history seed) (table seed) :=
  ((comparison_iff seed.code _ _).mp (selection seed feasible).policy.no_regression).2 _ _
    (restriction_is_generated seed.code seed.opponent)

theorem every_original_debt_has_its_actual_native_counterpart :
    ∀ index (inside : index < (Native.generate (original seed) seed.history.length).finance.current.slots.length),
      ∃ new ∈ (Native.generate (replacement seed feasible) seed.history.length).finance.current.slots,
        DebtCorrespondence seed.code (original seed).input (replacement seed feasible).input
          (Native.generate (original seed) seed.history.length).finance.current.slots[index] new :=
  equal_images_recover_each_original_native_debt seed.code (original seed).input (replacement seed feasible).input _ _
    (congrArg Profile.debts (actual_native_profiles_are_equal seed feasible))

theorem actual_full_carrier_extension :
    (∀ party good, 0 ≤ Open.reserve seed.code (selection seed feasible).policy.policy.val
      seed.reference seed.history (respond seed.code (table seed)) party good) ∧
      ((replacement seed feasible).actualExecution seed.history.length).after =
        ((original seed).actualExecution seed.history.length).after.addReserve
          (Open.reserve seed.code (selection seed feasible).policy.policy.val seed.reference seed.history (respond seed.code (table seed))) := by
  have checked := ((comparison_iff seed.code _ _).mp (selection seed feasible).policy.no_regression).1
  have generated := Open.generated_full_carrier_extension seed.code _ _
    (selection seed feasible).policy.policy.property seed.reference_generated checked
    (respond seed.code (table seed)) seed.history seed.original
  have new := (replacement seed feasible).actual_reaction_word_and_next (selection seed feasible).policy.policy.val rfl
  have old := (original seed).actual_reaction_word_and_next seed.reference rfl
  have newAfter : ((replacement seed feasible).actualExecution seed.history.length).after =
      Open.terminal seed.code (selection seed feasible).policy.policy.val seed.history (respond seed.code (table seed)) := new.2.2.1
  have oldAfter : ((original seed).actualExecution seed.history.length).after =
      Open.terminal seed.code seed.reference seed.history (respond seed.code (table seed)) := old.2.2.1
  exact ⟨generated.1, newAfter.trans (generated.2.trans (congrArg
    (fun current : RawCurrent Party Good Technology Instrument => current.addReserve
      (Open.reserve seed.code (selection seed feasible).policy.policy.val seed.reference seed.history (respond seed.code (table seed))))
    oldAfter.symm))⟩

theorem actual_raw_responsibility_vector_is_not_worse :
    ∀ metric, (replacement seed feasible).actualScore metric ≤ (original seed).actualScore metric := by
  intro metric
  rw [(replacement seed feasible).opponent_payoff_is_the_actual_receipt_vector _ rfl,
    (original seed).opponent_payoff_is_the_actual_receipt_vector _ rfl]
  have originalComparison := ((comparison_iff seed.code _ _).mp (selection seed feasible).policy.no_regression).1
  exact ((Open.finite_comparison_iff_every_same_opponent seed.code _ _
    (selection seed feasible).policy.policy.property seed.reference_generated).mp originalComparison).1
    (respond seed.code (table seed)) seed.history seed.original metric

theorem every_old_legal_continuation_remains_open (stable : Open.Stable seed.code.law)
    (words : List (RawEvent Party Good Port Technology Instrument))
    (accepted : Open.LegalHistory seed.code.law ((original seed).actualExecution seed.history.length).after words) :
    Open.LegalHistory seed.code.law ((replacement seed feasible).actualExecution seed.history.length).after words := by
  obtain ⟨nonnegative, extension⟩ := actual_full_carrier_extension seed feasible
  rw [extension]
  exact (Open.every_old_legal_history_remains_open seed.code.law stable _ _ nonnegative words accepted).1

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Identity
