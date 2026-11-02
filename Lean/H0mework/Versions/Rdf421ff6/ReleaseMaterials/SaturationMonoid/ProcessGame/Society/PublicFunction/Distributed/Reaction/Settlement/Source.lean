import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Settlement.Compiler
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Identity.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Settlement

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (seed : Machine Party Good Port Technology Instrument) (feasible : seed.code.feasible seed.reference)

abbrev reference : Program seed.code := ⟨seed.reference, seed.reference_generated⟩
abbrev history : OriginalHistory seed.code := ⟨seed.history, seed.original⟩
abbrev table := restrict seed.code seed.opponent

theorem public_bootstrap_is_actually_emitted (nonempty : seed.code.bootstrap ≠ []) :
    (seed.actualExecution 0).submitted = seed.code.bootstrap := by
  obtain ⟨suffix, _legal, same⟩ := List.mem_map.mp seed.original
  have words : seed.history = seed.code.bootstrap :: suffix := by
    simpa only [Code.publicPrefix, if_neg nonempty, List.singleton_append] using same.symm
  rw [seed.history_word_is_actual 0 (by rw [words]; simp)]
  simp only [words, List.getElem_cons_zero]

def selection : Selection seed.code (reference seed) :=
  match compile seed.code (reference seed) with
  | .selected chosen => chosen
  | .blocked rejected => False.elim (feasible_original_cannot_be_blocked seed.code (reference seed) feasible rejected)

def original := machine seed.code (reference seed) (history seed) (table seed)
def replacement := machine seed.code (selection seed feasible).policy.policy (history seed) (table seed)

theorem original_opponent_response_is_actually_emitted (program : Program seed.code) :
    ((machine seed.code program (history seed) (table seed)).actualExecution seed.history.length).submitted =
      (execution seed.code program.val seed.history seed.opponent).word :=
  Identity.canonical_source_emits_the_original_opponent_response seed program

theorem actual_native_profiles_preserve_realized_rights :
    profile seed.code (selection seed feasible).policy.policy (history seed) (table seed) =
      profile seed.code (reference seed) (history seed) (table seed) :=
  ((comparison_iff seed.code _ _).mp (selection seed feasible).policy.no_regression).2 _ _
    (restriction_is_generated seed.code seed.opponent)

theorem actual_old_debts_keep_their_original_native_admission :
    ∀ index (inside : index < (before seed.code (reference seed) (history seed) (table seed)).current.slots.length),
      ∃ new ∈ (before seed.code (selection seed feasible).policy.policy (history seed) (table seed)).current.slots,
        Identity.DebtCorrespondence seed.code (original seed).input (replacement seed feasible).input
          (before seed.code (reference seed) (history seed) (table seed)).current.slots[index] new :=
  Identity.equal_images_recover_each_original_native_debt seed.code (original seed).input
    (replacement seed feasible).input _ _
    (congrArg Profile.originalDebts (actual_native_profiles_preserve_realized_rights seed feasible))

theorem actual_payment_receipts_do_not_regress (index : Nat)
    (inside : index < (before seed.code (reference seed) (history seed) (table seed)).current.slots.length)
    (holder : Party) :
    received seed.code (reference seed) (history seed) (table seed) index holder ≤
      received seed.code (selection seed feasible).policy.policy (history seed) (table seed) index holder :=
  lawful_comparison_protects_each_original_holder seed.code _ _ (selection seed feasible).policy.no_regression
    _ _ (restriction_is_generated seed.code seed.opponent) index inside holder

theorem actual_material_time_and_admissibility_do_not_regress (metric : Material Party Good)
    (present : metric ∈ materials seed.code) :
    (replacement seed feasible).actualScore (materialMetric metric) ≤
      (original seed).actualScore (materialMetric metric) := by
  have values := ((comparison_iff seed.code _ _).mp (selection seed feasible).policy.no_regression).1
  exact values (.material (history seed) (table seed) metric)
    (material_axis_is_generated seed.code _ _ (restriction_is_generated seed.code seed.opponent) metric present)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Settlement
