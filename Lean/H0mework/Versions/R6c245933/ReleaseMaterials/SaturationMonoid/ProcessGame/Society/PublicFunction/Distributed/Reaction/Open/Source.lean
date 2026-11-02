import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open.Continuation
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (seed : Machine Party Good Port Technology Instrument) (originalFeasible : seed.code.feasible seed.reference)

/-- Feasibility belongs to the supplied original programme. The alternative
and its maximality are computed, not supplied as admission evidence. -/
def selection : Selection seed.code seed.reference :=
  match compile seed.code seed.reference seed.reference_generated with
  | .selected choice => choice
  | .blocked rejected => False.elim (feasible_original_cannot_be_blocked seed.code seed.reference
      seed.reference_generated originalFeasible rejected)

def original := seed.withSide .original

def replacement : Machine Party Good Port Technology Instrument where
  code := seed.code
  reference := (selection seed originalFeasible).policy.policy
  reference_generated := (selection seed originalFeasible).policy.generated
  history := seed.history
  original := seed.original
  opponent := seed.opponent
  side := .original
  continuation := seed.continuation

theorem generated_policy_is_actually_emitted :
    (replacement seed originalFeasible).policy? = some (selection seed originalFeasible).policy.policy := rfl

theorem both_actual_reactions_extend_the_same_history :
    (replacement seed originalFeasible).history = (original seed).history ∧
      (replacement seed originalFeasible).opponent = (original seed).opponent := ⟨rfl, rfl⟩

theorem actual_full_carrier_extension :
    (∀ party good, 0 ≤ reserve seed.code (selection seed originalFeasible).policy.policy
      seed.reference seed.history seed.opponent party good) ∧
      ((replacement seed originalFeasible).actualExecution seed.history.length).after =
        ((original seed).actualExecution seed.history.length).after.addReserve
          (reserve seed.code (selection seed originalFeasible).policy.policy seed.reference seed.history seed.opponent) := by
  have new := (replacement seed originalFeasible).actual_reaction_word_and_next _
    (generated_policy_is_actually_emitted seed originalFeasible)
  have old := (original seed).actual_reaction_word_and_next seed.reference rfl
  have result := generated_full_carrier_extension seed.code _ _ (selection seed originalFeasible).policy.generated
    seed.reference_generated (selection seed originalFeasible).policy.no_regression seed.opponent seed.history seed.original
  have oldReserve := congrArg (fun current : RawCurrent Party Good Technology Instrument =>
    current.addReserve (reserve seed.code (selection seed originalFeasible).policy.policy seed.reference seed.history seed.opponent))
    old.2.2.1.symm
  exact ⟨result.1, new.2.2.1.trans (result.2.trans oldReserve)⟩

theorem raw_responsibility_vector_is_not_worse :
    ∀ metric, (replacement seed originalFeasible).actualScore metric ≤ (original seed).actualScore metric := by
  intro metric
  rw [(replacement seed originalFeasible).opponent_payoff_is_the_actual_receipt_vector _
      (generated_policy_is_actually_emitted seed originalFeasible),
    (original seed).opponent_payoff_is_the_actual_receipt_vector _ rfl]
  exact ((finite_comparison_iff_every_same_opponent seed.code _ _ (selection seed originalFeasible).policy.generated
    seed.reference_generated).mp (selection seed originalFeasible).policy.no_regression).1 seed.opponent seed.history seed.original metric

theorem all_old_legal_histories_remain_actually_open (stable : Stable seed.code.law)
    (words : List (RawEvent Party Good Port Technology Instrument))
    (accepted : LegalHistory seed.code.law ((original seed).actualExecution seed.history.length).after words) :
    LegalHistory seed.code.law ((replacement seed originalFeasible).actualExecution seed.history.length).after words ∧
      words.foldl seed.code.law.next ((replacement seed originalFeasible).actualExecution seed.history.length).after =
        (words.foldl seed.code.law.next ((original seed).actualExecution seed.history.length).after).addReserve
          (reserve seed.code (selection seed originalFeasible).policy.policy seed.reference seed.history seed.opponent) := by
  obtain ⟨nonnegative, same⟩ := actual_full_carrier_extension seed originalFeasible
  rw [same]
  exact every_old_legal_history_remains_open seed.code.law stable _ _ nonnegative words accepted

theorem both_sources_settle_the_original_native_service
    (eligible : seed.code.eligible (trace seed.code seed.reference seed.history seed.opponent) = true) :
    (∀ index, ((Native.generate (original seed) seed.history.length).services index).state.TerminalAt 0) ∧
      (∀ index, ((Native.generate (replacement seed originalFeasible) seed.history.length).services index).state.TerminalAt 0) := by
  let chosen := selection seed originalFeasible
  have raw := ((comparison_iff seed.code _ _ seed.reference_generated).mp chosen.policy.no_regression).1
  have newEligible := no_loss_of_task_admissibility seed.code chosen.policy.policy seed.reference chosen.policy.generated
    seed.reference_generated raw seed.opponent seed.history seed.original eligible
  exact ⟨fun index => Native.actual_feasible_response_closes_native_services (original seed) seed.reference rfl
      originalFeasible eligible index,
    fun index => Native.actual_feasible_response_closes_native_services (replacement seed originalFeasible) chosen.policy.policy
      (generated_policy_is_actually_emitted seed originalFeasible) chosen.policy.feasible newEligible index⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Open
