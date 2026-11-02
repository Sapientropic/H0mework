import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Quota.Plan
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Quota.Regression

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

abbrev need := Feedback.Regression.need
def issue : Request Bool Unit Unit Unit Unit := ⟨true, [], (), [], .issue () true false 1⟩
def uncapped : Request Bool Unit Unit Unit Unit := ⟨true, [], (), [], .settle () true false 9⟩
def payment : Request Bool Unit Unit Unit Unit := ⟨true, [], (), [], .settle () true false 2⟩

abbrev code : Code Bool Unit Unit Unit Unit := {Feedback.Regression.code with
  initial := {Feedback.Regression.code.initial with
    stock := fun person _ => if person then 4 else 0
    claims := fun _instrument debtor creditor => if debtor && !creditor then 7 else 0}
  bootstrap := [issue, issue]
  actions := [need, uncapped, payment] }

def originalPolicy : code.Policy := fun key _ => if key.2 = 0 then [need] else [uncapped]

theorem original_policy_is_generated : originalPolicy ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key _
  simp only [originalPolicy]
  split <;> exact (mem_words_iff _ _ _).mpr (by simp)

def opponent : Opponent code := fun _ past _ => match past.length with
  | 0 => some ⟨.activate 0, by decide +kernel⟩
  | 1 => some ⟨.send 0 0, by decide +kernel⟩
  | 2 => some ⟨.deliver 0, by decide +kernel⟩
  | 3 => some ⟨.activate 0, by decide +kernel⟩
  | _ => none

abbrev base : Machine Bool Unit Unit Unit Unit where
  code := code
  reference := originalPolicy
  reference_generated := original_policy_is_generated
  history := [[issue, issue]]
  original := by decide +kernel
  opponent := opponent
  side := .original

abbrev original := base.withFeedback opponent 3
abbrev input : Input code := ⟨opponent, 3⟩
abbrev position : Repayment.Position Bool Unit := ⟨(), true, false⟩
abbrev source := planned original input 2 position 0 rfl

theorem actual_cut_distinguishes_raw_debt_from_native_support :
    (original.feedbackState input 2).current.claims () true false = 9 ∧
      support original 2 position = 2 ∧ amount original input 2 position = 2 ∧
      candidate original input 2 position = [payment] := by decide +kernel

theorem actual_capped_payment_uses_both_original_slots_and_keeps_unbacked_balance :
    (original.actualExecution 4).submitted = [uncapped] ∧
      (source.actualExecution 4).submitted = [payment] ∧
      (source.actualExecution 4).after.stock true () = 1 ∧
      (source.actualExecution 4).after.stock false () = 2 ∧
      (source.actualExecution 4).after.claims () true false = 7 ∧
      Financial.outstanding source.input (Native.generate source 4).finance.current = 0 ∧
      (Native.generate source 4).finance.current.slots.length = 2 ∧
      (source.feedbackState input 3).past.length = 4 ∧
      (source.feedbackState input 3).frame.sent.length = 1 := by decide +kernel

abbrev paymentIndex : Fin (Financial.IssueTrace.inventory source.input 5).length := ⟨3, by decide +kernel⟩
abbrev origin := Financial.IssueTrace.origin source.input 5 paymentIndex
abbrev before := Financial.IssueTrace.before source.input 5 paymentIndex
def movement : Financial.Movement source.input origin :=
  (Financial.readMovement source.input origin).get (by decide +kernel)

theorem actual_movement_is_supported_without_raw_ledger_equality :
    movement.quantity = 2 ∧ movement.instruction.before.claims () true false = 9 ∧
      Financial.BalanceConservation.ledgerClaims source.input before.current () true false = 2 := by
  decide +kernel

theorem original_slot_quota_is_exhausted_and_uncovered_claims_are_preserved :
    (Financial.allocate source.input origin before movement.quantity (movement.quantity_nonnegative source.input)).remaining = 0 ∧
      (source.input.law.step movement.instruction.before movement.instruction.request).claims () true false -
        Financial.BalanceConservation.ledgerClaims source.input
          (Financial.allocate source.input origin before movement.quantity
            (movement.quantity_nonnegative source.input)).after.current () true false =
      movement.instruction.before.claims () true false -
        Financial.BalanceConservation.ledgerClaims source.input before.current () true false := by
  have within : movement.quantity ≤ Financial.BalanceConservation.ledgerClaims source.input before.current
      movement.instrument movement.debtor movement.sender := by decide +kernel
  exact ⟨Financial.BalanceConservation.supported_movement_quota_exhausted source.input movement before within,
    Financial.BalanceConservation.supported_movement_preserves_uncovered_claims source.input movement before within _ _ _⟩

theorem next_cut_does_not_repeat_the_capped_request :
    (source.actualExecution 5).submitted = [] ∧
      source.feedbackPolicy 3 = original.feedbackPolicy 3 := by
  exact ⟨by decide +kernel,
    original.scheduled_policy_does_not_change_other_cuts 2 3 _ (by decide +kernel)⟩

theorem unbacked_remainder_does_not_generate_another_native_payment :
    (source.feedbackState input 3).current.claims () true false = 7 ∧
      support source 3 position = 0 ∧ amount source input 3 position = 0 ∧
      emitted source input 3 position = [] := by decide +kernel

abbrev refusedCode : Code Bool Unit Unit Unit Unit := {code with
  law := {code.law with policy := .opaque fun _ request => match request.operation with
    | .settle .. => false | _ => true}}

def refusedOpponent : Opponent refusedCode := fun _ past _ => match past.length with
  | 0 => some ⟨.activate 0, by decide +kernel⟩
  | 1 => some ⟨.send 0 0, by decide +kernel⟩
  | 2 => some ⟨.deliver 0, by decide +kernel⟩
  | 3 => some ⟨.activate 0, by decide +kernel⟩
  | _ => none

abbrev refusedBase : Machine Bool Unit Unit Unit Unit := {base with
  code := refusedCode
  opponent := refusedOpponent
  feedback? := none
  feedbackOverrides := []}
abbrev refusedOriginal := refusedBase.withFeedback refusedOpponent 3
abbrev refusedInput : Input refusedCode := ⟨refusedOpponent, 3⟩
abbrev refusedSource := planned refusedOriginal refusedInput 2 position 0 rfl

def blocked : Repayment.Quota.Outcome refusedCode.law position (refusedOriginal.feedbackState refusedInput 2).current
    (support refusedOriginal 2 position) → Bool
  | .blocked .. => true | _ => false

theorem the_exact_capped_candidate_is_rechecked_and_refusal_keeps_both_debts :
    blocked (proposal refusedOriginal refusedInput 2 position) = true ∧
      (refusedSource.actualExecution 4).submitted = [payment] ∧
      (refusedSource.actualExecution 4).after.stock true () = 3 ∧
      (refusedSource.actualExecution 4).after.stock false () = 0 ∧
      (refusedSource.actualExecution 4).after.claims () true false = 9 ∧
      Financial.outstanding refusedSource.input (Native.generate refusedSource 4).finance.current = 2 := by
  decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Quota.Regression
