import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Runtime

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Review

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (point : Cursor model.source.code) (origin : Origin point) (template : Template (code := model.source.code))
  (selected : Activation template)

def rows (account : (Financial.process (target point origin template selected).input).GeneratedState) :=
  ((Identity.financeImage model.source.code (target point origin template selected).input account).drop
    (Debt.account point origin).current.slots.length)

def Protected : Prop := rows model point origin template selected
    (Runtime.native model point origin template selected).joint.finance =
  rows model point origin template selected (Financial.accountAt (target point origin template selected).input (arrival point))

instance : Decidable (Protected model point origin template selected) := by unfold Protected rows;infer_instance

inductive Outcome where
  | cleared (original : remaining point origin template = 0)
      (quantity : quantity point origin template = 0)
  | noPositiveRequest (original : 0 < remaining point origin template) (nonpositive : template.amount ≤ 0)
  | exhausted (original : 0 < remaining point origin template) (budget : (seed point).remaining = 0)
  | unavailableMemory (original : 0 < remaining point origin template)
      (memory : model.source.code.memoryReady ((seed point).frame.inbox selected.site) = false)
  | refused (item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument)
      (actual : item ∈ model.source.code.law.rawItems (execution point origin template selected).before
        (execution point origin template selected).submitted)
      (failure : ¬ model.source.code.law.Valid item.before item.request)
  | newbornMismatch (mismatch : ¬ Protected model point origin template selected)
  | paid (quantity : 0 < quantity point origin template)
      (actual : (execution point origin template selected).submitted = [payment point origin template])
      (lawful : ∀ item ∈ model.source.code.law.rawItems (execution point origin template selected).before
        (execution point origin template selected).submitted,model.source.code.law.Valid item.before item.request)
      (newborn : Protected model point origin template selected)

def generate : Outcome model point origin template selected :=
  if original : 0 < remaining point origin template then
    if positive : 0 < template.amount then
      if exhausted : (seed point).remaining = 0 then .exhausted original exhausted
      else if memory : model.source.code.memoryReady ((seed point).frame.inbox selected.site) = true then
        match inspect (fun item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument =>
          model.source.code.law.Valid item.before item.request)
          (model.source.code.law.rawItems (execution point origin template selected).before
            (execution point origin template selected).submitted) with
        | .rejected item actual failure => .refused item actual failure
        | .accepted lawful =>
          if checked : Protected model point origin template selected then
            .paid (lt_of_lt_of_le (lt_min positive original) (le_max_right _ _)) (by
              rw [the_generated_word_is_actually_submitted,if_neg exhausted,if_pos memory]
              exact if_pos (lt_of_lt_of_le (lt_min positive original) (le_max_right _ _))) lawful checked
          else .newbornMismatch checked
      else .unavailableMemory original (Bool.eq_false_iff.mpr memory)
    else .noPositiveRequest original (le_of_not_gt positive)
  else .cleared (le_antisymm (le_of_not_gt original) (original_remaining_is_nonnegative point origin template)) (by
    have empty : remaining point origin template = 0 :=
      le_antisymm (le_of_not_gt original) (original_remaining_is_nonnegative point origin template)
    simp [quantity,empty])

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Review
