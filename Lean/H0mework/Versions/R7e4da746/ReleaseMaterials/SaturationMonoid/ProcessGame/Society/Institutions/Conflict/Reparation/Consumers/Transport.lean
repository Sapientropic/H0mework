import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Consumers.Occurrence
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Path.Registration
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Consumers.Issue.Native

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Consumers

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Root.Registered.Macro
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Conflict.Consumers.Evolving (C R W compact conflict sourceInput sourceRead)
open Quantities.Execution (primitiveScript endAt)
open Evolving.Consumers.Issue (request)
open Transport

noncomputable section

open private executed from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Consumers.Occurrence

private abbrev issueInput : Option (Compile.RawInput Bool Bool Bool Unit Unit) :=
  some (.primitive request)

private theorem original_issue_registers (cut : C) (ready : Ready cut) (review : ReviewAvailable cut) :
    let body := afterBody cut request
    NativeWork body ∧ ∃ registration, registrationAt body = some registration := by
  let q := queued cut request
  have done : ¬ NativeWork q := ready
  have valid := Evolving.Consumers.Issue.valid_at_every_actual_raw cut.native.input cut.raw
  refine ⟨the_actual_body_must_consume_its_original_native_head cut request ready review rfl valid, ?_⟩
  have readers : q.executionReader = q.native.reader := by
    funext cursor account
    exact the_available_review_forwards_the_actual_requested_primitive cut request review
  have found : (registrationAt (afterBody cut request)).isSome = true := by
    unfold registrationAt afterBody
    rw [show (queued cut request).advance = Evolving.Epoch.Transition.next q done from q.advance_eq_epoch done]
    change (Public.Accounting.registration? q.native.input q.native.depth q.native.count q.native.prefixLimit
      q.native.renewalLimit q.native.oldPast
      (Factory.Direct.selectedStart q.native.full q.native.sourceActual q.executionReader)
      (Factory.Direct.bodyNext q.native.full q.native.sourceActual)).isSome = true
    rw [readers]
    exact Evolving.Consumers.Issue.Native.found q.native done rfl
  exact ⟨_, (Option.some_get found).symm⟩

private theorem at_original_issue (front : W) (paid : Conflict.Root.Paid warCut ((conflict ++ front) ++ [request])) :
    let cut := originalAt original (primitiveScript front ++ [issueInput])
    NativeWork cut ∧ ∃ registration, registrationAt cut = some registration := by
  have trace := Conflict.Root.trace_after_prefix warCut _ (conflict ++ front) [request] paid.trace
  have start := trace.a_nonempty_execution_starts_at_the_actual_ready_boundary (by simp)
  have same : Conflict.Root.terminal warCut (conflict ++ front) = originalAt original (primitiveScript front) := by
    unfold originalAt Reparation.Birth.attacked Conflict.Root.terminal
    rw [Quantities.Execution.primitiveScript_append, Quantities.Execution.endAt_append]
  rw [same] at start
  have registered := original_issue_registers _ start.1 start.2
  unfold originalAt
  rw [Quantities.Execution.endAt_append]
  exact registered

def firstBirthPrefix := primitiveScript [receipt 2] ++ [issueInput]
def secondBirthPrefix := primitiveScript [receipt 2, request, receipt 4] ++ [issueInput]

theorem the_second_birth_follows_the_first_on_the_same_trajectory :
    secondBirthPrefix = (firstBirthPrefix ++ [none]) ++ primitiveScript [receipt 4] ++ [issueInput] := rfl

private theorem first_issue_paid : Conflict.Root.Paid warCut ((conflict ++ [receipt 2]) ++ [request]) :=
  executed _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem second_issue_paid :
    Conflict.Root.Paid warCut ((conflict ++ [receipt 2, request, receipt 4]) ++ [request]) :=
  executed _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem first_paid_due :
    recordedDue warCut conflict (firstBirthPrefix ++ [none]) id address = 4 := by
  change recordedDue warCut conflict (primitiveScript [receipt 2, request]) id address = 4
  rw [recordedDue_of_paid_word original (show Conflict.Root.Paid warCut
    (conflict ++ [receipt 2, request]) from first_issue_paid)]
  unfold remaining received continuationItems occurred
  rw [gross_is_the_original_six, sourceInput, sourceRead]
  decide +kernel

private theorem second_paid_due :
    recordedDue warCut conflict (secondBirthPrefix ++ [none]) id address = 0 := by
  change recordedDue warCut conflict (primitiveScript [receipt 2, request, receipt 4, request]) id address = 0
  rw [recordedDue_of_paid_word original (show Conflict.Root.Paid warCut
    (conflict ++ [receipt 2, request, receipt 4, request]) from second_issue_paid)]
  unfold remaining received continuationItems occurred
  rw [gross_is_the_original_six, sourceInput, sourceRead]
  decide +kernel

def recordsActualBirth (history : List (Option (Compile.RawInput Bool Bool Bool Unit Unit))) : Prop :=
    let cut := originalAt original history
    let before := run original history
    let after := run original (history ++ [none])
    ∃ (work : NativeWork cut) (registered : Admission.Registration cut.native),
      registrationAt cut = some registered ∧
      (step before none).emission = .admission (Admission.generated before.resident registered work) ∧
      (step before none).emission.next = after.resident.erase

def paidAt (history : List (Option (Compile.RawInput Bool Bool Bool Unit Unit))) : Prop :=
  Nonempty ((Birth.law original).SettlementAt (run original history).position.phase)

theorem first_actual_birth_preserves_the_four_due_and_generates_next :
    recordsActualBirth firstBirthPrefix ∧
    recordedDue warCut conflict firstBirthPrefix id address = 4 ∧
    ¬ paidAt (firstBirthPrefix ++ [none]) := by
  obtain ⟨work, registered, selected⟩ := at_original_issue _ first_issue_paid
  have transported := every_original_registration_transports_the_live_account original firstBirthPrefix none work selected
  refine ⟨⟨work, registered, selected, transported.1, transported.2.1⟩,
    transported.2.2.2.1.symm.trans first_paid_due, ?_⟩
  intro settled
  have zero := (exact_settlement_at_every_generated_visit original _).mp settled
  exact (by decide : (4 : ℚ) ≠ 0) (first_paid_due.symm.trans zero)

theorem second_actual_birth_preserves_the_paid_row_and_generates_next :
    recordsActualBirth secondBirthPrefix ∧ paidAt secondBirthPrefix ∧ paidAt (secondBirthPrefix ++ [none]) := by
  obtain ⟨work, registered, selected⟩ := at_original_issue _ second_issue_paid
  have transported := every_original_registration_transports_the_live_account original secondBirthPrefix none work selected
  refine ⟨⟨work, registered, selected, transported.1, transported.2.1⟩, ?_,
    (exact_settlement_at_every_generated_visit original _).mpr second_paid_due⟩
  exact (exact_settlement_at_every_generated_visit original _).mpr
    (transported.2.2.2.1.symm.trans second_paid_due)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Consumers
