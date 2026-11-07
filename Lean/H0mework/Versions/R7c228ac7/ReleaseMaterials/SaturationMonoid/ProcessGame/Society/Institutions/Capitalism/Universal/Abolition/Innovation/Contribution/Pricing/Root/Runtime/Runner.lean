import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime.Native

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

inductive Trace : C → RawEvent Party Good Port Technology Instrument → C → Prop
  | nil (source : C) : Trace source [] source
  | cons (source : C) (request : Request Party Good Port Technology Instrument)
      (tail : RawEvent Party Good Port Technology Instrument) (target : C)
      (ready : Ready source) (review : ReviewAvailable source) (noConsents : request.consents = [])
      (valid : (Physical.Public.interpreter source.native.input).Valid source.raw request)
      (later : Trace (afterNative source request) tail target) : Trace source (request :: tail) target

inductive Issue (source : C) (request : Request Party Good Port Technology Instrument) : Type
  | nativePending (work : Public.Inquiry.HasWork source.native.frame source.native.actual.actual)
  | reviewPending (cursor : Evolving.Epoch.ReviewCursor (Party := Party) (Good := Good) (Port := Port)
        (Technology := Technology) (Instrument := Instrument))
      (original : source.control.review = some cursor) (pending : cursor.recourse = false)
  | consents (original : request.consents ≠ [])
  | material (failed : ¬ (Physical.Public.interpreter source.native.input).Valid source.raw request)

private def reviewIssue (source : C) (request : Request Party Good Port Technology Instrument)
    (failed : ¬ ReviewAvailable source) : Issue source request :=
  match original : source.control.review with
  | none => False.elim (failed (by simp only [ReviewAvailable,original]))
  | some cursor => .reviewPending cursor original (Bool.eq_false_of_not_eq_true (by
      intro allowed
      exact failed (by simp only [ReviewAvailable,original,allowed])))

inductive Outcome (source : C) (word : RawEvent Party Good Port Technology Instrument) : Type 4
  | completed (target : C) (actual : Trace source word target)
  | blocked (front : RawEvent Party Good Port Technology Instrument) (stopped : C)
      (request : Request Party Good Port Technology Instrument) (remaining : RawEvent Party Good Port Technology Instrument)
      (split : word = front ++ request :: remaining) (actual : Trace source front stopped) (issue : Issue stopped request)

/-- Each original request uses its real body write and native consumption;
issue heads take the original birth branch before the next request is read. -/
def run (source : C) : (word : RawEvent Party Good Port Technology Instrument) → Outcome source word
  | [] => .completed source (.nil source)
  | request :: tail =>
      if ready : Ready source then
        if review : ReviewAvailable source then
          if noConsents : request.consents = [] then
            if valid : (Physical.Public.interpreter source.native.input).Valid source.raw request then
              match run (afterNative source request) tail with
              | .completed target actual =>
                  .completed target (.cons source request tail target ready review noConsents valid actual)
              | .blocked front stopped first remaining split actual issue =>
                  .blocked (request :: front) stopped first remaining
                    (by simp only [List.cons_append,split])
                    (.cons source request front stopped ready review noConsents valid actual) issue
            else .blocked [] source request tail rfl (.nil source) (.material valid)
          else .blocked [] source request tail rfl (.nil source) (.consents noConsents)
        else .blocked [] source request tail rfl (.nil source) (reviewIssue source request review)
      else .blocked [] source request tail rfl (.nil source) (.nativePending (Classical.not_not.mp ready))

def Outcome.current {source : C} {word : RawEvent Party Good Port Technology Instrument} :
    Outcome source word → C
  | .completed target _ => target
  | .blocked _ stopped request _ _ _ _ => afterBody stopped request

def Outcome.ticks {source : C} {word : RawEvent Party Good Port Technology Instrument} :
    Outcome source word → Nat
  | .completed _ _ => 2 * word.length
  | .blocked front _ _ _ _ _ _ => 2 * front.length + 1

theorem the_actual_attempt_bound_is_generated_by_its_original_finite_word
    {source : C} {word : RawEvent Party Good Port Technology Instrument}
    (outcome : Outcome source word) : outcome.ticks ≤ 2 * word.length := by
  cases outcome with
  | completed target actual => exact le_refl _
  | blocked front stopped request remaining split actual issue =>
      simp only [Outcome.ticks]
      rw [split]
      simp only [List.length_append,List.length_cons]
      omega

theorem every_blocked_attempt_keeps_its_actual_whole_ledger_next
    {source : C} {word : RawEvent Party Good Port Technology Instrument}
    (front : RawEvent Party Good Port Technology Instrument) (stopped : C)
    (request : Request Party Good Port Technology Instrument) (remaining : RawEvent Party Good Port Technology Instrument)
    (split : word = front ++ request :: remaining) (actual : Trace source front stopped) (issue : Issue stopped request) :
    Evolving.Epoch.Current.ClosedAt (queued stopped request) ∧
      (Outcome.blocked front stopped request remaining split actual issue).current.inquiry.erase =
        (RootInquiryProcessNode.answered (queued stopped request).inquiry PUnit.unit).erase :=
  ⟨each_queued_request_is_an_actual_whole_ledger_root_step stopped request,
    (the_actual_body_is_the_same_root_answer_and_generated_next stopped request).1⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
