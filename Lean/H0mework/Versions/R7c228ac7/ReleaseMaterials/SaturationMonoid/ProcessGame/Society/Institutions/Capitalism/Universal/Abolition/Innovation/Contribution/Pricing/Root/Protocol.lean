import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Preparation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  (prepared : Prepared source mechanism) (nature : Request Party Good Port Technology Instrument)
  (proposed : Option ℚ)

def bodyWord := Runtime.normalise (prepared.schedule.programme.word nature)
def decision := Source.submit prepared.schedule nature proposed
def priceWord := Runtime.normalise ((decision prepared nature proposed).word prepared.schedule mechanism.investmentPort)

theorem every_refused_risk_amount_sends_no_financial_requests
    (refused : (decision prepared nature proposed).net prepared.schedule = none) :
    priceWord prepared nature proposed = [] := by
  unfold priceWord
  cases selected : decision prepared nature proposed <;>
    simp [selected,Source.Submission.net] at refused <;>
    simp [Source.Submission.word,Runtime.normalise]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

def runtimeBlocked {before : C} {word : RawEvent Party Good Port Technology Instrument} :
    Runtime.Outcome before word → Prop
  | .completed _ _ => False
  | .blocked .. => True

inductive Execution : Type 4
  | interrupted (body : Runtime.Outcome source (bodyWord prepared nature)) (blocked : runtimeBlocked body)
  | delivered (afterBody : C) (actualBody : Runtime.Trace source (bodyWord prepared nature) afterBody)
      (price : Runtime.Outcome afterBody (priceWord prepared nature proposed))

/-- The price writer is entered only after the original trial body has
actually run and its native admissions have been consumed. -/
def execute : Execution prepared nature proposed :=
  match Runtime.run source (bodyWord prepared nature) with
  | .completed afterBody actualBody =>
      .delivered afterBody actualBody (Runtime.run afterBody (priceWord prepared nature proposed))
  | .blocked front stopped request remaining split actual issue =>
      .interrupted (.blocked front stopped request remaining split actual issue) trivial

def Execution.current : Execution prepared nature proposed → C
  | .interrupted body _ => body.current
  | .delivered _ _ price => price.current

theorem the_actual_trial_endpoint_is_the_original_price_basis
    {afterBody : C} (actual : Runtime.Trace source (bodyWord prepared nature) afterBody) :
    afterBody.raw = prepared.schedule.programme.after nature := by
  exact (actual.raw_is_the_complete_original_execution 0).trans
    (Runtime.public_normalisation_keeps_the_complete_original_execution source.native.input.law source.raw 0
      (prepared.schedule.programme.word nature))

theorem a_completed_trial_keeps_the_original_accounts_and_every_responsibility
    {afterBody : C} (actual : Runtime.Trace source (bodyWord prepared nature) afterBody) :
    afterBody.native.input = source.native.input ∧
      type_of% actual.carries_every_original_row_and_claim_without_refilling :=
  ⟨actual.keeps_the_original_source_input,actual.carries_every_original_row_and_claim_without_refilling⟩

theorem every_new_price_request_is_routed_by_its_original_root
    {afterBody : C} (_actual : Runtime.Trace source (bodyWord prepared nature) afterBody)
    (request : Request Party Good Port Technology Instrument)
    (_generated : request ∈ priceWord prepared nature proposed) :
    Evolving.Epoch.Current.ClosedAt (Runtime.queued afterBody request) ∧
      (Runtime.afterBody afterBody request).inquiry.erase =
        (RootInquiryProcessNode.answered (Runtime.queued afterBody request).inquiry PUnit.unit).erase :=
  ⟨Runtime.each_queued_request_is_an_actual_whole_ledger_root_step afterBody request,
    (Runtime.the_actual_body_is_the_same_root_answer_and_generated_next afterBody request).1⟩

theorem a_supported_prepared_trial_forces_its_actual_body_completion
    (nature : prepared.schedule.programme.QuotedNature)
    (ready : Runtime.Ready source) (review : Runtime.ReviewAvailable source) :
    ∃ afterBody actual, Runtime.run source (bodyWord prepared nature.val) = .completed afterBody actual := by
  have checks := prepared.allBranches nature (every_declared_nature_is_in_the_forecast_domain _ nature)
  have bodyValid : ∀ item ∈ ((sourceInput source).law.execute source.raw 0
      (prepared.schedule.programme.word nature.val)).items, (sourceInput source).law.Valid item.before item.request := by
    intro item member
    apply (checks.2.1.1 item ?_).1
    unfold Source.Schedule.requests
    rw [RawLaw.rawItems,RawLaw.execute_append]
    exact List.mem_append_left _ member
  apply Runtime.a_checked_original_word_forces_actual_root_completion source _ 0 ready review
    (Runtime.normalised_requests_have_no_controller_consents _)
  exact Runtime.public_normalisation_preserves_all_actual_request_guards source.native.input.law source.raw 0 _ bodyValid

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root
