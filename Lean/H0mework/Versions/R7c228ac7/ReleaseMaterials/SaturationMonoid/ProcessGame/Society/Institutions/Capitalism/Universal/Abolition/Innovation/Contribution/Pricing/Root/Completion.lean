import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Protocol

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
  (prepared : Prepared source mechanism)

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

omit [DecidableEq Technology] in
theorem an_actual_trace_keeps_its_ready_boundary_and_available_review
    {start target : C} {word : RawEvent Party Good Port Technology Instrument}
    (actual : Runtime.Trace start word target) :
    Runtime.Ready start → Runtime.ReviewAvailable start →
      Runtime.Ready target ∧ Runtime.ReviewAvailable target := by
  induction actual with
  | nil start => exact fun ready review => ⟨ready,review⟩
  | cons start request tail target ready review noConsents valid later inherited =>
      intro _ready _review
      exact inherited
        (Runtime.two_actual_root_steps_pay_and_consume_the_generated_primitive
          start request ready review noConsents valid).1
        (Runtime.afterNative_keeps_the_available_review start request ready review noConsents valid)

theorem the_default_payment_is_exactly_the_preflighted_source_suffix
    (nature : Request Party Good Port Technology Instrument) :
    prepared.schedule.requests nature mechanism.investmentPort =
      prepared.schedule.programme.word nature ++
        (decision prepared nature none).word prepared.schedule mechanism.investmentPort := by
  unfold Source.Schedule.requests decision
  cases selected : prepared.schedule.select nature <;>
    simp only [Source.Schedule.payment,Source.submit,selected,Source.Submission.word]

theorem a_supported_prepared_trial_forces_its_actual_price_completion
    (nature : prepared.schedule.programme.QuotedNature)
    (ready : Runtime.Ready source) (review : Runtime.ReviewAvailable source)
    {afterBody : C} (actualBody : Runtime.Trace source (bodyWord prepared nature.val) afterBody) :
    ∃ target actualPrice, Runtime.run afterBody (priceWord prepared nature.val none) =
      .completed target actualPrice := by
  have checked := prepared.allBranches nature (every_declared_nature_is_in_the_forecast_domain _ nature)
  have sourceValid : ∀ item ∈ (sourceInput source).law.rawItems source.raw
      (prepared.schedule.requests nature.val mechanism.investmentPort),
      (sourceInput source).law.Valid item.before item.request :=
    fun item member => (checked.2.1.1 item member).1
  rw [the_default_payment_is_exactly_the_preflighted_source_suffix prepared nature.val,
    RawLaw.rawItems,RawLaw.execute_append] at sourceValid
  have suffixValid : ∀ item ∈ ((sourceInput source).law.execute
      (prepared.schedule.programme.after nature.val) (prepared.schedule.programme.word nature.val).length
      ((decision prepared nature.val none).word prepared.schedule mechanism.investmentPort)).items,
      (sourceInput source).law.Valid item.before item.request := by
    intro item member
    apply sourceValid item
    apply List.mem_append_right
    have endpoint : ((sourceInput source).law.execute source.raw 0
        (prepared.schedule.programme.word nature.val)).final = prepared.schedule.programme.after nature.val := rfl
    rw [endpoint]
    simpa only [Nat.zero_add] using member
  have boundary := an_actual_trace_keeps_its_ready_boundary_and_available_review actualBody ready review
  apply Runtime.a_checked_original_word_forces_actual_root_completion afterBody _
    (prepared.schedule.programme.word nature.val).length boundary.1 boundary.2
    (Runtime.normalised_requests_have_no_controller_consents _)
  rw [actualBody.keeps_the_original_source_input,
    the_actual_trial_endpoint_is_the_original_price_basis prepared nature.val actualBody]
  exact Runtime.public_normalisation_preserves_all_actual_request_guards source.native.input.law
    (prepared.schedule.programme.after nature.val) (prepared.schedule.programme.word nature.val).length _ suffixValid

theorem the_prepared_default_contract_is_delivered_by_the_same_actual_root
    (nature : prepared.schedule.programme.QuotedNature)
    (ready : Runtime.Ready source) (review : Runtime.ReviewAvailable source) :
    ∃ afterBody actualBody target actualPrice,
      execute prepared nature.val none =
        .delivered afterBody actualBody (.completed target actualPrice) := by
  obtain ⟨afterBody,actualBody,bodyCompleted⟩ :=
    a_supported_prepared_trial_forces_its_actual_body_completion prepared nature ready review
  obtain ⟨target,actualPrice,priceCompleted⟩ :=
    a_supported_prepared_trial_forces_its_actual_price_completion prepared nature ready review actualBody
  exact ⟨afterBody,actualBody,target,actualPrice,by
    simp only [execute,bodyCompleted,priceCompleted]⟩

omit [DecidableEq Technology] in
theorem the_two_actual_instruction_traces_compose_without_another_occurrence
    {first middle target : C} {front back : RawEvent Party Good Port Technology Instrument}
    (actualFront : Runtime.Trace first front middle) (actualBack : Runtime.Trace middle back target) :
    Runtime.Trace first (front ++ back) target := by
  induction actualFront with
  | nil first => exact actualBack
  | cons first request tail middle ready review noConsents valid later inherited =>
      exact .cons first request (tail ++ back) target ready review noConsents valid (inherited actualBack)

theorem the_prepared_default_payment_generates_its_same_whole_ledger_successor
    (nature : prepared.schedule.programme.QuotedNature)
    (ready : Runtime.Ready source) (review : Runtime.ReviewAvailable source) :
    ∃ afterBody actualBody target actualPrice,
      execute prepared nature.val none = .delivered afterBody actualBody (.completed target actualPrice) ∧
      ∃ whole : Runtime.Trace source (Runtime.normalise
          (prepared.schedule.requests nature.val mechanism.investmentPort)) target,
        target.raw = ((sourceInput source).law.execute source.raw 0
          (prepared.schedule.requests nature.val mechanism.investmentPort)).final ∧
        target.native.input = source.native.input ∧
        (type_of% whole.carries_every_original_row_and_claim_without_refilling) := by
  obtain ⟨afterBody,actualBody,target,actualPrice,delivered⟩ :=
    the_prepared_default_contract_is_delivered_by_the_same_actual_root prepared nature ready review
  have wordSame : Runtime.normalise (prepared.schedule.requests nature.val mechanism.investmentPort) =
      bodyWord prepared nature.val ++ priceWord prepared nature.val none := by
    rw [the_default_payment_is_exactly_the_preflighted_source_suffix prepared nature.val]
    exact List.map_append
  have whole : Runtime.Trace source (Runtime.normalise
      (prepared.schedule.requests nature.val mechanism.investmentPort)) target := by
    rw [wordSame]
    exact the_two_actual_instruction_traces_compose_without_another_occurrence actualBody actualPrice
  refine ⟨afterBody,actualBody,target,actualPrice,delivered,whole,?_,whole.keeps_the_original_source_input,
    whole.carries_every_original_row_and_claim_without_refilling⟩
  exact (whole.raw_is_the_complete_original_execution 0).trans
    (Runtime.public_normalisation_keeps_the_complete_original_execution source.native.input.law source.raw 0
      (prepared.schedule.requests nature.val mechanism.investmentPort))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root
