import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Observed

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Observed.Transcript

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

/-- The published past controls are the input; private success/failure never
    decides how much of this input the planner is allowed to see. -/
def publicViews (published : List (Distributed.Recall.Information.Agency.Protocol.Rule code))
    (initial : List (View (code := code))) := published.foldl (fun views rule => PublicDomain.next rule views) initial

def actualView (published : List (Distributed.Recall.Information.Agency.Protocol.Rule code))
    (initial : View (code := code)) (pastOpponent : Opponent code) :=
  published.foldl (fun actual rule => Evidence.after actual rule pastOpponent) initial

theorem every_actual_past_keeps_a_representative_in_the_same_public_domain
    (published : List (Distributed.Recall.Information.Agency.Protocol.Rule code))
    (initial : List (View (code := code))) (actual : View (code := code))
    (covered : Knowledge.Contains initial actual) (pastOpponent : Opponent code) :
    Knowledge.Contains (publicViews published initial) (actualView published actual pastOpponent) := by
  unfold publicViews actualView
  induction published generalizing initial actual with
  | nil => exact covered
  | cons rule rest ih => exact ih _ _ (PublicDomain.after initial actual covered rule pastOpponent)

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (budget : Nat) (published : List (Distributed.Recall.Information.Agency.Protocol.Rule model.source.code))
  (reference : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)

abbrev views := publicViews published (completeViews model budget)
abbrev plan := Observed.plan model (views model budget published) reference
abbrev prepared := Observed.prepare model (views model budget published) reference

variable (world : Distributed.Recall.Information.World model budget)
  (pastOpponent futureOpponent : Opponent model.source.code)

abbrev actual := actualView published (ofWorld model budget world) pastOpponent
abbrev finish := (prepared model budget published reference).finish (actual model budget published world pastOpponent) futureOpponent
abbrev facade := Native.AuthorityRuntime.facade ((prepared model budget published reference).bound
  (actual model budget published world pastOpponent) futureOpponent)
abbrev activated := Inquiry.Runtime.readState ((prepared model budget published reference).bound
  (actual model budget published world pastOpponent) futureOpponent)
  (depth (finish model budget published reference world pastOpponent futureOpponent))

theorem actual_coverage_is_generated_without_a_caller_witness :
    Knowledge.Contains (views model budget published) (actual model budget published world pastOpponent) :=
  every_actual_past_keeps_a_representative_in_the_same_public_domain published (completeViews model budget)
    (ofWorld model budget world)
    (Knowledge.member _ _ (every_source_generated_world_is_in_the_information_domain model budget world)) pastOpponent

theorem every_original_world_consumes_the_public_plan_and_its_actual_root_without_a_coverage_premise :
    let actual := actual model budget published world pastOpponent
    let prepared := prepared model budget published reference
    let current := activated model budget published reference world pastOpponent futureOpponent
    Knowledge.Contains (views model budget published) actual ∧
      Protected model (views model budget published) reference prepared.outcome ∧
      AcceptedOn model (views model budget published) reference actual prepared.outcome ∧
      Knowledge.Contains prepared.finalViews (prepared.finalView actual futureOpponent) ∧
      ((seed actual.point).frame.localLegal = false →
        (seed (prepared.finish actual futureOpponent)).frame.localLegal = false) ∧
      (∀ ordinal ≤ arrival actual.point,Native.Coupling.Match model.source.code actual.point.source.input
        (prepared.finish actual futureOpponent).source.input (Financial.accountAt actual.point.source.input ordinal)
        (Financial.accountAt (prepared.finish actual futureOpponent).source.input ordinal)) ∧
      HEq ((facade model budget published reference world pastOpponent futureOpponent).readoutAt current .responsibilities)
        (current.tick.generated.projectionOutcome (.component ())) ∧
      HEq current.tick.generated.wholeLedgerWriteBack
        (current.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current.current.visit.current) ∧
      current.tick.nextCurrent = (facade model budget published reference world pastOpponent futureOpponent).process.stateAt
        ((facade model budget published reference world pastOpponent futureOpponent).process.successor current.state) := by
  have covered := actual_coverage_is_generated_without_a_caller_witness model budget published world pastOpponent
  have full := the_original_root_consumes_public_selection_actual_execution_full_finance_and_next model
    (views model budget published) reference (actual model budget published world pastOpponent) futureOpponent covered
  exact ⟨covered,full.1,full.2.1,full.2.2.2.1,full.2.2.2.2.1,full.2.2.2.2.2.1,
    full.2.2.2.2.2.2.2.1,full.2.2.2.2.2.2.2.2.1,full.2.2.2.2.2.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Observed.Transcript
