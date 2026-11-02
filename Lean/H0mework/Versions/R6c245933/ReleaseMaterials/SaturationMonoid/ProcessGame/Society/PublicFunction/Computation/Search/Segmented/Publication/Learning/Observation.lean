import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Runtime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Receipt.Domain

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Observation
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix
open PublicFunction.Protocol.SymbolicAuthentication

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

private theorem record_after_is_the_exact_delivery_prefix (start : Cursor code)
    (stages : List (EventHistory.Stage (code := code))) (index : Nat)
    (row : StageTrace.Record (code := code)) (found : (StageTrace.records start stages)[index]? = some row) :
    row.after = EventStep.seed (EventHistory.execute start (stages.take (index+1))) := by
  induction stages generalizing start index with
  | nil => simp only [StageTrace.records,List.getElem?_nil] at found;cases found
  | cons stage rest ih =>
    rcases stage with ⟨rule,rival⟩
    cases index with
    | zero =>
      simp only [StageTrace.records,List.getElem?_cons_zero] at found
      cases Option.some.inj found
      exact (StageTrace.material_is_the_actual_step start rule rival).1
    | succ index =>
      simp only [StageTrace.records,List.getElem?_cons_succ] at found
      simpa only [List.take_succ_cons,EventHistory.execute] using ih (start.after rule rival) index found

private theorem actual_view_has_the_executed_point (controls : List (Prefix.Rule code))
    (point : View (code := code)) (rival : Opponent code) :
    (Window.Observed.Transcript.actualView controls point rival).point =
      EventHistory.execute point.point (controls.map (fun rule => (rule,rival))) := by
  induction controls generalizing point with
  | nil => rfl
  | cons rule rest ih => exact ih (Evidence.after point rule rival)

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Prefix.Rule model.source.code)
  (reference : Program model.source.code (horizon domain))
  (worker receiver : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (quotas : List Nat) (slots : Nat)
  (point : View (code := model.source.code)) (rival : Opponent model.source.code) (ordinal : Nat)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code))
  (law : StageReception.Law model.source.code)
  (record : Publication.Receipt.Published model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law)

abbrev controls := reserved model original worker quote quotas ++ record.plan.announcements
abbrev delivered := record.receipt.confirmation.index+1
abbrev atDelivery := Window.Observed.Transcript.actualView
  ((controls model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).take
    (delivered model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record)) point rival
abbrev atCommunication := Window.Observed.Transcript.actualView
  (controls model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) point rival

/-- Condition at the real delivery stage, then propagate the unobserved remainder.
The earlier reading is never asserted to equal the final inbox. -/
def posterior (initial : List (View (code := model.source.code))) :=
  let past := controls model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record
  let cut := delivered model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record
  Window.Observed.Transcript.publicViews (past.drop cut)
    (fiber (Window.Observed.Transcript.publicViews (past.take cut) initial) receiver record.receipt.reading)

theorem the_received_reading_is_the_observation_at_its_actual_delivery :
    observation (atDelivery model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) receiver = record.receipt.reading := by
  obtain ⟨_,_,_,_,row,found,reading,_,_⟩ :=
    Publication.Receipt.every_published_address_has_real_paid_communication_and_local_readback
      model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record
  have actual := record_after_is_the_exact_delivery_prefix point.point
    (Publication.Receipt.stages model domain original reference worker receiver quote quotas slots point rival ordinal record.plan)
    record.receipt.confirmation.index row found
  change (EventStep.seed (atDelivery model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).point).frame.inbox receiver = _
  rw [actual_view_has_the_executed_point]
  change row.after = EventStep.seed (EventHistory.execute point.point
    (((controls model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).map
      (fun rule => (rule,rival))).take (delivered model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record))) at actual
  rw [←List.map_take] at actual
  exact (congrArg (fun state : State model.source.code => state.frame.inbox receiver) actual).symm.trans reading.symm

theorem the_received_reading_generates_an_origin_preserving_posterior
    (initial : List (View (code := model.source.code))) (covered : Knowledge.Contains initial point) :
    Knowledge.Contains (posterior model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial)
      (atCommunication model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) := by
  let past := controls model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record
  let cut := delivered model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record
  have early := Window.Observed.Transcript.every_actual_past_keeps_a_representative_in_the_same_public_domain
    (past.take cut) initial point covered rival
  have posteriorCovered := Rolling.Receipt.the_actual_local_record_generates_its_own_covered_planning_domain _ _ early receiver
  rw [the_received_reading_is_the_observation_at_its_actual_delivery model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record] at posteriorCovered
  have later := Window.Observed.Transcript.every_actual_past_keeps_a_representative_in_the_same_public_domain
    (past.drop cut) _ _ posteriorCovered rival
  change Knowledge.Contains _ (Window.Observed.Transcript.actualView past point rival)
  have joined : Window.Observed.Transcript.actualView past point rival =
      Window.Observed.Transcript.actualView (past.drop cut)
        (Window.Observed.Transcript.actualView (past.take cut) point rival) rival := by
    unfold Window.Observed.Transcript.actualView
    rw [←List.foldl_append,List.take_append_drop]
  rw [joined]
  exact later

theorem the_after_receipt_point_is_the_actual_locked_prefix :
    (atCommunication model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).point = Splice.install point.point rival (controls model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) := by
  rw [actual_view_has_the_executed_point]
  have mapped (cursor : Cursor model.source.code) (rules : List (Prefix.Rule model.source.code)) :
      EventHistory.execute cursor (rules.map (fun rule => (rule,rival))) = Splice.install cursor rival rules := by
    induction rules generalizing cursor with
    | nil => rfl
    | cons rule rest ih => exact ih (cursor.after rule rival)
  exact mapped _ _

theorem the_posterior_point_is_the_actual_communication_cut :
    (atCommunication model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record).point =
      Plan.cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal record.plan.announcements.length := by
  rw [actual_view_has_the_executed_point]
  exact Publication.Receipt.the_publication_source_is_an_actual_prefix_of_the_full_selected_source
    model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Observation
