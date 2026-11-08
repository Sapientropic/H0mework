import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommunicationObservation

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptObservation

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}


theorem records_take (start : Cursor code) (stages : List (EventHistory.Stage (code := code))) (count : Nat) :
    StageTrace.records start (stages.take count) = (StageTrace.records start stages).take count := by
  induction stages generalizing start count with
  | nil => simp [StageTrace.records]
  | cons stage tail ih =>
    rcases stage with ⟨rule, rival⟩
    cases count with
    | zero => rfl
    | succ count => simp only [List.take_succ_cons, StageTrace.records, ih]

variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)

theorem ledger_equal {left right : List (StageTrace.Record (code := code))}
    (same : CommunicationObservation.Related left right) :
    left.flatMap (RequestLocalDomain.statements vocabulary) = right.flatMap (RequestLocalDomain.statements vocabulary) := by
  induction same with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.flatMap_cons, ih,
      RequestLocalDomain.statements_depend_only_on_actual_material_and_ownership vocabulary _ _
        head.cut head.before head.submitted head.activation]

variable (start : Cursor code) (first second : List (EventHistory.Stage (code := code)))
  (same : CommunicationObservation.Related (StageTrace.records start first) (StageTrace.records start second))

include same in
theorem prior_equal (wire : StageTransport.Wire (code := code)) :
    RequestReadback.priorStatements vocabulary start first wire = RequestReadback.priorStatements vocabulary start second wire := by
  unfold RequestReadback.priorStatements RequestAttestation.ledger
  rw [records_take, records_take]
  exact ledger_equal vocabulary (CommunicationObservation.take_related same _)

include same in
theorem inspect_equal (receiver : Fin code.sites) (confirmation : StageReception.Receipt (code := code)) :
    RequestReadback.inspect vocabulary start first receiver confirmation = RequestReadback.inspect vocabulary start second receiver confirmation := by
  unfold RequestReadback.inspect RequestReadback.sourceBody
  rw [prior_equal vocabulary start first second same]
  split <;> try rfl
  split <;> try rfl
  refine CommunicationObservation.lookup_congr (Value := RequestReadback.Outcome (code := code)) same confirmation.index (.rejected .missingDeliveryRow) _ _ ?_
  intro a b related
  rw [related.after]

include same in
theorem produce_equal (receiver : Fin code.sites) (count : Nat) :
    RequestReadback.produce vocabulary encoding law start first receiver count =
      RequestReadback.produce vocabulary encoding law start second receiver count := by
  have reception := CommunicationObservation.run_equal vocabulary encoding start start first second same law receiver count
  have inspections : RequestReadback.inspect vocabulary start first receiver = RequestReadback.inspect vocabulary start second receiver := by
    funext confirmation
    exact inspect_equal vocabulary start first second same receiver confirmation
  unfold RequestReadback.produce
  rw [reception, inspections]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptObservation
