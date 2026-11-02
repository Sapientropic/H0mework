import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Receipt
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Material.Execution
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Driving.History

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Feedback
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix
open PublicFunction.Protocol.SymbolicAuthentication
open Publication.Learning Publication.Learning.Paid

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

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
  (record : Reservation.Receipt.Published model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law)
  (initial : List (View (code := model.source.code)))

abbrev material := Receipt.material model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record
abbrev seed := Material.Execution.seed model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law
  (material model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) initial

theorem the_received_reservation_keeps_its_source_generated_fee_and_learning_slot :
    (Driving.Round.prepared (seed model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial)).Booked
      (Paid.requestedRule receiver quote record.selection.supported) := by
  let start := seed model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial
  have fromSource := Service.the_paid_cache_generates_its_own_next_fee_and_learning_reservation
    model domain original reference worker receiver quote quotas slots point rival ordinal record.selection initial
  have booked : start.Booked (Paid.requestedRule receiver quote record.selection.supported) := fromSource
  have retained : start.programme.controls.take (start.past ++ [Paid.requestedRule receiver quote record.selection.supported]).length =
      start.past ++ [Paid.requestedRule receiver quote record.selection.supported] := by
    simpa only [List.length_append,List.length_singleton] using booked.2.2
  have padded := Padding.preserves_prefix original start.programme _ retained
  refine ⟨booked.1,booked.2.1,?_⟩
  change (Padding.controls original start.programme).take (start.past.length+1) = start.past ++ [Paid.requestedRule receiver quote record.selection.supported]
  simpa only [List.length_append,List.length_singleton] using padded

theorem the_historical_receipt_does_not_empty_the_actual_planning_domain
    (covered : Knowledge.Contains initial point) :
    (Driving.Round.prepared (seed model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial)).beliefs.isEmpty = false := by
  have actual := Material.Observation.the_received_reading_generates_an_origin_preserving_posterior model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law
    (material model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record) initial covered
  obtain ⟨view,inside,_⟩ := actual
  let start := seed model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial
  have present : view ∈ start.beliefs := inside
  change start.beliefs.isEmpty = false
  cases cached : start.beliefs with
  | nil => rw [cached] at present;cases present
  | cons => rfl

theorem the_first_batch_keeps_the_original_registered_resource_request
    (covered : Knowledge.Contains initial point) :
    Driving.Round.quoted (seed model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial) quote = quote := by
  have inhabited := the_historical_receipt_does_not_empty_the_actual_planning_domain model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial covered
  unfold Driving.Round.quoted Paid.Schedule.request
  rw [inhabited]
  rfl

theorem the_first_reserved_fee_is_really_attempted
    (covered : Knowledge.Contains initial point) :
    (Driving.Round.service (seed model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial) receiver quote point rival).rules =
      [Paid.requestedRule receiver quote record.selection.supported] := by
  have booked := the_received_reservation_keeps_its_source_generated_fee_and_learning_slot model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial
  unfold Driving.Round.service
  rw [the_first_batch_keeps_the_original_registered_resource_request model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record initial covered]
  unfold Paid.turn
  rw [dif_pos record.selection.supported,dif_pos booked]
  split <;> rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Feedback
