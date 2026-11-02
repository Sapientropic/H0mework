import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Service
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Material.Observation
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestReadback

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Receipt
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open PublicFunction.Protocol.SymbolicAuthentication

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
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



structure Published where
  selection : Reservation.Selection model domain original reference worker receiver quote quotas slots point rival ordinal
  selected : Reservation.select model domain original reference worker receiver quote quotas slots point rival ordinal = some selection
  payload : Material.Payload model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law selection.plan

structure Pending where
  selection : Reservation.Selection model domain original reference worker receiver quote quotas slots point rival ordinal
  selected : Reservation.select model domain original reference worker receiver quote quotas slots point rival ordinal = some selection
  residual : Material.Pending model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law selection.plan

inductive Outcome where
  | noSelectedProgramme (reason : Reservation.Blocked model domain original reference worker receiver quote quotas slots point rival ordinal)
  | pending (residual : Pending model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law)
  | published (record : Published model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law)

def generate : Outcome model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law :=
  match selected : Reservation.select model domain original reference worker receiver quote quotas slots point rival ordinal with
  | none => .noSelectedProgramme (Reservation.obstruction model domain original reference worker receiver quote quotas slots point rival ordinal selected)
  | some selection =>
    match Material.receive model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law selection.plan with
    | .pending residual => .pending ⟨selection,selected,residual⟩
    | .delivered payload => .published ⟨selection,selected,payload⟩

variable (record : Published model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law)

def material : Material.Carrier model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law :=
  ⟨record.selection.plan,record.payload⟩

theorem the_actual_receipt_keeps_the_new_selector_and_original_complete_contract :
    Reservation.select model domain original reference worker receiver quote quotas slots point rival ordinal = some record.selection ∧
    (Segmented.trace model domain original reference worker quote quotas point rival).closingReceipt = some record.payload.closing ∧
    Charge.paid quote model worker record.payload.closing.before rival (Charge.endAt quote model worker record.payload.closing.before rival) ∧
    Publication.Receipt.Addresses model worker quote rival record.payload.closing record.payload.receipt ∧
    Prefix.Contract model domain original (reserved model original worker quote quotas) reference (.selected record.selection.plan.choice) :=
  ⟨record.selected,record.payload.sealed,record.payload.closing.receipt,record.payload.addressed,
    Prefix.every_generated_outcome_has_the_complete_future_contract model domain original (reserved model original worker quote quotas) reference (.selected record.selection.plan.choice)⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Receipt
