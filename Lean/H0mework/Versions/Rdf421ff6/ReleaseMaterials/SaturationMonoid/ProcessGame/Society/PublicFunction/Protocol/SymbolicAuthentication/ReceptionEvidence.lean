import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentResponse

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceptionEvidence

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor code) (past : List (EventHistory.Stage (code := code)))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)
  (receiver : Fin code.sites)

abbrev seen (index : Nat) := (StageReception.run vocabulary encoding law start past receiver index).receipts.map
  (fun receipt => (receipt.wire.ballot.cut, receipt.wire.ballot.position))

structure Entry where
  private mk ::
  index : Nat
  row : StageTrace.Record (code := code)
  wire : StageTransport.Wire (code := code)
  reason : AttestationReception.Rejection
  actual : (StageTrace.records start past)[index]? = some row
  incoming : StageReception.incoming vocabulary encoding start past index = some wire
  intended : wire.recipient = receiver
  rejected : StageReception.check vocabulary encoding law start past receiver row
    (seen start past vocabulary encoding law receiver index) wire = .rejected reason

def readAt (index : Nat) : Option (Entry start past vocabulary encoding law receiver) :=
  match actual : (StageTrace.records start past)[index]? with
  | none => none
  | some row => match incoming : StageReception.incoming vocabulary encoding start past index with
    | none => none
    | some wire => if intended : wire.recipient = receiver then
        match rejected : StageReception.check vocabulary encoding law start past receiver row
            (seen start past vocabulary encoding law receiver index) wire with
        | .accepted _ => none
        | .rejected reason => some ⟨index, row, wire, reason, actual, incoming, intended, rejected⟩
      else none

def observed := (List.range past.length).filterMap (readAt start past vocabulary encoding law receiver)

variable (entry : Entry start past vocabulary encoding law receiver)

theorem bounded : entry.index < past.length := by
  have inside := List.getElem?_eq_some_iff.mp entry.actual
  simpa only [StageTrace.record_count] using inside.1

theorem incoming_is_an_actual_delivery : StageReception.delivered entry.row entry.wire.serial = true := by
  have incoming := entry.incoming
  simp only [StageReception.incoming, entry.actual] at incoming
  split at incoming <;> try contradiction
  rename_i event selected
  split at incoming <;> try contradiction
  rename_i serial kind
  have matched : (entry.wire.serial == serial) = true := List.find?_some (p := fun candidate : StageTransport.Wire (code := code) => candidate.serial == serial) (a := entry.wire) incoming
  have address : entry.wire.serial = serial := of_decide_eq_true matched
  simp only [StageReception.delivered, selected, kind, address, beq_self_eq_true]

theorem incoming_has_its_actual_authenticated_origin :
    StageTransport.verify vocabulary encoding start past entry.wire = true :=
  StagePrefix.incoming_is_authenticated start past vocabulary encoding entry.index
    (Nat.le_of_lt (bounded start past vocabulary encoding law receiver entry)) entry.wire entry.incoming

private theorem audit_increases (count last : Nat) (ordered : count ≤ last) :
    (StageReception.run vocabulary encoding law start past receiver count).audit <+:
      (StageReception.run vocabulary encoding law start past receiver last).audit := by
  induction last, ordered using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ last _ ih =>
    apply ih.trans
    simp only [StageReception.run, StageReception.receive]
    split
    · exact List.prefix_refl _
    · exact List.prefix_append _ _

theorem the_rejection_is_in_its_actual_audit :
    (entry.row.cursor.cut, some entry.wire, .rejected entry.reason) ∈
      (StageReception.run vocabulary encoding law start past receiver past.length).audit := by
  have now : (entry.row.cursor.cut, some entry.wire, .rejected entry.reason) ∈
      (StageReception.run vocabulary encoding law start past receiver (entry.index + 1)).audit := by
    simp only [StageReception.run, StageReception.receive, entry.actual, entry.incoming, entry.rejected]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  exact (audit_increases start past vocabulary encoding law receiver _ _
    (by have limit := bounded start past vocabulary encoding law receiver entry; omega)).subset now

-- Extension replays the same receive prefix; no verdict is reconstructed from an arbitrary status.
theorem the_rejection_survives_actual_extension (more : List (EventHistory.Stage (code := code))) :
    (entry.row.cursor.cut, some entry.wire, .rejected entry.reason) ∈
      (StageReception.run vocabulary encoding law start (past ++ more) receiver (past ++ more).length).audit := by
  have old := the_rejection_is_in_its_actual_audit start past vocabulary encoding law receiver entry
  rw [← StagePrefix.run_at start past more vocabulary encoding law receiver past.length (Nat.le_refl _)] at old
  exact (audit_increases start (past ++ more) vocabulary encoding law receiver _ _ (by simp)).subset old

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceptionEvidence
