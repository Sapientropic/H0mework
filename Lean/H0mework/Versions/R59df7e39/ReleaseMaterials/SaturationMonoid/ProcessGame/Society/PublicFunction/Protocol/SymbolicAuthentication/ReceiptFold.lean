import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AttestationReception

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptFold

open Distributed Reaction Reaction.Feedback

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (input : Input source.code) (cut : Nat)
  (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code)
  (rival : Opponent source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : AttestationTransport.Encoding source) (law : AttestationReception.ReceptionLaw source)

theorem before_is_feedback (empty : source.continuation = []) (n : Nat) :
    (AttestationTransport.execution source input cut protocol rival n).before =
      (AttestationTransport.state source input cut protocol rival n).current := by
  exact ((OwnedAttestation.actual source input cut protocol rival).feedback_body_reads_the_actual_local_current
    (AttestationTransport.actualInput source input cut protocol rival) rfl empty (cut + n)).symm

theorem word_is_feedback (empty : source.continuation = []) (n : Nat) :
    (AttestationTransport.execution source input cut protocol rival n).submitted =
      Feedback.word source.code ((OwnedAttestation.actual source input cut protocol rival).feedbackPolicy (cut + n))
        (AttestationTransport.actualInput source input cut protocol rival)
        (AttestationTransport.state source input cut protocol rival n) := by
  exact (OwnedAttestation.actual source input cut protocol rival).feedback_word_is_actual
    (AttestationTransport.actualInput source input cut protocol rival) rfl empty (cut + n)

def baseVerdict (receiver : Fin source.code.sites) (n : Nat) : AttestationReception.Verdict source :=
  match AttestationReception.incoming source input cut protocol rival vocabulary encoding n with
  | none => .rejected .missingWire
  | some wire => AttestationReception.check source input cut protocol rival vocabulary encoding law receiver n [] wire

def step (previous : List (AttestationReception.Receipt source))
    (item : Nat × AttestationReception.Verdict source) : List (AttestationReception.Receipt source) :=
  match item.2 with
  | .rejected _ => previous
  | .accepted wire =>
      if (wire.ballot.cut, wire.ballot.position) ∈ previous.map (fun receipt => (receipt.wire.ballot.cut, receipt.wire.ballot.position))
      then previous else previous ++ [⟨wire, item.1⟩]

theorem check_factors_seen (receiver : Fin source.code.sites) (n : Nat) (seen : List (Nat × Nat))
    (wire : AttestationTransport.Wire source) :
    AttestationReception.check source input cut protocol rival vocabulary encoding law receiver n seen wire =
      match AttestationReception.check source input cut protocol rival vocabulary encoding law receiver n [] wire with
      | .rejected reason => .rejected reason
      | .accepted body => if (body.ballot.cut, body.ballot.position) ∈ seen then .rejected .duplicate else .accepted body := by
  simp only [AttestationReception.check, List.not_mem_nil, if_false]
  split_ifs <;> simp_all

/-- The source check at each cut is paid once; the original run keeps its full
audit. This fold is a proved receipt projection, never a new incoming producer. -/
theorem receipts_are_fold (receiver : Fin source.code.sites) (count : Nat) :
    (AttestationReception.run source input cut protocol rival vocabulary encoding law receiver count).receipts =
      ((List.range count).map (fun n => (n, baseVerdict source input cut protocol rival vocabulary encoding law receiver n))).foldl (step source) [] := by
  induction count with
  | zero => rfl
  | succ n ih =>
    conv_rhs => rw [List.range_succ, List.map_append, List.map_singleton, List.foldl_append]
    change (AttestationReception.receive source input cut protocol rival vocabulary encoding law receiver n
      (AttestationReception.run source input cut protocol rival vocabulary encoding law receiver n)).receipts =
        step source (((List.range n).map (fun k => (k, baseVerdict source input cut protocol rival vocabulary encoding law receiver k))).foldl (step source) [])
          (n, baseVerdict source input cut protocol rival vocabulary encoding law receiver n)
    conv_rhs => rw [← ih]
    unfold AttestationReception.receive baseVerdict step
    cases chosen : AttestationReception.incoming source input cut protocol rival vocabulary encoding n with
    | none => rfl
    | some wire =>
      dsimp only
      rw [check_factors_seen source input cut protocol rival vocabulary encoding law receiver n _ wire]
      cases verdict : AttestationReception.check source input cut protocol rival vocabulary encoding law receiver n [] wire with
      | rejected reason => rfl
      | accepted body => dsimp only; split_ifs <;> rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptFold
