import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalAuthenticationRuntime

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommunicationObservation

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

-- Rejected raw callbacks remain in the actual audit. Communication observes their
-- admitted effect; this relation does not identify the original callback records.
structure Same (left right : StageTrace.Record (code := code)) : Prop where
  cut : left.cursor.cut = right.cursor.cut
  before : left.before = right.before
  submitted : left.submitted = right.submitted
  after : left.after = right.after
  activation : StageTrace.activation left = StageTrace.activation right
  outgoing : StageTransport.outgoing left = StageTransport.outgoing right
  admission : StageTransport.admission left = StageTransport.admission right

abbrev Related := List.Forall₂ (Same (code := code))

theorem items_equal {left right : StageTrace.Record (code := code)} (same : Same left right) :
    StageTrace.items left = StageTrace.items right := by
  unfold StageTrace.items
  rw [same.before, same.submitted]

theorem take_related {left right : List (StageTrace.Record (code := code))} (same : Related left right) (count : Nat) :
    Related (left.take count) (right.take count) := by
  induction same generalizing count with
  | nil => simp only [List.take_nil]; exact List.Forall₂.nil
  | cons head tail ih =>
    cases count with
    | zero => exact List.Forall₂.nil
    | succ count => exact List.Forall₂.cons head (ih count)

theorem lookup_congr {Value : Type} {left right : List (StageTrace.Record (code := code))}
    (same : Related left right) (index : Nat) (fallback : Value)
    (first second : StageTrace.Record (code := code) → Value)
    (compatible : ∀ a b, Same a b → first a = second b) :
    (match left[index]? with | none => fallback | some row => first row) =
      (match right[index]? with | none => fallback | some row => second row) := by
  by_cases bounded : index < left.length
  · have other : index < right.length := by rw [← same.length_eq]; exact bounded
    simp only [List.getElem?_eq_getElem bounded, List.getElem?_eq_getElem other]
    exact compatible _ _ (same.get bounded other)
  · have other : ¬ index < right.length := by rw [← same.length_eq]; exact bounded
    rw [List.getElem?_eq_none_iff.mpr (by omega), List.getElem?_eq_none_iff.mpr (by omega)]

theorem find_projection_equal {Value : Type} {left right : List (StageTrace.Record (code := code))}
    (same : Related left right) (p q : StageTrace.Record (code := code) → Bool)
    (first second : StageTrace.Record (code := code) → Value)
    (predicates : ∀ a b, Same a b → p a = q b)
    (values : ∀ a b, Same a b → first a = second b) :
    (left.find? p).map first = (right.find? q).map second := by
  induction same with
  | nil => rfl
  | @cons a b left right head tail ih =>
    simp only [List.find?_cons, predicates a b head]
    split
    · exact congrArg some (values a b head)
    · exact ih

variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code))

theorem ballots_equal {left right : StageTrace.Record (code := code)} (same : Same left right) :
    StageTransport.ballots vocabulary left = StageTransport.ballots vocabulary right := by
  have issued : ∀ position, StageBudget.issued vocabulary left position = StageBudget.issued vocabulary right position := by
    intro position
    simp only [StageBudget.issued, StageBudget.outcome, same.activation, items_equal same,
      OwnedAttestation.classify, same.cut]
  simp only [StageTransport.ballots, same.submitted, issued]

theorem issue_equal {earlier first : List (StageTrace.Record (code := code))}
    (past : Related earlier first) {left right : StageTrace.Record (code := code)} (same : Same left right) :
    StageTransport.issue vocabulary encoding earlier left = StageTransport.issue vocabulary encoding first right := by
  unfold StageTransport.issue
  rw [same.outgoing, same.before, same.after, items_equal same, same.cut]
  split <;> try rfl
  dsimp only
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  rename_i body encoded
  have offsets := find_projection_equal past
    (fun row => decide (body ∈ StageTransport.ballots vocabulary row))
    (fun row => decide (body ∈ StageTransport.ballots vocabulary row))
    (fun row => row.before.frame.word.length) (fun row => row.before.frame.word.length)
    (fun _ _ related => congrArg (fun entries => decide (body ∈ entries)) (ballots_equal vocabulary related))
    (fun _ _ related => congrArg (fun state : State code => state.frame.word.length) related.before)
  cases original : earlier.find? (fun row => decide (body ∈ StageTransport.ballots vocabulary row)) with
  | none =>
    cases replacement : first.find? (fun row => decide (body ∈ StageTransport.ballots vocabulary row)) with
    | none => rfl
    | some row => simp only [original, replacement, Option.map_none, Option.map_some] at offsets; contradiction
  | some origin =>
    cases replacement : first.find? (fun row => decide (body ∈ StageTransport.ballots vocabulary row)) with
    | none => simp only [original, replacement, Option.map_none, Option.map_some] at offsets; contradiction
    | some other =>
      have words := Option.some.inj (by simpa only [original, replacement, Option.map_some] using offsets)
      simp only [words]

variable (left right : Cursor code)
  (first second : List (EventHistory.Stage (code := code)))
  (same : Related (StageTrace.records left first) (StageTrace.records right second))

include same in
theorem issued_at_equal (index : Nat) :
    StageTransport.issuedAt vocabulary encoding left first index =
      StageTransport.issuedAt vocabulary encoding right second index := by
  unfold StageTransport.issuedAt
  apply lookup_congr same index none
  intro a b related
  exact issue_equal vocabulary encoding (take_related same index) related

include same in
theorem wires_equal : StageTransport.wires vocabulary encoding left first = StageTransport.wires vocabulary encoding right second := by
  have length : first.length = second.length := by
    rw [← StageTrace.record_count left first, ← StageTrace.record_count right second]
    exact same.length_eq
  unfold StageTransport.wires
  rw [length]
  apply List.filterMap_congr
  intro index _
  exact issued_at_equal vocabulary encoding left right first second same index

include same in
theorem check_equal (law : StageReception.Law code) (receiver : Fin code.sites)
    {a b : StageTrace.Record (code := code)} (related : Same a b)
    (seen : List (Nat × Nat)) (wire : StageTransport.Wire (code := code)) :
    StageReception.check vocabulary encoding law left first receiver a seen wire =
      StageReception.check vocabulary encoding law right second receiver b seen wire := by
  unfold StageReception.check StageReception.delivered StageReception.matchingPacket StageTransport.verify
  rw [related.admission, related.before, related.cut, items_equal related,
    wires_equal vocabulary encoding left right first second same]

include same in
theorem incoming_equal (index : Nat) :
    StageReception.incoming vocabulary encoding left first index =
      StageReception.incoming vocabulary encoding right second index := by
  have issued : (List.range index).filterMap (StageTransport.issuedAt vocabulary encoding left first) =
      (List.range index).filterMap (StageTransport.issuedAt vocabulary encoding right second) := by
    apply List.filterMap_congr
    intro position _
    exact issued_at_equal vocabulary encoding left right first second same position
  unfold StageReception.incoming
  apply lookup_congr same index none
  intro a b related
  rw [related.admission, issued]

include same in
theorem receive_equal (law : StageReception.Law code) (receiver : Fin code.sites)
    (index : Nat) (previous : StageReception.Receiver (code := code)) :
    StageReception.receive vocabulary encoding law left first receiver index previous =
      StageReception.receive vocabulary encoding law right second receiver index previous := by
  unfold StageReception.receive
  apply lookup_congr same index previous
  intro a b related
  rw [incoming_equal vocabulary encoding left right first second same index]
  have checked := check_equal vocabulary encoding left right first second same law receiver related
  dsimp only
  simp only [checked, related.cut]

include same in
theorem run_equal (law : StageReception.Law code) (receiver : Fin code.sites) (count : Nat) :
    StageReception.run vocabulary encoding law left first receiver count =
      StageReception.run vocabulary encoding law right second receiver count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [StageReception.run, ih]
    exact receive_equal vocabulary encoding left right first second same law receiver count _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommunicationObservation
