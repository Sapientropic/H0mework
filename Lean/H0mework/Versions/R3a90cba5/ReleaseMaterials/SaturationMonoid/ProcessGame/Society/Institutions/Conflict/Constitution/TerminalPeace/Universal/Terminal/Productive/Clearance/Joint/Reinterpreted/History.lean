import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Dispatch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted

open Capitalism.Universal.Source.Program
open Reparation (Key)
open Reparation.Actual (Script JointReceipt)
open FixedPoint (RevisionAnswers reviseProgramme)
open FixedPoint.OpenPeace.Operational (RepeatCode)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {loss : Reparation.Actual.Occurrence seed community} {front : Script Party Good Port Technology Instrument}

variable (before : Current loss front)

inductive Submission
  | payment (key : Key Party Good) (quantity : ℚ)
  | production (offer : ProductionOffer Party Good Port Technology Instrument)
      (code : RepeatCode (reviseProgramme before.programme offer) before.physical.raw)

inductive Event
  | paid {answers : DeliveryAnswers Party Good Port Technology Instrument} {key : Key Party Good} {quantity : ℚ}
      (actual : PaidWrite before answers key quantity)
  | revised {approvals : RevisionAnswers Party Good Port Technology Instrument}
      {offer : ProductionOffer Party Good Port Technology Instrument} (actual : TrialWrite before approvals offer)
  | refused {Issue : Type} (actual : Refused before Issue)

namespace Event

variable {before} (event : Event before)

def next : Current loss front :=
  match event with
  | .paid actual => actual.next
  | .revised actual => actual.period.next
  | .refused actual => actual.next

theorem next_ordinal : event.next.ordinal = before.ordinal + 1 := by
  cases event with
  | paid actual => exact actual.ordinal
  | revised actual => exact actual.period.ownClock
  | refused actual => exact actual.exactOrdinal

theorem balance_le (key : Key Party Good) : liveBalance event.next key ≤ liveBalance before key := by
  cases event with
  | @paid _ _ amount actual =>
    change liveBalance actual.next key ≤ _
    rw [actual.balances]
    have positive : 0 < amount := actual.amount ▸ actual.receipt.positive
    apply sub_le_self
    split
    · exact positive.le
    · exact le_rfl
  | revised actual =>
    change dueFor key actual.period.next.ledger.stack.balances ≤ _
    rw [actual.period.rows]
  | refused actual =>
    change dueFor key actual.next.ledger.stack.balances ≤ _
    rw [actual.keepsRows]

def receipt : Option ((key : Key Party Good) × JointReceipt seed key) :=
  match event with
  | .paid actual => some ⟨_, actual.receipt⟩
  | _ => none

theorem receipt_stamp {found : (key : Key Party Good) × JointReceipt seed key}
    (actual : event.receipt = some found) : found.2.address.1 = before.ordinal := by
  cases event with
  | paid paid =>
    have same := Option.some.inj actual
    exact same ▸ paid.receipt_is_stamped_on_its_actual_visit
  | revised | refused => cases actual

end Event

variable [DecidableEq (Request Party Good Port Technology Instrument)]
  (approvals : RevisionAnswers Party Good Port Technology Instrument)
  (answers : DeliveryAnswers Party Good Port Technology Instrument)
  (addresses : List (Party × Good)) (covered : ∀ address, address ∈ addresses)

def dispatch (submission : Submission before) : Event before :=
  match submission with
  | .payment key amount =>
    match pay before answers key amount addresses covered with
    | .inl denied => .refused denied
    | .inr actual => .paid actual
  | .production offer code =>
    match revise before approvals offer code with
    | .inl denied => .refused denied
    | .inr actual => .revised actual

variable (initial : Current loss front) (policy : (n : Nat) → (state : Current loss front) → Submission state)

def history : Nat → Current loss front
  | 0 => initial
  | n + 1 =>
    let reached := history n
    (dispatch reached approvals answers addresses covered (policy n reached)).next

abbrev eventAt (n : Nat) :=
  let reached := history approvals answers addresses covered initial policy n
  dispatch reached approvals answers addresses covered (policy n reached)

theorem history_ordinal (n : Nat) :
    (history approvals answers addresses covered initial policy n).ordinal = initial.ordinal + n := by
  induction n with
  | zero => rfl
  | succ n earlier =>
    change (eventAt approvals answers addresses covered initial policy n).next.ordinal = _
    rw [Event.next_ordinal]
    rw [earlier, Nat.add_assoc]

theorem every_history_preserves_its_original_addresses (n : Nat) :
    (history approvals answers addresses covered initial policy n).ledger.stack.balances.map Prod.fst =
      initial.ledger.stack.balances.map Prod.fst :=
  (history approvals answers addresses covered initial policy n).origins.trans initial.origins.symm

theorem no_receipt_can_be_booked_again_in_the_same_history {i j : Nat} (later : i < j)
    (receipt : (key : Key Party Good) × JointReceipt seed key)
    (used : (eventAt approvals answers addresses covered initial policy i).receipt = some receipt) :
    (eventAt approvals answers addresses covered initial policy j).receipt ≠ some receipt := by
  intro duplicate
  have first := Event.receipt_stamp _ used
  have second := Event.receipt_stamp _ duplicate
  have equal := first.symm.trans second
  change (history approvals answers addresses covered initial policy i).ordinal =
    (history approvals answers addresses covered initial policy j).ordinal at equal
  rw [history_ordinal, history_ordinal] at equal
  exact (ne_of_lt (Nat.add_lt_add_left later _)) equal

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted
