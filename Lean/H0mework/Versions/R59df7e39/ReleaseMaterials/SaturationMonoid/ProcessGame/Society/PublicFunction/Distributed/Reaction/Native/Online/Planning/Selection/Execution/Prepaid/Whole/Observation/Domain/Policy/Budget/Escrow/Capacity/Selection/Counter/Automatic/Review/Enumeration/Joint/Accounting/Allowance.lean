import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Reference
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Allowance
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}
  {source : SourceQuota.Generated prepared} {catalogue : SourceQuota.Catalogue source.snapshot}
  {all : Candidates source catalogue}

variable (items : List (Report all))
def parentBound := (Machine.initial items).rank items
def tailBound := items.length*((axes all).length+2)+Machine.ceiling items+3
def required := parentBound items+tailBound items

theorem parent_history_spends_at_most_its_source_rank {before after : Machine.State items} {work}
    (history : Machine.LedgerTrace items before after work) : work.length+after.rank items ≤ before.rank items := by
  induction history with
  | nil => simp
  | step actual later ih =>
    have progress := Machine.each_step_decreases_rank items actual
    simp only [List.length_cons]
    omega

theorem actual_parent_work_is_bounded (units : Nat) :
    (Machine.execute items units (Machine.initial items)).work.length ≤ parentBound items := by
  have bounded := parent_history_spends_at_most_its_source_rank items (Machine.execute items units (Machine.initial items)).history
  dsimp only [parentBound]
  omega

theorem pool_length : (candidates items).length ≤ items.length := by
  have small := List.length_filterMap_le (fun row : Row all => row.2.accept?) (directory items)
  simpa only [candidates,directory,List.length_map] using small

theorem actual_tail_initial_rank_is_bounded (position : Nat) (parent : Machine.State items) :
    (Reference.initial items position parent).rank items position ≤ tailBound items := by
  cases parent with
  | reading => exact Nat.zero_le _
  | searching rows complete pool pooled current =>
    have small : pool.length ≤ items.length := by rw [pooled];exact pool_length items
    have first := Nat.mul_le_mul_right ((axes all).length+2) small
    have a := Nat.mul_le_mul_right (2*(axes all).length+3) small
    have b := Nat.mul_le_mul small (Nat.add_le_add_right (Nat.add_le_add_left a 1) 2)
    dsimp only [Reference.initial,Reference.fromCursor,Reference.State.rank,tailBound,Refinement.searchBound,Machine.ceiling]
    omega

def parentFor {prepared : Prepared input} : (menu : DomainResult prepared) → ReportsFor menu → Nat
  | .empty ..,_ | .blocked ..,_ => 0
  | .ready ..,items => parentBound items
def tailFor {prepared : Prepared input} : (menu : DomainResult prepared) → ReportsFor menu → Nat
  | .empty ..,_ | .blocked ..,_ => 0
  | .ready ..,items => tailBound items
def requiredFor {prepared : Prepared input} (menu : DomainResult prepared) (items : ReportsFor menu) := parentFor menu items+tailFor menu items

theorem parent_work_bound {prepared : Prepared input} (menu : DomainResult prepared) (items : ReportsFor menu) (units : Nat) :
    Prepayment.workLength menu items (Prepayment.runFor menu items units) ≤ parentFor menu items := by
  cases menu with
  | empty | blocked => exact Nat.le_refl _
  | ready => exact actual_parent_work_is_bounded _ units

def finishedFor {prepared : Prepared input} : (menu : DomainResult prepared) → (items : ReportsFor menu) → {units : Nat} →
    {parent : Prepayment.WorkFor menu items units} → {position capacity : Nat} → Reference.Payment.WorkFor menu items parent position capacity → Bool
  | .empty ..,_ ,_,_,_,_,_ | .blocked ..,_ ,_,_,_,_,_ => true
  | .ready ..,items,_,_,position,_,tail => tail.endpoint.stopped items position

theorem generated_parent_is_finished {prepared : Prepared input} (menu : DomainResult prepared) (items : ReportsFor menu) (units : Nat)
    (enough : parentFor menu items ≤ units) : Prepayment.finishedFor menu items (Prepayment.runFor menu items units) = true := by
  cases menu with
  | empty | blocked => rfl
  | ready => exact Machine.source_rank_completes _ units _ enough

theorem generated_tail_is_finished {prepared : Prepared input} (menu : DomainResult prepared) (items : ReportsFor menu) {units : Nat}
    (parent : Prepayment.WorkFor menu items units) (position capacity : Nat) (enough : tailFor menu items ≤ capacity) :
    finishedFor menu items (Reference.Payment.runFor menu items parent position capacity) = true := by
  cases menu with
  | empty | blocked => rfl
  | ready =>
    exact Reference.sufficient_source_rank_stops _ position capacity _ ((actual_tail_initial_rank_is_bounded _ position parent.endpoint).trans enough)

theorem same_paid_amount_finishes_parent_and_tail {units position : Nat} (made : Reference.Payment.Funded prepared units position)
    (enough : requiredFor made.parent.body.menu made.parent.body.reports ≤ units) :
    made.parent.finished = true ∧ finishedFor made.parent.body.menu made.parent.body.reports made.tail = true := by
  have spent : made.parent.spent ≤ parentFor made.parent.body.menu made.parent.body.reports := by
    dsimp only [Prepayment.Started.spent]
    rw [made.parent.run_generated]
    exact parent_work_bound _ _ units
  have balance := made.parent.consumed_or_retained
  have head : parentFor made.parent.body.menu made.parent.body.reports ≤ units := by dsimp only [requiredFor] at enough;omega
  have tail : tailFor made.parent.body.menu made.parent.body.reports ≤ made.parent.unused := by dsimp only [requiredFor] at enough;omega
  constructor
  · dsimp only [Prepayment.Started.finished]
    rw [made.parent.run_generated]
    exact generated_parent_is_finished _ _ units head
  · rw [made.tail_generated]
    exact generated_tail_is_finished _ _ made.parent.run position made.parent.unused tail

-- The estimate reads the domain generated after this exact quoted payment, not an executed search.
structure Shape (prepared : Prepared input) (units : Nat) where
  private mk ::
  funding : EscrowBudget.Funding prepared units
  funding_generated : funding = EscrowBudget.reserve prepared units
  body : Record funding.installed
  body_generated : body = Joint.build funding.installed

def describe (prepared : Prepared input) (units : Nat) : Shape prepared units :=
  let funding := EscrowBudget.reserve prepared units
  ⟨funding,rfl,Joint.build funding.installed,rfl⟩
def Shape.amount {units : Nat} (shape : Shape prepared units) := requiredFor shape.body.menu shape.body.reports

theorem generated_shape_is_the_actual_post_payment_requirement {units position : Nat}
    (shape : Shape prepared units) (made : Reference.Payment.Funded prepared units position) :
    shape.amount = requiredFor made.parent.body.menu made.parent.body.reports := by
  have sameFunding := shape.funding_generated.trans made.parent.funding_generated.symm
  rw [Shape.amount,shape.body_generated,made.parent.body_generated]
  exact congrArg (fun funding : EscrowBudget.Funding prepared units =>
    let body := Joint.build funding.installed
    requiredFor body.menu body.reports) sameFunding

theorem quoted_source_bound_finishes_the_actual_execution {units position : Nat} (shape : Shape prepared units)
    (enough : shape.amount ≤ units) (made : Reference.Payment.Funded prepared units position) :
    made.parent.finished = true ∧ finishedFor made.parent.body.menu made.parent.body.reports made.tail = true := by
  apply same_paid_amount_finishes_parent_and_tail made
  rw [←generated_shape_is_the_actual_post_payment_requirement shape made]
  exact enough
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Allowance

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Allowance
namespace Description
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {units : Nat}
private theorem canonical (shape : Shape prepared units) : shape = describe prepared units := by
  rcases shape with ⟨funding,generated,body,bodyGenerated⟩
  cases generated;cases bodyGenerated;rfl
structure Output (prepared : Prepared input) (units : Nat) where
  private mk ::
  shape : Shape prepared units
  source : shape = describe prepared units
  amount : Nat
  amount_exact : amount = shape.amount
inductive State (prepared : Prepared input) (units : Nat) where
  | funding (cursor : EscrowBudget.Acquisition.State prepared units)
  | body (funding : EscrowBudget.Funding prepared units) (generated : funding = EscrowBudget.reserve prepared units)
      (cursor : Joint.BodyAcquisition.State funding.installed)
  | measuring (shape : Shape prepared units) (generated : shape = describe prepared units)
  | finished (output : Output prepared units)
def initial (prepared : Prepared input) (units : Nat) : State prepared units := .funding (EscrowBudget.Acquisition.initial prepared units)
inductive Event (prepared : Prepared input) (units : Nat) where
  | funding (event : EscrowBudget.Acquisition.Event prepared units)
  | source (funding : EscrowBudget.Funding prepared units) (generated : funding = EscrowBudget.reserve prepared units)
  | body (funding : EscrowBudget.Funding prepared units) (event : Joint.BodyAcquisition.Event funding.installed)
  | described (shape : Shape prepared units) (generated : shape = describe prepared units)
  | measured (output : Output prepared units)
def move : State prepared units → Option (State prepared units × Event prepared units)
  | .funding (.finished funding generated) => some (.body funding generated .opening,.source funding generated)
  | .funding cursor@(.reading ..) => match _actual : EscrowBudget.Acquisition.move cursor with
    | none => none
    | some (after,event) => some (.funding after,.funding event)
  | .body funding generated (.finished record actual) =>
      let shape : Shape prepared units := ⟨funding,generated,record,actual⟩
      some (.measuring shape (canonical shape),.described shape (canonical shape))
  | .body funding generated cursor@(.opening)
  | .body funding generated cursor@(.reporting ..) => match _actual : Joint.BodyAcquisition.move cursor with
    | none => none
    | some (after,event) => some (.body funding generated after,.body funding event)
  | .measuring shape generated =>
      let output : Output prepared units := ⟨shape,generated,shape.amount,rfl⟩
      some (.finished output,.measured output)
  | .finished .. => none

def bodyRank (prepared : Prepared input) (units : Nat) :=
  (Joint.BodyAcquisition.State.opening (prepared := (EscrowBudget.reserve prepared units).installed)).rank
def State.rank : State prepared units → Nat
  | .funding cursor => cursor.rank+bodyRank prepared units+3
  | .body _ _ cursor => cursor.rank+2
  | .measuring .. => 1
  | .finished .. => 0
def State.done : State prepared units → Bool | .finished .. => true | _ => false
theorem progress {before after : State prepared units} {event : Event prepared units}
    (actual : move before = some (after,event)) : after.rank < before.rank := by
  cases before with
  | funding cursor =>
      cases cursor with
      | finished funding generated =>
          dsimp only [move] at actual;cases Option.some.inj actual
          subst funding
          simp only [State.rank,EscrowBudget.Acquisition.State.rank,bodyRank];omega
      | reading =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step;cases Option.some.inj actual
            have less := EscrowBudget.Acquisition.progress step
            simp only [State.rank];omega
  | body funding generated cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,Joint.BodyAcquisition.State.rank];omega
      | opening =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := Joint.BodyAcquisition.progress step
            simp only [State.rank];omega
      | reporting =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := Joint.BodyAcquisition.progress step
            simp only [State.rank];omega
  | measuring => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank];omega
  | finished => cases actual

theorem no_move_iff_done (before : State prepared units) : move before = none ↔ before.done = true := by
  cases before with
  | funding cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | reading cached remaining conserved => cases remaining <;> simp [move,EscrowBudget.Acquisition.move,State.done]
  | body funding generated cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | opening | reporting =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (Joint.BodyAcquisition.no_move_iff_done _).mp stopped;cases done)
            | simp
  | measuring | finished => simp [move,State.done]
end Description
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Allowance

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Allowance
namespace MenuDescription
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {units : Nat}
private theorem canonical (shape : Shape prepared units) : shape = describe prepared units := by
  rcases shape with ⟨funding,generated,body,bodyGenerated⟩
  cases generated;cases bodyGenerated;rfl
structure Output (prepared : Prepared input) (units : Nat) where
  private mk ::
  shape : Shape prepared units
  source : shape = describe prepared units
  amount : Nat
  amount_exact : amount = shape.amount
inductive State (prepared : Prepared input) (units : Nat) where
  | funding (cursor : EscrowBudget.Acquisition.State prepared units)
  | body (funding : EscrowBudget.Funding prepared units) (generated : funding = EscrowBudget.reserve prepared units)
      (cursor : Joint.MenuBodyAcquisition.State funding.installed)
  | measuring (shape : Shape prepared units) (generated : shape = describe prepared units)
  | finished (output : Output prepared units)
def initial (prepared : Prepared input) (units : Nat) : State prepared units := .funding (EscrowBudget.Acquisition.initial prepared units)
inductive Event (prepared : Prepared input) (units : Nat) where
  | funding (event : EscrowBudget.Acquisition.Event prepared units)
  | source (funding : EscrowBudget.Funding prepared units) (generated : funding = EscrowBudget.reserve prepared units)
  | body (funding : EscrowBudget.Funding prepared units) (event : Joint.MenuBodyAcquisition.Event funding.installed)
  | described (shape : Shape prepared units) (generated : shape = describe prepared units)
  | measured (output : Output prepared units)
def move : State prepared units → Option (State prepared units × Event prepared units)
  | .funding (.finished funding generated) => some (.body funding generated .opening,.source funding generated)
  | .funding cursor@(.reading ..) => match _actual : EscrowBudget.Acquisition.move cursor with
    | none => none
    | some (after,event) => some (.funding after,.funding event)
  | .body funding generated (.finished record actual) =>
      let shape : Shape prepared units := ⟨funding,generated,record,actual⟩
      some (.measuring shape (canonical shape),.described shape (canonical shape))
  | .body funding generated cursor@(.opening)
  | .body funding generated cursor@(.menu ..)
  | .body funding generated cursor@(.reporting ..) => match _actual : Joint.MenuBodyAcquisition.move cursor with
    | none => none
    | some (after,event) => some (.body funding generated after,.body funding event)
  | .measuring shape generated =>
      let output : Output prepared units := ⟨shape,generated,shape.amount,rfl⟩
      some (.finished output,.measured output)
  | .finished .. => none

def bodyRank (prepared : Prepared input) (units : Nat) :=
  (Joint.MenuBodyAcquisition.State.opening (prepared := (EscrowBudget.reserve prepared units).installed)).rank
def State.rank : State prepared units → Nat
  | .funding cursor => cursor.rank+bodyRank prepared units+3
  | .body _ _ cursor => cursor.rank+2
  | .measuring .. => 1
  | .finished .. => 0
def State.done : State prepared units → Bool | .finished .. => true | _ => false
theorem progress {before after : State prepared units} {event : Event prepared units}
    (actual : move before = some (after,event)) : after.rank < before.rank := by
  cases before with
  | funding cursor =>
      cases cursor with
      | finished funding generated =>
          dsimp only [move] at actual;cases Option.some.inj actual
          subst funding
          simp only [State.rank,EscrowBudget.Acquisition.State.rank,bodyRank];omega
      | reading =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step;cases Option.some.inj actual
            have less := EscrowBudget.Acquisition.progress step
            simp only [State.rank];omega
  | body funding generated cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,Joint.MenuBodyAcquisition.State.rank];omega
      | opening =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := Joint.MenuBodyAcquisition.progress step
            simp only [State.rank];omega
      | reporting =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := Joint.MenuBodyAcquisition.progress step
            simp only [State.rank];omega
      | menu =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := Joint.MenuBodyAcquisition.progress step
            simp only [State.rank];omega
  | measuring => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank];omega
  | finished => cases actual

theorem no_move_iff_done (before : State prepared units) : move before = none ↔ before.done = true := by
  cases before with
  | funding cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | reading cached remaining conserved => cases remaining <;> simp [move,EscrowBudget.Acquisition.move,State.done]
  | body funding generated cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | opening | menu | reporting =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (Joint.MenuBodyAcquisition.no_move_iff_done _).mp stopped;cases done)
            | simp
  | measuring | finished => simp [move,State.done]
end MenuDescription
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Allowance

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Allowance
namespace CandidateDescription
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {units : Nat}
private theorem canonical (shape : Shape prepared units) : shape = describe prepared units := by
  rcases shape with ⟨funding,generated,body,bodyGenerated⟩
  cases generated;cases bodyGenerated;rfl
structure Output (prepared : Prepared input) (units : Nat) where
  private mk ::
  shape : Shape prepared units
  source : shape = describe prepared units
  amount : Nat
  amount_exact : amount = shape.amount
inductive State (prepared : Prepared input) (units : Nat) where
  | funding (cursor : EscrowBudget.Acquisition.State prepared units)
  | body (funding : EscrowBudget.Funding prepared units) (generated : funding = EscrowBudget.reserve prepared units)
      (cursor : Joint.CandidateBodyAcquisition.State funding.installed)
  | measuring (shape : Shape prepared units) (generated : shape = describe prepared units)
  | finished (output : Output prepared units)
def initial (prepared : Prepared input) (units : Nat) : State prepared units := .funding (EscrowBudget.Acquisition.initial prepared units)
inductive Event (prepared : Prepared input) (units : Nat) where
  | funding (event : EscrowBudget.Acquisition.Event prepared units)
  | source (funding : EscrowBudget.Funding prepared units) (generated : funding = EscrowBudget.reserve prepared units)
  | body (funding : EscrowBudget.Funding prepared units) (event : Joint.CandidateBodyAcquisition.Event funding.installed)
  | described (shape : Shape prepared units) (generated : shape = describe prepared units)
  | measured (output : Output prepared units)
def move : State prepared units → Option (State prepared units × Event prepared units)
  | .funding (.finished funding generated) => some (.body funding generated .opening,.source funding generated)
  | .funding cursor@(.reading ..) => match _actual : EscrowBudget.Acquisition.move cursor with
    | none => none
    | some (after,event) => some (.funding after,.funding event)
  | .body funding generated (.finished record actual) =>
      let shape : Shape prepared units := ⟨funding,generated,record,actual⟩
      some (.measuring shape (canonical shape),.described shape (canonical shape))
  | .body funding generated cursor@(.opening)
  | .body funding generated cursor@(.menu ..)
  | .body funding generated cursor@(.reporting ..) => match _actual : Joint.CandidateBodyAcquisition.move cursor with
    | none => none
    | some (after,event) => some (.body funding generated after,.body funding event)
  | .measuring shape generated =>
      let output : Output prepared units := ⟨shape,generated,shape.amount,rfl⟩
      some (.finished output,.measured output)
  | .finished .. => none

def bodyRank (prepared : Prepared input) (units : Nat) :=
  (Joint.CandidateBodyAcquisition.State.opening (prepared := (EscrowBudget.reserve prepared units).installed)).rank
def State.rank : State prepared units → Nat
  | .funding cursor => cursor.rank+bodyRank prepared units+3
  | .body _ _ cursor => cursor.rank+2
  | .measuring .. => 1
  | .finished .. => 0
def State.done : State prepared units → Bool | .finished .. => true | _ => false
theorem progress {before after : State prepared units} {event : Event prepared units}
    (actual : move before = some (after,event)) : after.rank < before.rank := by
  cases before with
  | funding cursor =>
      cases cursor with
      | finished funding generated =>
          dsimp only [move] at actual;cases Option.some.inj actual
          subst funding
          simp only [State.rank,EscrowBudget.Acquisition.State.rank,bodyRank];omega
      | reading =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step;cases Option.some.inj actual
            have less := EscrowBudget.Acquisition.progress step
            simp only [State.rank];omega
  | body funding generated cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,Joint.CandidateBodyAcquisition.State.rank];omega
      | opening =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := Joint.CandidateBodyAcquisition.progress step
            simp only [State.rank];omega
      | reporting =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := Joint.CandidateBodyAcquisition.progress step
            simp only [State.rank];omega
      | menu =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step
            cases Option.some.inj actual
            have less := Joint.CandidateBodyAcquisition.progress step
            simp only [State.rank];omega
  | measuring => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank];omega
  | finished => cases actual

theorem no_move_iff_done (before : State prepared units) : move before = none ↔ before.done = true := by
  cases before with
  | funding cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | reading cached remaining conserved => cases remaining <;> simp [move,EscrowBudget.Acquisition.move,State.done]
  | body funding generated cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | opening | menu | reporting =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (Joint.CandidateBodyAcquisition.no_move_iff_done _).mp stopped;cases done)
            | simp
  | measuring | finished => simp [move,State.done]
end CandidateDescription
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Allowance
