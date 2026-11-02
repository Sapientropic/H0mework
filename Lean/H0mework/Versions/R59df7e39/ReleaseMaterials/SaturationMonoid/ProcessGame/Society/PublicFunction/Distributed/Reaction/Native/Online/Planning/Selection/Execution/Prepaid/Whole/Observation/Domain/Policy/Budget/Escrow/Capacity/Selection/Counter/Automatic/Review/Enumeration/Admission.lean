import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Admission.Budget
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Admission
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {source : SourceQuota.Generated prepared}
  {catalogue : SourceQuota.Catalogue source.snapshot} {all : Candidates source catalogue} (owner : Ready all)
abbrev Term := Section owner.release.programme.actual.pool
abbrev Row := PublicPolicy.Row owner.release.programme.actual.pool
abbrev Holds (term : Term owner) (row : Row owner) := PublicPolicy.Holds owner.release.programme.actual.pool term row
abbrev rows := PublicPolicy.rows owner.release.programme.actual.pool
def sourceUnits := Budget.sourceUnits owner

theorem native_work_fits_the_original_paid_source (term : Term owner) (row : Row owner) (inside : row ∈ rows owner) :
    (Work.atom owner.release.programme.actual.pool (.admission term row)).work.length ≤ sourceUnits owner :=
  (Work.atom_work_bound _ _).trans (Budget.atom_budget_fits_the_original_source owner term row inside)

structure Receipt (term : Term owner) (row : Row owner) where
  private mk ::
  allowance : Budget.Quote owner term row
  checked : Work.Check owner.release.programme.actual.pool (Holds owner term row)
  generated : checked = Work.atom owner.release.programme.actual.pool (.admission term row)
  prepaid : Nat
  exact_prepaid : prepaid = allowance.amount
  covered : checked.work.length ≤ prepaid
namespace Receipt
variable {owner} {term : Term owner} {row : Row owner} (made : Receipt owner term row)
def slot (event : Fin made.checked.work.length) : Fin made.prepaid := ⟨event.val,event.isLt.trans_le made.covered⟩
theorem native_work_has_distinct_prepaid_slots : Function.Injective made.slot := by
  intro first second same
  have equal := congrArg (fun slot : Fin made.prepaid => slot.val) same
  exact Fin.ext equal
end Receipt

inductive State (term : Term owner) where
  | waiting (todo : List (Row owner)) (within : ∀ row ∈ todo,row ∈ rows owner)
      (passed : (∀ row ∈ todo,Holds owner term row) → Accepted owner.release.programme.actual.pool term)
  | finishing (row : Row owner) (rest : List (Row owner))
      (within : ∀ probe ∈ row::rest,probe ∈ rows owner)
      (passed : (∀ probe ∈ row::rest,Holds owner term probe) → Accepted owner.release.programme.actual.pool term)
      (cursor : Budget.Cursor owner term row)
  | quoting (row : Row owner) (rest : List (Row owner))
      (within : ∀ probe ∈ row::rest,probe ∈ rows owner)
      (passed : (∀ probe ∈ row::rest,Holds owner term probe) → Accepted owner.release.programme.actual.pool term)
      (cursor : Budget.Cursor owner term row) (remaining : Nat) (balanced : cursor.work.length+remaining = sourceUnits owner)
  | reserving (row : Row owner) (rest : List (Row owner))
      (within : ∀ probe ∈ row::rest,probe ∈ rows owner)
      (passed : (∀ probe ∈ row::rest,Holds owner term probe) → Accepted owner.release.programme.actual.pool term)
      (allowance : Budget.Quote owner term row) (remaining prepaid : Nat) (balanced : prepaid+remaining = allowance.amount)
  | approved (valid : Accepted owner.release.programme.actual.pool term)
  | refused (row : Row owner) (inside : row ∈ rows owner) (invalid : ¬ Holds owner term row)
def start (term : Term owner) : State owner term := .waiting (rows owner) (fun _ member => member) ((rows_iff _ term).mp)

inductive Event (term : Term owner) where
  | openRow (row : Row owner)
  | budgetStep (row : Row owner) (before : Budget.Cursor owner term row) (made : Budget.Advance before)
  | quoted (row : Row owner) (allowance : Budget.Quote owner term row)
  | credit (row : Row owner) (ordinal : Nat)
  | tested (row : Row owner) (receipt : Receipt owner term row)
  | complete

def step {term : Term owner} : State owner term → Option (State owner term × Event owner term)
  | .waiting [] _ passed => some (.approved (passed (by intro row inside;cases inside)),.complete)
  | .waiting (row::rest) within passed =>
      some (.finishing row rest within passed (Budget.start owner term row),.openRow row)
  | .finishing row rest within passed cursor =>
      match Budget.quote? cursor (within row List.mem_cons_self) with
      | some allowance => some (.reserving row rest within passed allowance allowance.amount 0 (by omega),.quoted row allowance)
      | none =>
          let made := Budget.advance cursor
          some (.finishing row rest within passed made.after,.budgetStep row cursor made)
  | .quoting row rest within passed cursor remaining balanced =>
      match Budget.quote? cursor (within row List.mem_cons_self) with
      | some allowance => some (.reserving row rest within passed allowance allowance.amount 0 (by omega),.quoted row allowance)
      | none => match remaining with
        | 0 =>
            let allowance := Budget.retain cursor (within row List.mem_cons_self) (by change cursor.work.length = sourceUnits owner;omega)
            some (.reserving row rest within passed allowance allowance.amount 0 (by omega),.quoted row allowance)
        | remaining+1 =>
            let made := Budget.advance cursor
            some (.quoting row rest within passed made.after remaining (by rw [made.work_exact,List.length_append,List.length_singleton];omega),
              .budgetStep row cursor made)
  | .reserving row rest within passed allowance (remaining+1) prepaid balanced =>
      some (.reserving row rest within passed allowance remaining (prepaid+1) (by omega),.credit row prepaid)
  | .reserving row rest within passed allowance 0 prepaid balanced =>
      let made : Receipt owner term row := ⟨allowance,Work.atom owner.release.programme.actual.pool (.admission term row),rfl,
        prepaid,by omega,by have := allowance.covered;change (Work.atom _ (.admission term row)).work.length ≤ _ at this;omega⟩
      match made.checked.decision with
      | .isTrue valid => some (.waiting rest (fun probe member => within probe (List.mem_cons_of_mem _ member)) (by
          intro later
          apply passed
          intro probe member
          rcases List.mem_cons.mp member with same | remaining
          · subst probe;exact valid
          · exact later probe remaining),.tested row made)
      | .isFalse invalid => some (.refused row (within row List.mem_cons_self) invalid,.tested row made)
  | .approved _ | .refused .. => none

def State.finished {term : Term owner} : State owner term → Bool
  | .approved _ | .refused .. => true
  | _ => false
def State.decision {term : Term owner} : State owner term → Option (Decidable (Accepted owner.release.programme.actual.pool term))
  | .approved valid => some (.isTrue valid)
  | .refused row inside invalid => some (.isFalse (fun valid => invalid ((rows_iff _ term).mpr valid row inside)))
  | _ => none

def rowWeight := 2*sourceUnits owner+Budget.quotationCeiling owner+4
def ceiling := (rows owner).length*rowWeight owner+1
def State.rank {term : Term owner} : State owner term → Nat
  | .waiting todo .. => todo.length*rowWeight owner+1
  | .finishing _ rest _ _ cursor => rest.length*rowWeight owner+sourceUnits owner+Counter.Termination.rank _ cursor.current+3
  | .quoting _ rest _ _ _ remaining _ => rest.length*rowWeight owner+sourceUnits owner+remaining+3
  | .reserving _ rest _ _ _ remaining _ _ => rest.length*rowWeight owner+remaining+2
  | .approved _ | .refused .. => 0

theorem start_rank (term : Term owner) : (start owner term).rank owner = ceiling owner := rfl

theorem each_step_progresses {term : Term owner} {before after : State owner term} {event : Event owner term}
    (observed : step owner before = some (after,event)) : after.rank owner < before.rank owner := by
  cases before with
  | waiting todo within passed =>
    cases todo with
    | nil => cases Option.some.inj observed;simp only [State.rank];omega
    | cons row rest =>
      cases Option.some.inj observed
      have bounded := Budget.initial_rank_is_covered owner term row (within row List.mem_cons_self)
      simp only [State.rank,Budget.start,List.length_cons,rowWeight,Nat.add_mul,Nat.one_mul]
      omega
  | finishing row rest within passed cursor =>
    dsimp only [step] at observed;split at observed
    · rename_i allowance found
      cases Option.some.inj observed
      have bound := allowance.bounded
      change allowance.amount ≤ sourceUnits owner at bound
      simp only [State.rank];omega
    · rename_i missing
      cases Option.some.inj observed
      have reduced := Budget.every_pending_source_advance_progresses cursor (within row List.mem_cons_self) missing
      simp only [State.rank];omega
  | quoting row rest within passed cursor remaining balanced =>
    dsimp only [step] at observed;split at observed
    · rename_i allowance found
      cases Option.some.inj observed
      have bound := allowance.bounded
      change allowance.amount ≤ sourceUnits owner at bound
      simp only [State.rank];omega
    · cases remaining with
      | zero => cases Option.some.inj observed;simp only [State.rank,Budget.retain,sourceUnits];omega
      | succ remaining => cases Option.some.inj observed;simp only [State.rank];omega
  | reserving row rest within passed allowance remaining prepaid balanced =>
    cases remaining with
    | succ remaining => cases Option.some.inj observed;simp only [State.rank];omega
    | zero =>
      dsimp only [step] at observed;split at observed
      all_goals cases Option.some.inj observed
      all_goals simp only [State.rank];omega
  | approved | refused => cases observed

theorem stopped_iff_finished {term : Term owner} (before : State owner term) : step owner before = none ↔ before.finished owner = true := by
  cases before with
  | waiting todo => cases todo <;> simp [step,State.finished]
  | finishing row rest within passed cursor =>
    dsimp only [step,State.finished];split <;> simp
  | quoting row rest within passed cursor remaining balanced =>
    dsimp only [step,State.finished];split
    · simp
    · cases remaining <;> simp
  | reserving row rest within passed allowance remaining prepaid balanced =>
    cases remaining with
    | succ => simp [step,State.finished]
    | zero => dsimp only [step,State.finished];split <;> simp
  | approved | refused => simp [step,State.finished]

theorem a_native_receipt_is_emitted_only_after_full_reservation {term : Term owner} (row : Row owner)
    (rest : List (Row owner)) (within : ∀ probe ∈ row::rest,probe ∈ rows owner)
    (passed : (∀ probe ∈ row::rest,Holds owner term probe) → Accepted owner.release.programme.actual.pool term)
    (allowance : Budget.Quote owner term row) (remaining prepaid : Nat) (balanced : prepaid+remaining = allowance.amount)
    (after : State owner term) (receipt : Receipt owner term row)
    (observed : step owner (.reserving row rest within passed allowance remaining prepaid balanced) = some (after,.tested row receipt)) :
    remaining = 0 ∧ prepaid = allowance.amount := by
  cases remaining with
  | succ remaining => cases observed
  | zero => exact ⟨rfl,by omega⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Admission
