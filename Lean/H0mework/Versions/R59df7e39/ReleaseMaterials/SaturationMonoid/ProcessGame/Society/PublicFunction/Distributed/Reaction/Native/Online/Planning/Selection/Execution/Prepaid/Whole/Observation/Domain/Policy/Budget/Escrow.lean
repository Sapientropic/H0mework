import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Funding
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Runtime
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.EscrowBudget
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {units : Nat}

structure Programme (prepared : Prepared input) (units : Nat) where
  private mk ::
  funding : Funding prepared units
  funding_generated : funding = reserve prepared units
  nonempty : prepared.saved ≠ []
  all_paid : ∀ index : Index prepared,(funding.resultAt index).funded
  calculation : Calculation funding.installed units
  calculation_generated : calculation = calculate funding.installed units

inductive Attempt (prepared : Prepared input) (units : Nat) where
  | empty (absent : prepared.saved = [])
  | unpaid (funding : Funding prepared units) (generated : funding = reserve prepared units)
      (index : Index prepared) (failed : ¬ (funding.resultAt index).funded)
  | running (made : Programme prepared units)

def generate (prepared : Prepared input) (units : Nat) : Attempt prepared units :=
  if absent : prepared.saved = [] then .empty absent else
    let funding := reserve prepared units
    match Distributed.inspect (fun index : Index prepared => (funding.resultAt index).funded) (keys prepared) with
    | .rejected index _ unpaid => .unpaid funding rfl index unpaid
    | .accepted all => .running ⟨funding,rfl,absent,fun index => all index (List.mem_finRange _),
        calculate funding.installed units,rfl⟩

namespace Attempt
def endpoint : Attempt prepared units → Prepared input
  | .empty _ => prepared
  | .unpaid funding .. => funding.installed
  | .running made => made.funding.installed
end Attempt

namespace Programme
variable (made : Programme prepared units)

def affordable (value : Nat) : Prop := made.calculation.run.spent+value ≤ units
instance (value : Nat) : Decidable (made.affordable value) := inferInstanceAs (Decidable (_ ≤ _))
def funded : Prop := ∀ index : Index prepared,(made.funding.resultAt index).funded
instance : Decidable made.funded := by unfold funded;infer_instance

inductive Debt where
  | old (obligation : Policy.Obligation prepared)
  | funding (entry : CachedCharge prepared units)
  | calculation (run : Calculation made.funding.installed units)
  | body (event : Budget.Event made.funding.installed)
  | allocation (index : Index prepared) (ordinal : Fin made.calculation.run.spent)

def pending : List (Debt made) :=
  (Policy.obligations prepared).map Debt.old ++ made.funding.cached.map Debt.funding ++
    [Debt.calculation made.calculation] ++ made.calculation.run.work.map Debt.body ++
    (keys prepared).flatMap fun index => (List.finRange made.calculation.run.spent).map (Debt.allocation index)

structure Release (value : Nat) where
  private mk ::
  all_paid : made.funded
  correct : value = Work.workBudget made.funding.installed
  covered : made.affordable value
  execution : Policy.Protocol made.funding.installed
  generated : execution = Policy.invoke made.funding.installed

inductive Outcome where
  | exhausted (state : Frame) (residual : made.calculation.run.endpoint = state)
      (all_spent : made.calculation.run.spent = units)
  | shortfall (value : Nat) (correct : value = Work.workBudget made.funding.installed)
      (lacks : units < made.calculation.run.spent+value)
  | ready (value : Nat) (released : Release made value)

def release : Outcome made :=
  match made.calculation.result with
  | .exhausted state residual all_spent => .exhausted state residual all_spent
  | .budget value _ _ _ correct =>
      if covered : made.affordable value then
        .ready value ⟨made.all_paid,correct,covered,Policy.invoke made.funding.installed,rfl⟩
      else .shortfall value correct (Nat.lt_of_not_ge covered)

structure Allocation (index : Index prepared) (ordinal : Fin made.calculation.run.spent) where
  private mk ::
  invoice : Charge.Invoice (made.funding.resultAt index)
  slot : Fin invoice.bill.units
  slot_exact : slot.val = ordinal.val

def allocation (index : Index prepared) (ordinal : Fin made.calculation.run.spent) : Allocation made index ordinal :=
  let receipt := (made.funding.resultAt index).invoice (made.all_paid index)
  ⟨receipt,⟨ordinal.val,by rw [receipt.size];exact Nat.lt_of_lt_of_le ordinal.isLt made.calculation.run.bounded⟩,rfl⟩

theorem no_two_transitions_reuse_a_cell_invoice_slot (index : Index prepared)
    (first second : Fin made.calculation.run.spent)
    (same : (made.allocation index first).slot.val = (made.allocation index second).slot.val) : first = second := by
  exact Fin.ext same

theorem actual_prepaid_units (index : Index prepared) (ordinal : Fin made.calculation.run.spent) :
    (made.allocation index ordinal).invoice.bill.units = units ∧
      (made.allocation index ordinal).invoice.bill.payment.succeeded = true :=
  ⟨(made.allocation index ordinal).invoice.size,(made.allocation index ordinal).invoice.paid⟩
def occurrenceSlot (index : Index prepared) (ordinal : Fin made.calculation.run.spent) : Index prepared × Nat :=
  (index,(made.allocation index ordinal).slot.val)

theorem distinct_cells_or_transitions_do_not_share_an_occurrence_slot
    (first second : Index prepared) (a b : Fin made.calculation.run.spent)
    (same : made.occurrenceSlot first a = made.occurrenceSlot second b) : first = second ∧ a = b := by
  exact ⟨congrArg Prod.fst same,Fin.ext (congrArg Prod.snd same)⟩


namespace Release
variable {made : Programme prepared units} {value : Nat} (released : Release made value)

theorem arithmetic_and_original_execution_fit_the_same_prepaid_quota :
    made.calculation.run.spent+Work.controlSteps made.funding.installed released.execution.work ≤ units := by
  have body := released.execution.whole_cached_public_work_fits_its_source_budget
  have paid := released.covered
  have correct := released.correct
  unfold affordable at paid
  omega

def executionSlot (index : Index prepared)
    (ordinal : Fin (Work.controlSteps made.funding.installed released.execution.work)) :
    Fin (((made.funding.resultAt index).invoice (released.all_paid index)).bill.units) :=
  ⟨made.calculation.run.spent+ordinal.val,by
    rw [((made.funding.resultAt index).invoice (released.all_paid index)).size]
    have bounded := released.arithmetic_and_original_execution_fit_the_same_prepaid_quota
    omega⟩

theorem arithmetic_and_execution_slots_are_disjoint (index : Index prepared)
    (arithmetic : Fin made.calculation.run.spent)
    (execution : Fin (Work.controlSteps made.funding.installed released.execution.work)) :
    (made.allocation index arithmetic).slot.val ≠ (released.executionSlot index execution).val := by
  have smaller := arithmetic.isLt
  change arithmetic.val ≠ made.calculation.run.spent+execution.val
  omega

def unused : Nat := units-(made.calculation.run.spent+Work.controlSteps made.funding.installed released.execution.work)

theorem prepaid_quota_is_consumed_or_retained :
    made.calculation.run.spent+Work.controlSteps made.funding.installed released.execution.work+released.unused = units := by
  have bounded := released.arithmetic_and_original_execution_fit_the_same_prepaid_quota
  unfold unused
  omega

end Release
end Programme
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.EscrowBudget

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.EscrowBudget
namespace OfferAcquisition
set_option backward.isDefEq.respectTransparency false
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {units : Nat}

abbrev Check (funding : Funding prepared units) (remaining : List (Index prepared)) :=
  Distributed.Inspection (fun index : Index prepared => (funding.resultAt index).funded) remaining
private def liftCheck (funding : Funding prepared units) (head : Index prepared)
    {tail : List (Index prepared)} (checked : (funding.resultAt head).funded) : Check funding tail → Check funding (head::tail)
  | .accepted all => .accepted (by
      intro index inside;rcases List.mem_cons.mp inside with same | later
      · subst index;exact checked
      · exact all index later)
  | .rejected index listed broken => .rejected index (List.mem_cons_of_mem _ listed) broken
private theorem liftCheck_exact (funding : Funding prepared units) (head : Index prepared)
    (tail : List (Index prepared)) (checked : (funding.resultAt head).funded) :
    liftCheck funding head checked (Distributed.inspect (fun index : Index prepared => (funding.resultAt index).funded) tail) =
      Distributed.inspect (fun index : Index prepared => (funding.resultAt index).funded) (head::tail) := by
  simp only [Distributed.inspect,checked,↓reduceDIte]
  cases Distributed.inspect (fun index : Index prepared => (funding.resultAt index).funded) tail <;> rfl
private theorem unpaid_exact (funding : Funding prepared units) (generated : funding = reserve prepared units)
    (nonempty : prepared.saved ≠ []) (index : Index prepared) (listed : index ∈ keys prepared)
    (broken : ¬(funding.resultAt index).funded)
    (actual : Distributed.Inspection.rejected index listed broken = Distributed.inspect (fun index : Index prepared => (funding.resultAt index).funded) (keys prepared)) :
    Attempt.unpaid funding generated index broken = generate prepared units := by
  cases generated;simp only [generate,dif_neg nonempty,←actual]
private theorem running_exact (funding : Funding prepared units) (generated : funding = reserve prepared units)
    (nonempty : prepared.saved ≠ []) (all : ∀ index ∈ keys prepared,(funding.resultAt index).funded)
    (actual : Distributed.Inspection.accepted all = Distributed.inspect (fun index : Index prepared => (funding.resultAt index).funded) (keys prepared))
    (calculation : Calculation funding.installed units) (calculated : calculation = calculate funding.installed units) :
    Attempt.running (⟨funding,generated,nonempty,fun index => all index (List.mem_finRange _),calculation,calculated⟩ : Programme prepared units) = generate prepared units := by
  cases generated;cases calculated;simp only [generate,dif_neg nonempty,←actual]
inductive State (prepared : Prepared input) (units : Nat) where
  | opening
  | funding (nonempty : prepared.saved ≠ []) (cursor : Acquisition.State prepared units)
  | checking (funding : Funding prepared units) (generated : funding = reserve prepared units)
      (nonempty : prepared.saved ≠ []) (remaining : List (Index prepared))
      (embed : Check funding remaining → Check funding (keys prepared))
      (coherent : embed (Distributed.inspect (fun index : Index prepared => (funding.resultAt index).funded) remaining) =
        Distributed.inspect (fun index : Index prepared => (funding.resultAt index).funded) (keys prepared))
  | calculating (funding : Funding prepared units) (generated : funding = reserve prepared units)
      (nonempty : prepared.saved ≠ []) (all : ∀ index ∈ keys prepared,(funding.resultAt index).funded)
      (actual : Distributed.Inspection.accepted all = Distributed.inspect (fun index : Index prepared => (funding.resultAt index).funded) (keys prepared))
      (cursor : CalculationAcquisition.State funding.installed units)
  | finished (attempt : Attempt prepared units) (generated : attempt = generate prepared units)
def initial (prepared : Prepared input) (units : Nat) : State prepared units := .opening
inductive Event (prepared : Prepared input) (units : Nat) where
  | opened
  | funding (event : Acquisition.Event prepared units)
  | funded (funding : Funding prepared units) (generated : funding = reserve prepared units)
  | checked (funding : Funding prepared units) (index : Index prepared) (value : Bool)
      (actual : value = decide (funding.resultAt index).funded)
  | qualified (funding : Funding prepared units) (generated : funding = reserve prepared units)
  | calculation (funding : Funding prepared units) (event : CalculationAcquisition.Event funding.installed units)
  | completed (attempt : Attempt prepared units) (generated : attempt = generate prepared units)
private def startCheck (funding : Funding prepared units) (generated : funding = reserve prepared units)
    (nonempty : prepared.saved ≠ []) (checked : Check funding (keys prepared))
    (actual : checked = Distributed.inspect (fun index : Index prepared => (funding.resultAt index).funded) (keys prepared)) : State prepared units :=
  match checked with
  | .rejected index listed broken => .finished (.unpaid funding generated index broken) (unpaid_exact funding generated nonempty index listed broken actual)
  | .accepted all => .calculating funding generated nonempty all actual (CalculationAcquisition.initial funding.installed units)
def move : State prepared units → Option (State prepared units × Event prepared units)
  | .opening => if absent : prepared.saved = [] then
      some (.finished (.empty absent) (by simp only [generate,dif_pos absent]),.opened)
    else some (.funding absent (Acquisition.initial prepared units),.opened)
  | .funding nonempty (.finished funding generated) =>
      some (.checking funding generated nonempty (keys prepared) id rfl,.funded funding generated)
  | .funding nonempty cursor@(.reading ..) => match _step : Acquisition.move cursor with
      | none => none
      | some (after,event) => some (.funding nonempty after,.funding event)
  | .checking funding generated nonempty [] embed coherent =>
      some (startCheck funding generated nonempty (embed (.accepted (by simp))) coherent,.qualified funding generated)
  | .checking funding generated nonempty (head::tail) embed coherent =>
      if checked : (funding.resultAt head).funded then
        some (.checking funding generated nonempty tail (fun later => embed (liftCheck funding head checked later))
          (by rw [liftCheck_exact];exact coherent),.checked funding head true (by simp [checked]))
      else some (startCheck funding generated nonempty (embed (.rejected head List.mem_cons_self checked)) (by
          rw [←coherent];congr 1;rw [Distributed.inspect,dif_neg checked]),.checked funding head false (by simp [checked]))
  | .calculating funding generated nonempty all checked (.finished calculation calculated) =>
      let made : Programme prepared units := ⟨funding,generated,nonempty,fun index => all index (List.mem_finRange _),calculation,calculated⟩
      let exact := running_exact funding generated nonempty all checked calculation calculated
      some (.finished (.running made) exact,.completed (.running made) exact)
  | .calculating funding generated nonempty all checked cursor@(.running ..) =>
      match _step : CalculationAcquisition.move funding.installed units cursor with
      | none => none
      | some (after,event) => some (.calculating funding generated nonempty all checked after,.calculation funding event)
  | .finished .. => none
def State.rank : State prepared units → Nat
  | .opening => 2*(keys prepared).length+units+6
  | .funding _ cursor => cursor.rank+(keys prepared).length+units+4
  | .checking _ _ _ remaining .. => remaining.length+units+3
  | .calculating account _ _ _ _ cursor => cursor.rank account.installed units+1
  | .finished .. => 0
def State.done : State prepared units → Bool | .finished .. => true | _ => false
private theorem startCheck_rank (funding : Funding prepared units) (generated : funding = reserve prepared units)
    (nonempty : prepared.saved ≠ []) (checked : Check funding (keys prepared))
    (actual : checked = Distributed.inspect (fun index : Index prepared => (funding.resultAt index).funded) (keys prepared)) :
    (startCheck funding generated nonempty checked actual).rank < units+3 := by
  cases checked with
  | rejected => dsimp only [startCheck,State.rank];omega
  | accepted => dsimp only [startCheck,State.rank,CalculationAcquisition.initial,CalculationAcquisition.State.rank];omega
theorem progress {before after : State prepared units} {event : Event prepared units}
    (actual : move before = some (after,event)) : after.rank < before.rank := by
  cases before with
  | opening =>
      dsimp only [move] at actual;split at actual
      all_goals cases Option.some.inj actual;dsimp only [State.rank,Acquisition.initial,Acquisition.State.rank];omega
  | funding nonempty cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,Acquisition.State.rank];omega
      | reading =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step;cases Option.some.inj actual
            have less := Acquisition.progress step;simp only [State.rank];omega
  | checking funding generated nonempty remaining embed coherent =>
      cases remaining with
      | nil =>
          dsimp only [move] at actual;cases Option.some.inj actual
          simpa only [State.rank,List.length_nil,Nat.zero_add] using startCheck_rank funding generated nonempty (embed (.accepted (by simp))) coherent
      | cons head tail =>
          dsimp only [move] at actual;split at actual
          · cases Option.some.inj actual;simp only [State.rank,List.length_cons];omega
          · rename_i refused
            cases Option.some.inj actual
            have checkedEq : embed (.rejected head List.mem_cons_self refused) = Distributed.inspect (fun index : Index prepared => (funding.resultAt index).funded) (keys prepared) := by
              rw [←coherent];congr 1;rw [Distributed.inspect,dif_neg refused]
            have less := startCheck_rank funding generated nonempty (embed (.rejected head List.mem_cons_self refused)) checkedEq
            apply lt_of_lt_of_le less
            simp only [State.rank,List.length_cons];omega
  | calculating funding generated nonempty all checked cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,CalculationAcquisition.State.rank];omega
      | running =>
          dsimp only [move] at actual;split at actual
          · cases actual
          · rename_i after event step;cases Option.some.inj actual
            have less := CalculationAcquisition.progress funding.installed units step;simp only [State.rank];omega
  | finished => cases actual
theorem no_move_iff_done (before : State prepared units) : move before = none ↔ before.done = true := by
  cases before with
  | opening => dsimp only [move,State.done];split <;> simp
  | funding nonempty cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | reading cached remaining conserved =>
          dsimp only [move,State.done];split
          · rename_i stopped;cases remaining <;> simp [Acquisition.move] at stopped
          · simp
  | checking funding generated nonempty remaining embed coherent =>
      cases remaining <;> dsimp only [move,State.done] <;> first | (split <;> simp) | simp
  | calculating funding generated nonempty all checked cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | running =>
          dsimp only [move,State.done];split
          · rename_i stopped;have done := (CalculationAcquisition.no_move_iff_done funding.installed units _).mp stopped;cases done
          · simp
  | finished => simp [move,State.done]
end OfferAcquisition

namespace Programme.ContinuationAcquisition
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {units : Nat}

variable (made : Programme prepared units)
private theorem exhausted_exact (state : Frame) (residual : made.calculation.run.endpoint = state)
    (spent : made.calculation.run.spent = units) (result : made.calculation.result = .exhausted state residual spent) :
    Outcome.exhausted state residual spent = made.release := by simp only [Programme.release,result]
private theorem shortfall_exact (value : Nat) (core : SourceBudgetMachine.Core)
    (cached : made.calculation.run.endpoint = .program core []) (observed : core.stack.head? = some value)
    (correct : value = Work.workBudget made.funding.installed)
    (result : made.calculation.result = .budget value core cached observed correct) (refused : ¬ made.affordable value) :
    Outcome.shortfall value correct (Nat.lt_of_not_ge refused) = made.release := by simp only [Programme.release,result,dif_neg refused]
private theorem ready_exact (value : Nat) (core : SourceBudgetMachine.Core)
    (cached : made.calculation.run.endpoint = .program core []) (observed : core.stack.head? = some value)
    (correct : value = Work.workBudget made.funding.installed)
    (result : made.calculation.result = .budget value core cached observed correct) (covered : made.affordable value)
    (execution : Policy.Protocol made.funding.installed) (generated : execution = Policy.invoke made.funding.installed) :
    Outcome.ready value (⟨made.all_paid,correct,covered,execution,generated⟩ : Release made value) = made.release := by
  cases generated;simp only [Programme.release,result,dif_pos covered]
inductive State where
  | opening
  | execution (value : Nat) (core : SourceBudgetMachine.Core)
      (cached : made.calculation.run.endpoint = .program core []) (observed : core.stack.head? = some value)
      (correct : value = Work.workBudget made.funding.installed)
      (result : made.calculation.result = .budget value core cached observed correct) (covered : made.affordable value)
      (cursor : Policy.ProtocolAcquisition.State made.funding.installed)
  | finished (outcome : Outcome made) (generated : outcome = made.release)
def initial : State made := .opening
inductive Event where
  | disposed (outcome : Outcome made) (generated : outcome = made.release)
  | covered (value : Nat) (correct : value = Work.workBudget made.funding.installed) (covered : made.affordable value)
  | protocol (event : Policy.ProtocolAcquisition.Event made.funding.installed)
  | executed (execution : Policy.Protocol made.funding.installed) (generated : execution = Policy.invoke made.funding.installed)
def move : State made → Option (State made × Event made)
  | .opening => match result : made.calculation.result with
    | .exhausted state residual spent =>
        let outcome := Outcome.exhausted state residual spent
        let exact := exhausted_exact made state residual spent result
        some (.finished outcome exact,.disposed outcome exact)
    | .budget value core cached observed correct =>
        if covered : made.affordable value then
          some (.execution value core cached observed correct result covered (Policy.ProtocolAcquisition.initial made.funding.installed),.covered value correct covered)
        else
          let outcome := Outcome.shortfall value correct (Nat.lt_of_not_ge covered)
          let exact := shortfall_exact made value core cached observed correct result covered
          some (.finished outcome exact,.disposed outcome exact)
  | .execution value core cached observed correct result covered (.finished execution generated) =>
      let release : Release made value := ⟨made.all_paid,correct,covered,execution,generated⟩
      let exact := ready_exact made value core cached observed correct result covered execution generated
      some (.finished (.ready value release) exact,.executed execution generated)
  | .execution value core cached observed correct result covered cursor@(.opening)
  | .execution value core cached observed correct result covered cursor@(.compiling ..)
  | .execution value core cached observed correct result covered cursor@(.reviewing ..)
  | .execution value core cached observed correct result covered cursor@(.coverage ..)
  | .execution value core cached observed correct result covered cursor@(.authorizing ..) =>
      match _step : Policy.ProtocolAcquisition.move cursor with
      | none => none
      | some (after,event) => some (.execution value core cached observed correct result covered after,.protocol event)
  | .finished .. => none
def State.rank : State made → Nat | .opening => (Policy.ProtocolAcquisition.initial made.funding.installed).rank+2 | .execution _ _ _ _ _ _ _ cursor => cursor.rank+1 | .finished .. => 0
def State.done : State made → Bool | .finished .. => true | _ => false
theorem progress {before after : State made} {event : Event made}
    (actual : move made before = some (after,event)) : after.rank made < before.rank made := by
  cases before with
  | opening =>
      dsimp only [move] at actual;split at actual
      · cases Option.some.inj actual;simp only [State.rank];omega
      · split at actual
        all_goals cases Option.some.inj actual;simp only [State.rank];omega
  | execution value core cached observed correct result covered cursor =>
      cases cursor with
      | finished => dsimp only [move] at actual;cases Option.some.inj actual;simp only [State.rank,Policy.ProtocolAcquisition.State.rank];omega
      | opening | compiling | reviewing | coverage | authorizing =>
          all_goals dsimp only [move] at actual;split at actual
          all_goals first
            | (solve | cases actual)
            | (rename_i after event step;cases Option.some.inj actual
               have less := Policy.ProtocolAcquisition.progress step;simp only [State.rank];omega)
  | finished => cases actual
theorem no_move_iff_done (before : State made) : move made before = none ↔ before.done made = true := by
  cases before with
  | opening => dsimp only [move,State.done];split <;> first | (split <;> simp) | simp
  | execution value core cached observed correct result covered cursor =>
      cases cursor with
      | finished => simp [move,State.done]
      | opening | compiling | reviewing | coverage | authorizing =>
          all_goals dsimp only [move,State.done];split
          all_goals first
            | (rename_i stopped;have done := (Policy.ProtocolAcquisition.no_move_iff_done _).mp stopped;cases done)
            | simp
  | finished => simp [move,State.done]
end Programme.ContinuationAcquisition

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.EscrowBudget
