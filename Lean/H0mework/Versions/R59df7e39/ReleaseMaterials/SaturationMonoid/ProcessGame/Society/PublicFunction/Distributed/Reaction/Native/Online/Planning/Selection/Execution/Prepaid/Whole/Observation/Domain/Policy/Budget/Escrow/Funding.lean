import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Machine
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.EscrowBudget
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {point : NativePoint input} {prepared : Prepared input}

inductive Charge (units : Nat) : Stage input point → Type where
  | stopped (header) : Charge units (.stopped header)
  | prior (failure) : Charge units (.blocked failure)
  | absent (scope) (why : Prefix.quote (Whole.paidPoint scope) input.actor input.position scope.continuation.words units = none) :
      Charge units (.ready scope)
  | refused (scope) (bill : Prefix.Bill (Whole.paidPoint scope) input.actor input.position)
      (before : bill.before = scope.continuation.words) (size : bill.units = units)
      (quoted : Prefix.quote (Whole.paidPoint scope) input.actor input.position scope.continuation.words units = some ⟨bill,before,size⟩)
      (unpaid : bill.payment.succeeded = false) : Charge units (.ready scope)
  | paid (scope) (bill : Prefix.Bill (Whole.paidPoint scope) input.actor input.position)
      (before : bill.before = scope.continuation.words) (size : bill.units = units)
      (quoted : Prefix.quote (Whole.paidPoint scope) input.actor input.position scope.continuation.words units = some ⟨bill,before,size⟩)
      (success : bill.payment.succeeded = true) : Charge units (.ready scope)

def charge (units : Nat) : (stage : Stage input point) → Charge units stage
  | .stopped header => .stopped header
  | .blocked failure => .prior failure
  | .ready scope =>
      match quoted : Prefix.quote (Whole.paidPoint scope) input.actor input.position scope.continuation.words units with
      | none => .absent scope quoted
      | some bill =>
          if paid : bill.val.payment.succeeded = true then
            .paid scope bill.val bill.property.1 bill.property.2 quoted paid
          else .refused scope bill.val bill.property.1 bill.property.2 quoted (Bool.eq_false_iff.mpr paid)

namespace Charge
variable {units : Nat} {stage : Stage input point}

def endpoint : Charge units stage → Stage input point
  | .stopped header => .stopped header
  | .prior failure => .blocked failure
  | .absent scope why => .blocked (.unpriced scope units why)
  | .refused scope bill before _ _ unpaid => .blocked (.refused scope bill before unpaid)
  | .paid scope bill before _ _ _ => .ready (PaidBudgetArithmetic.refresh (Whole.extend scope bill before))

theorem original_reservation (made : Charge units stage) : made.endpoint = reserveStage input units stage := by
  cases made with
  | stopped | prior => rfl
  | absent scope why =>
      dsimp only [endpoint,reserveStage]
      split
      · rfl
      · rename_i invoice quoted
        cases why.symm.trans quoted
  | refused scope bill before size quoted unpaid =>
      dsimp only [endpoint,reserveStage]
      split
      · rename_i absent
        cases quoted.symm.trans absent
      · rename_i invoice observed
        have same := Option.some.inj (observed.symm.trans quoted)
        cases same
        split
        · rename_i paid
          rw [unpaid] at paid
          cases paid
        · rfl
  | paid scope bill before size quoted success =>
      dsimp only [endpoint,reserveStage]
      split
      · rename_i absent
        cases quoted.symm.trans absent
      · rename_i invoice observed
        have same := Option.some.inj (observed.symm.trans quoted)
        cases same
        split
        · rfl
        · rename_i refused
          exact False.elim (refused success)

def funded : Charge units stage → Prop
  | .paid .. => True
  | _ => False
instance (made : Charge units stage) : Decidable made.funded := by cases made <;> unfold funded <;> infer_instance

structure Invoice (made : Charge units stage) where
  private mk ::
  source : PaidBudgetArithmetic.OriginalScope point
  before_stage : stage = .ready source
  bill : Prefix.Bill (Whole.paidPoint source) input.actor input.position
  before : bill.before = source.continuation.words
  size : bill.units = units
  paid : bill.payment.succeeded = true
  after_stage : made.endpoint = .ready (PaidBudgetArithmetic.refresh (Whole.extend source bill before))

def invoice (made : Charge units stage) (paid : made.funded) : Invoice made := by
  cases made with
  | paid scope bill before size quoted success => exact ⟨scope,rfl,bill,before,size,success,rfl⟩
  | _ => exact False.elim paid

theorem actual_prefix (made : Charge units stage) (paid : made.funded) :
    let receipt := made.invoice paid
    (PaidBudgetArithmetic.refresh (Whole.extend receipt.source receipt.bill receipt.before)).continuation.words =
      receipt.source.continuation.words ++ [receipt.bill.payment.output] := by
  exact (made.invoice paid).source.continuation.append_words (made.invoice paid).bill (made.invoice paid).before
end Charge

abbrev CachedCharge (prepared : Prepared input) (units : Nat) := Sigma fun index : Index prepared => Charge units prepared.saved[index].stage

def charges (prepared : Prepared input) (units : Nat) : List (CachedCharge prepared units) :=
  (keys prepared).map fun index => ⟨index,charge units prepared.saved[index].stage⟩

structure Funding (prepared : Prepared input) (units : Nat) where
  private mk ::
  cached : List (CachedCharge prepared units)
  generated : cached = charges prepared units
  keys_exact : cached.map Sigma.fst = keys prepared

def reserve (prepared : Prepared input) (units : Nat) : Funding prepared units :=
  ⟨charges prepared units,rfl,by
    simp only [charges,List.map_map,Function.comp_def]
    induction keys prepared with
    | nil => rfl
    | cons head tail ih => exact congrArg (List.cons head) ih⟩

namespace Funding
variable {units : Nat} (funding : Funding prepared units)

theorem cached_length : funding.cached.length = prepared.saved.length := by
  have lengths := congrArg List.length funding.keys_exact
  simpa only [List.length_map,keys,List.length_finRange] using lengths

def cachedIndex (index : Index prepared) : Fin funding.cached.length :=
  ⟨index.val,by rw [funding.cached_length];exact index.isLt⟩

theorem cached_key (index : Index prepared) : funding.cached[funding.cachedIndex index].1 = index := by
  have selected : (funding.cached.map Sigma.fst)[index.val]? = some index := by
    rw [funding.keys_exact]
    simp [keys,List.finRange]
  obtain ⟨bounded,same⟩ := List.getElem?_eq_some_iff.mp selected
  simpa only [List.getElem_map,Fin.getElem_fin,cachedIndex] using same

def resultAt (index : Index prepared) : Charge units prepared.saved[index].stage :=
  funding.cached_key index ▸ funding.cached[funding.cachedIndex index].2

theorem alignment (index : Index prepared) : (funding.resultAt index).endpoint =
    stageFor input (.reserved prepared.recipe units) prepared.saved[index].point := by
  rw [(funding.resultAt index).original_reservation,prepared.original_cell_stage]
  rfl

def installed : Prepared input :=
  prepared.installCached (.reserved prepared.recipe units) (fun index => (funding.resultAt index).endpoint) funding.alignment

theorem source_order_and_multiplicity : funding.installed.saved.map Cell.point = prepared.saved.map Cell.point :=
  prepared.cached_installation_preserves_source_order _ _ funding.alignment

theorem every_actual_charge_is_installed (index : Index prepared) :
    ∃ cell ∈ funding.installed.saved,cell.point = prepared.saved[index].point ∧ HEq cell.stage (funding.resultAt index).endpoint :=
  prepared.cached_stage_is_installed _ _ funding.alignment index
end Funding
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.EscrowBudget

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.EscrowBudget
namespace Acquisition
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {units : Nat}

private theorem canonical (funding : Funding prepared units) : funding = reserve prepared units := by
  rcases funding with ⟨cached,generated,keys⟩
  cases generated;rfl
inductive State (prepared : Prepared input) (units : Nat) where
  | reading (cached : List (CachedCharge prepared units)) (remaining : List (Index prepared))
      (conserved : cached++remaining.map (fun index => ⟨index,charge units prepared.saved[index].stage⟩) = charges prepared units)
  | finished (funding : Funding prepared units) (generated : funding = reserve prepared units)
def initial (prepared : Prepared input) (units : Nat) : State prepared units := .reading [] (keys prepared) rfl
inductive Event (prepared : Prepared input) (units : Nat) where
  | charged (index : Index prepared) (result : Charge units prepared.saved[index].stage)
      (actual : result = charge units prepared.saved[index].stage)
  | installed (funding : Funding prepared units) (generated : funding = reserve prepared units)
def move : State prepared units → Option (State prepared units × Event prepared units)
  | .reading cached (index::rest) conserved =>
      let result := charge units prepared.saved[index].stage
      some (.reading (cached++[⟨index,result⟩]) rest (by
        simpa only [List.map_cons,List.append_assoc,List.singleton_append] using conserved),.charged index result rfl)
  | .reading cached [] conserved =>
      let generated : cached = charges prepared units := by simpa only [List.map_nil,List.append_nil] using conserved
      let funding : Funding prepared units := ⟨cached,generated,by rw [generated];exact (reserve prepared units).keys_exact⟩
      some (.finished funding (canonical funding),.installed funding (canonical funding))
  | .finished .. => none

def State.rank : State prepared units → Nat | .reading _ remaining _ => remaining.length+1 | .finished .. => 0
def State.done : State prepared units → Bool | .finished .. => true | _ => false
theorem progress {before after : State prepared units} {event : Event prepared units}
    (actual : move before = some (after,event)) : after.rank < before.rank := by
  cases before with
  | reading cached remaining conserved =>
      cases remaining <;> dsimp only [move] at actual <;> cases Option.some.inj actual
      all_goals simp only [State.rank,List.length_cons];omega
  | finished => cases actual
end Acquisition
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.EscrowBudget
