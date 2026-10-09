import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.OriginGraph
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ProductRead

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence
noncomputable section
open CPS1AtomicSource CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange
open scoped BigOperators
variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}

-- The field producer supplies its generated word. This consumer starts from the
-- same source and computes graph operations; it does not select a field outcome.
inductive MaterialRequest | sourceExchange deriving DecidableEq

inductive MaterialResidual (cursor : CPS1ReactiveNuclear.SourceCursor frame)
  | noSourceBond
  | reusedBond (bond : SourceBond cursor)
  | debitShortage (bond : SourceBond cursor) (inventory : ℤ)
  | occupiedCredit (bond : SourceBond cursor) (inventory : ℤ)
  deriving DecidableEq

structure MaterialState (source : Common before step raw) (_current : NativeCurrent source) where
  paid : List (BondToken cursor)

def MaterialState.graph {source : Common before step raw} {current : NativeCurrent source}
    (state : MaterialState source current) : OriginGraph source.atoms :=
  foldTokens (sourceGraph source) state.paid

def MaterialState.spent {source : Common before step raw} {current : NativeCurrent source}
    (state : MaterialState source current) : List (SourceBond cursor) := state.paid.map BondToken.debit

def MaterialState.record {source : Common before step raw} {current : NativeCurrent source}
    (state : MaterialState source current) (token : BondToken cursor) : MaterialState source current :=
  ⟨state.paid ++ [token]⟩

def materialInitial (source : Common before step raw) (current : NativeCurrent source) : MaterialState source current :=
  ⟨[]⟩

def MaterialState.whole {source : Common before step raw} {current : NativeCurrent source}
    (state : MaterialState source current) : NativeCurrent source × OriginGraph source.atoms :=
  (current,state.graph)

theorem recorded_graph {source : Common before step raw} {current : NativeCurrent source}
    (state : MaterialState source current) (token : BondToken cursor) :
    (state.record token).graph = applyToken state.graph token := by
  simp only [MaterialState.graph,MaterialState.record,foldTokens,List.foldl_append,
    List.foldl_cons,List.foldl_nil]

theorem recorded_spent {source : Common before step raw} {current : NativeCurrent source}
    (state : MaterialState source current) (token : BondToken cursor) :
    (state.record token).spent = state.spent ++ [token.debit] := by
  simp only [MaterialState.spent,MaterialState.record,List.map_append,List.map_cons,List.map_nil]

structure SourceMaterialStep (source : Common before step raw) (current : NativeCurrent source) where
  before : MaterialState source current
  token : BondToken cursor
  sourceActual : sourceToken? source current = some token
  unused : token.debit ∉ before.spent
  debitPaid : 1 ≤ before.graph.incidence token.debit
  creditFree : before.graph.incidence token.credit = 0

def SourceMaterialStep.after {source : Common before step raw} {current : NativeCurrent source}
    (event : SourceMaterialStep source current) : MaterialState source current := event.before.record event.token

def stepSource? (source : Common before step raw) (current : NativeCurrent source)
    (state : MaterialState source current) : Except (MaterialResidual cursor) (SourceMaterialStep source current) := by
  classical
  exact match selected : sourceToken? source current with
  | none => .error .noSourceBond
  | some token =>
    if spent : token.debit ∈ state.spent then .error (.reusedBond token.debit)
    else if paid : 1 ≤ state.graph.incidence token.debit then
      if empty : state.graph.incidence token.credit = 0 then
        .ok ⟨state,token,selected,spent,paid,empty⟩
      else .error (.occupiedCredit token.credit (state.graph.incidence token.credit))
    else .error (.debitShortage token.debit (state.graph.incidence token.debit))

theorem step_source_before (source : Common before step raw) (current : NativeCurrent source)
    (state : MaterialState source current) (event : SourceMaterialStep source current)
    (actual : stepSource? source current state = .ok event) : event.before = state := by
  unfold stepSource? at actual
  split at actual
  · cases actual
  · split at actual
    · cases actual
    · split at actual
      · split at actual
        · cases actual
          rfl
        · cases actual
      · cases actual

theorem step_vertices {source : Common before step raw} {current : NativeCurrent source}
    (event : SourceMaterialStep source current) :
    event.token.debit.left ∈ vertices source ∧ event.token.debit.right ∈ vertices source ∧
      event.token.credit.left ∈ vertices source ∧ event.token.credit.right ∈ vertices source :=
  (source_token_vertices source current event.token event.sourceActual).2

theorem step_distinct {source : Common before step raw} {current : NativeCurrent source}
    (event : SourceMaterialStep source current) : event.token.debit ≠ event.token.credit := by
  intro same
  have positive := event.debitPaid
  rw [same,event.creditFree] at positive
  norm_num at positive

theorem step_graph {source : Common before step raw} {current : NativeCurrent source}
    (event : SourceMaterialStep source current) : event.after.graph = applyToken event.before.graph event.token :=
  recorded_graph event.before event.token

theorem step_debit {source : Common before step raw} {current : NativeCurrent source}
    (event : SourceMaterialStep source current) :
    event.after.graph.incidence event.token.debit = event.before.graph.incidence event.token.debit-1 := by
  rw [step_graph]
  simp only [applyToken,BondToken.delta,sub_eq_add_neg,Finsupp.add_apply,Finsupp.neg_apply,
    Finsupp.single_eq_of_ne (step_distinct event),Finsupp.single_eq_same,zero_add]

theorem step_credit {source : Common before step raw} {current : NativeCurrent source}
    (event : SourceMaterialStep source current) : event.after.graph.incidence event.token.credit = 1 := by
  rw [step_graph]
  simp only [applyToken,BondToken.delta,Finsupp.add_apply,Finsupp.sub_apply,
    Finsupp.single_eq_of_ne (Ne.symm (step_distinct event)),Finsupp.single_eq_same,
    event.creditFree,sub_zero,zero_add]

theorem step_other_bonds {source : Common before step raw} {current : NativeCurrent source}
    (event : SourceMaterialStep source current) (bond : SourceBond cursor)
    (notDebit : bond ≠ event.token.debit) (notCredit : bond ≠ event.token.credit) :
    event.after.graph.incidence bond = event.before.graph.incidence bond := by
  rw [step_graph]
  exact apply_token_other _ _ bond notDebit notCredit

theorem step_charge {source : Common before step raw} {current : NativeCurrent source}
    (event : SourceMaterialStep source current) : event.after.graph.formalCharge = event.before.graph.formalCharge := by
  rw [step_graph]
  rfl

theorem step_whole {source : Common before step raw} {current : NativeCurrent source}
    (event : SourceMaterialStep source current) :
    event.after.whole.1 = current ∧ event.after.whole.1.nodes = current.nodes ∧
    event.after.whole.1.occupied = current.occupied ∧ event.after.whole.1.remaining = current.remaining :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem step_spent_unique {source : Common before step raw} {current : NativeCurrent source}
    (event : SourceMaterialStep source current) (unique : event.before.spent.Nodup) : event.after.spent.Nodup := by
  rw [SourceMaterialStep.after,recorded_spent]
  apply List.nodup_append.mpr
  refine ⟨unique,List.nodup_singleton _,?_⟩
  intro first firstHeld second secondHeld same
  have secondActual := List.mem_singleton.mp secondHeld
  apply event.unused
  rw [← secondActual,← same]
  exact firstHeld

theorem step_cannot_repeat {source : Common before step raw} {current : NativeCurrent source}
    (event : SourceMaterialStep source current) :
    stepSource? source current event.after = .error (.reusedBond event.token.debit) := by
  have spent : event.token.debit ∈ event.after.spent := by
    rw [SourceMaterialStep.after,recorded_spent]
    simp
  unfold stepSource?
  split
  · rename_i selected
    have impossible : none = some event.token := selected.symm.trans event.sourceActual
    cases impossible
  · rename_i token selected
    have same : token = event.token := Option.some.inj (selected.symm.trans event.sourceActual)
    subst token
    simp only [dif_pos spent]

structure SourceMaterialRun (source : Common before step raw) (current : NativeCurrent source) where
  fired : List (SourceMaterialStep source current)
  remaining : List MaterialRequest
  state : MaterialState source current
  residual : Option (MaterialResidual cursor)

private def runFrom (source : Common before step raw) (current : NativeCurrent source)
    (requests : List MaterialRequest) (state : MaterialState source current) : SourceMaterialRun source current :=
  match requests with
  | [] => ⟨[],[],state,none⟩
  | .sourceExchange :: rest => match stepSource? source current state with
    | .error residual => ⟨[],.sourceExchange :: rest,state,some residual⟩
    | .ok event =>
      let next := runFrom source current rest event.after
      ⟨event :: next.fired,next.remaining,next.state,next.residual⟩

def runMaterialWord (source : Common before step raw) (current : NativeCurrent source)
    (requests : List MaterialRequest) : SourceMaterialRun source current :=
  runFrom source current requests (materialInitial source current)

private theorem run_from_unique (source : Common before step raw) (current : NativeCurrent source)
    (requests : List MaterialRequest) (state : MaterialState source current) (unique : state.spent.Nodup) :
    (runFrom source current requests state).state.spent.Nodup := by
  induction requests generalizing state with
  | nil => exact unique
  | cons request rest ih =>
    cases request
    cases actual : stepSource? source current state with
    | error failure => simpa only [runFrom,actual] using unique
    | ok event =>
      have before := step_source_before source current state event actual
      have nextUnique := step_spent_unique event (before.symm ▸ unique)
      simpa only [runFrom,actual] using ih event.after nextUnique

theorem run_material_unique (source : Common before step raw) (current : NativeCurrent source)
    (requests : List MaterialRequest) : (runMaterialWord source current requests).state.spent.Nodup :=
  run_from_unique source current requests (materialInitial source current) List.nodup_nil

theorem run_material_whole (source : Common before step raw) (current : NativeCurrent source)
    (requests : List MaterialRequest) :
    (runMaterialWord source current requests).state.whole.1 = current ∧
    (runMaterialWord source current requests).state.whole.1.occupied = current.occupied ∧
    (runMaterialWord source current requests).state.whole.1.remaining = current.remaining := ⟨rfl,rfl,rfl⟩

theorem run_material_incidence (source : Common before step raw) (current : NativeCurrent source)
    (requests : List MaterialRequest) :
    (runMaterialWord source current requests).state.graph.incidence = bondInventory source.bonds+
      (((runMaterialWord source current requests).state.paid).map BondToken.delta).sum :=
  fold_tokens_incidence (sourceGraph source) _

theorem run_material_charge (source : Common before step raw) (current : NativeCurrent source)
    (requests : List MaterialRequest) :
    (runMaterialWord source current requests).state.graph.formalCharge = chargeInventory source.atoms :=
  fold_tokens_charge (sourceGraph source) _

theorem run_material_source_budget (source : Common before step raw) (current : NativeCurrent source)
    (requests : List MaterialRequest) (fuel : raw.fuel = firstFuel) :
    (reactionAtoms source.atoms).length = 95 ∧
    descriptorCharge ((reactionAtoms source.atoms).map Atom.descriptor) = -9 ∧
      descriptorElectrons ((reactionAtoms source.atoms).map Atom.descriptor) = 562 ∧
    (runMaterialWord source current requests).state.whole.1.remaining = current.remaining := by
  have budget : (reactionAtoms source.atoms).length = 95 ∧
      descriptorCharge ((reactionAtoms source.atoms).map Atom.descriptor) = -9 ∧
      descriptorElectrons ((reactionAtoms source.atoms).map Atom.descriptor) = 562 := by
    rw [source.atomSource,fuel]
    exact first_reaction_atoms_budget before.packet.source
  exact ⟨budget.1,budget.2.1,budget.2.2,rfl⟩

end
end CPS1MaterialIncidence
