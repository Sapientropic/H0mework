import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.MaterialAction

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

-- These are integer action data. The physical field word must generate them;
-- neither a field coefficient nor its nonzero support licenses an instruction.
inductive ChargedInstruction (cursor : CPS1ReactiveNuclear.SourceCursor frame)
  | electron (donor receiver : AtomOrigin cursor)
  | proton (hydrogen donor receiver : AtomOrigin cursor)
  | deprotonate (hydrogen donor : AtomOrigin cursor)
  deriving DecidableEq

abbrev ChargedSourceWord (cursor : CPS1ReactiveNuclear.SourceCursor frame) := List (ChargedInstruction cursor)

def nuclearInventory (atoms : List (Atom cursor)) : Charges cursor :=
  (atoms.map (fun atom => Finsupp.single atom.origin
    (Charged.atomicNumber atom.descriptor.source.element : ℤ))).sum

def electronInventory (source : Common before step raw) (graph : OriginGraph source.atoms)
    (origin : AtomOrigin cursor) : ℤ := nuclearInventory source.atoms origin-graph.formalCharge origin

def chargeWeight (weight : AtomOrigin cursor → ℤ) : Charges cursor →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ weight

def totalCharge : Charges cursor →ₗ[ℤ] ℤ := chargeWeight (fun _ => 1)

def reactionWeight (origin : AtomOrigin cursor) : ℤ := if reactionOrigin origin then 1 else 0

def reactionCharge : Charges cursor →ₗ[ℤ] ℤ := chargeWeight reactionWeight

def totalElectrons (source : Common before step raw) (graph : OriginGraph source.atoms) : ℤ :=
  totalCharge (nuclearInventory source.atoms)-totalCharge graph.formalCharge

def reactionElectrons (source : Common before step raw) (graph : OriginGraph source.atoms) : ℤ :=
  reactionCharge (nuclearInventory source.atoms)-reactionCharge graph.formalCharge

structure SourceBondAction (cursor : CPS1ReactiveNuclear.SourceCursor frame) where
  debit : SourceBond cursor
  credit : Option (SourceBond cursor)

def SourceBondAction.delta (action : SourceBondAction cursor) : Incidence cursor :=
  (action.credit.toList.map (fun bond => Finsupp.single bond 1)).sum-Finsupp.single action.debit 1

structure ChargedToken (cursor : CPS1ReactiveNuclear.SourceCursor frame) where
  chargeDonor : AtomOrigin cursor
  chargeReceiver : AtomOrigin cursor
  bond : Option (SourceBondAction cursor)

def ChargedToken.delta (token : ChargedToken cursor) : Charges cursor :=
  Finsupp.single token.chargeDonor 1-Finsupp.single token.chargeReceiver 1

def ChargedToken.incidenceDelta (token : ChargedToken cursor) : Incidence cursor :=
  (token.bond.toList.map SourceBondAction.delta).sum

def ChargedToken.debits (token : ChargedToken cursor) : List (SourceBond cursor) :=
  token.bond.toList.map SourceBondAction.debit

def ChargedToken.credits (token : ChargedToken cursor) : List (SourceBond cursor) :=
  token.bond.toList.flatMap (fun action => action.credit.toList)

def ChargedToken.safe (source : Common before step raw) (token : ChargedToken cursor) : Prop :=
  token.chargeDonor ∈ vertices source ∧ token.chargeReceiver ∈ vertices source ∧
    token.chargeDonor ≠ token.chargeReceiver ∧
    (∀ bond ∈ token.debits, bond ∈ source.bonds ∧
      bond.left ∈ vertices source ∧ bond.right ∈ vertices source) ∧
    ∀ bond ∈ token.credits, bond.left ∈ vertices source ∧ bond.right ∈ vertices source ∧ bond.left ≠ bond.right

def sourceHydrogenBond? (source : Common before step raw) (hydrogen donor : AtomOrigin cursor) : Option (SourceBond cursor) := do
  let actualH ← source.atoms.find? (fun atom => atom.origin == hydrogen)
  if actualH.descriptor.source.element == .H then
    source.bonds.find? (fun bond =>
      ((bond.left == donor && bond.right == hydrogen) ||
        (bond.left == hydrogen && bond.right == donor)) && bond.order == "SING")
  else none

def prepareCharged? (source : Common before step raw) : ChargedInstruction cursor → Option (ChargedToken cursor)
  | .electron donor receiver => some ⟨donor,receiver,none⟩
  | .proton hydrogen donor receiver => do
    let old ← sourceHydrogenBond? source hydrogen donor
    pure ⟨receiver,donor,some ⟨old,some {old with left := receiver,right := hydrogen}⟩⟩
  | .deprotonate hydrogen donor => do
    let old ← sourceHydrogenBond? source hydrogen donor
    pure ⟨hydrogen,donor,some ⟨old,none⟩⟩

def applyChargedToken {atoms : List (Atom cursor)} (graph : OriginGraph atoms)
    (token : ChargedToken cursor) : OriginGraph atoms :=
  ⟨graph.incidence+token.incidenceDelta,graph.formalCharge+token.delta⟩

structure ChargedState (source : Common before step raw) (_current : NativeCurrent source) where
  paid : List (ChargedToken cursor)

def ChargedState.graph {source : Common before step raw} {current : NativeCurrent source}
    (state : ChargedState source current) : OriginGraph source.atoms :=
  state.paid.foldl applyChargedToken (sourceGraph source)

def ChargedState.spent {source : Common before step raw} {current : NativeCurrent source}
    (state : ChargedState source current) : List (SourceBond cursor) :=
  state.paid.flatMap ChargedToken.debits

def ChargedState.boundaryFlow {source : Common before step raw} {current : NativeCurrent source}
    (state : ChargedState source current) : ℤ := (state.paid.map (fun token => reactionCharge token.delta)).sum

def ChargedState.record {source : Common before step raw} {current : NativeCurrent source}
    (state : ChargedState source current) (token : ChargedToken cursor) : ChargedState source current :=
  ⟨state.paid ++ [token]⟩

def ChargedState.whole {source : Common before step raw} {current : NativeCurrent source}
    (state : ChargedState source current) : NativeCurrent source × OriginGraph source.atoms := (current,state.graph)

def chargedInitial (source : Common before step raw) (current : NativeCurrent source) : ChargedState source current := ⟨[]⟩

def electronReady (source : Common before step raw) (graph : OriginGraph source.atoms) : Prop :=
  ∀ origin ∈ vertices source, 0 ≤ electronInventory source graph origin

inductive ChargedResidual (cursor : CPS1ReactiveNuclear.SourceCursor frame)
  | unresolvedInstruction (instruction : ChargedInstruction cursor)
  | invalidSourceToken
  | negativeElectronResource
  | electronShortage (origin : AtomOrigin cursor) (inventory : ℤ)
  | reusedSourceBond
  | bondShortage
  | occupiedBond
  | occupiedHydrogenPair

structure SourceChargedStep (source : Common before step raw) (current : NativeCurrent source) where
  before : ChargedState source current
  instruction : ChargedInstruction cursor
  token : ChargedToken cursor
  prepared : prepareCharged? source instruction = some token
  safe : token.safe source
  ready : electronReady source before.graph
  electronPaid : 1 ≤ electronInventory source before.graph token.chargeDonor
  unused : ∀ bond ∈ token.debits, bond ∉ before.spent
  debitPaid : ∀ bond ∈ token.debits, 1 ≤ before.graph.incidence bond
  creditFree : ∀ bond ∈ token.credits, before.graph.incidence bond = 0
  pairFree : ∀ bond ∈ token.credits, adjacent before.graph bond.left bond.right = false

def SourceChargedStep.after {source : Common before step raw} {current : NativeCurrent source}
    (event : SourceChargedStep source current) : ChargedState source current := event.before.record event.token

def stepCharged? (source : Common before step raw) (current : NativeCurrent source)
    (state : ChargedState source current) (instruction : ChargedInstruction cursor) :
    Except (ChargedResidual cursor) (SourceChargedStep source current) := by
  classical
  exact match prepared : prepareCharged? source instruction with
  | none => .error (.unresolvedInstruction instruction)
  | some token =>
    if safe : token.safe source then
      if ready : electronReady source state.graph then
        if paid : 1 ≤ electronInventory source state.graph token.chargeDonor then
          if unused : ∀ bond ∈ token.debits, bond ∉ state.spent then
            if debit : ∀ bond ∈ token.debits, 1 ≤ state.graph.incidence bond then
              if credit : ∀ bond ∈ token.credits, state.graph.incidence bond = 0 then
                if pairFree : ∀ bond ∈ token.credits, adjacent state.graph bond.left bond.right = false then
                  .ok ⟨state,instruction,token,prepared,safe,ready,paid,unused,debit,credit,pairFree⟩
                else .error .occupiedHydrogenPair
              else .error .occupiedBond
            else .error .bondShortage
          else .error .reusedSourceBond
        else .error (.electronShortage token.chargeDonor (electronInventory source state.graph token.chargeDonor))
      else .error .negativeElectronResource
    else .error .invalidSourceToken

theorem charged_record_graph {source : Common before step raw} {current : NativeCurrent source}
    (state : ChargedState source current) (token : ChargedToken cursor) :
    (state.record token).graph = applyChargedToken state.graph token := by
  simp only [ChargedState.record,ChargedState.graph,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem charged_step_graph {source : Common before step raw} {current : NativeCurrent source}
    (event : SourceChargedStep source current) :
    event.after.graph = applyChargedToken event.before.graph event.token := charged_record_graph _ _

theorem charged_step_before (source : Common before step raw) (current : NativeCurrent source)
    (state : ChargedState source current) (instruction : ChargedInstruction cursor)
    (event : SourceChargedStep source current) (actual : stepCharged? source current state instruction = .ok event) :
    event.before = state := by
  unfold stepCharged? at actual
  split at actual
  · cases actual
  · repeat' split at actual
    all_goals cases actual
    all_goals rfl

theorem charged_record_spent {source : Common before step raw} {current : NativeCurrent source}
    (state : ChargedState source current) (token : ChargedToken cursor) :
    (state.record token).spent = state.spent ++ token.debits := by
  simp only [ChargedState.record,ChargedState.spent,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]

theorem charged_step_spent_unique {source : Common before step raw} {current : NativeCurrent source}
    (event : SourceChargedStep source current) (unique : event.before.spent.Nodup) : event.after.spent.Nodup := by
  rw [SourceChargedStep.after,charged_record_spent]
  cases selected : event.token.bond with
  | none => simpa only [ChargedToken.debits,selected,Option.toList_none,List.map_nil,List.append_nil] using unique
  | some action =>
    simp only [ChargedToken.debits,selected,Option.toList_some,List.map_cons,List.map_nil]
    apply List.nodup_append.mpr
    refine ⟨unique,List.nodup_singleton _,?_⟩
    intro first firstHeld second secondHeld same
    have secondActual := List.mem_singleton.mp secondHeld
    have held : action.debit ∈ event.token.debits := by simp [ChargedToken.debits,selected]
    apply event.unused action.debit held
    rw [← secondActual,← same]
    exact firstHeld

theorem charged_electron_debit {source : Common before step raw} {current : NativeCurrent source}
    (event : SourceChargedStep source current) :
    electronInventory source event.after.graph event.token.chargeDonor =
      electronInventory source event.before.graph event.token.chargeDonor-1 := by
  rw [charged_step_graph]
  change nuclearInventory source.atoms event.token.chargeDonor-
    (event.before.graph.formalCharge event.token.chargeDonor+
      (Finsupp.single event.token.chargeDonor 1-Finsupp.single event.token.chargeReceiver 1 : Charges cursor) event.token.chargeDonor) = _
  rw [Finsupp.sub_apply,Finsupp.single_eq_same,Finsupp.single_eq_of_ne event.safe.2.2.1]
  unfold electronInventory
  ring

theorem charged_electron_credit {source : Common before step raw} {current : NativeCurrent source}
    (event : SourceChargedStep source current) :
    electronInventory source event.after.graph event.token.chargeReceiver =
      electronInventory source event.before.graph event.token.chargeReceiver+1 := by
  rw [charged_step_graph]
  change nuclearInventory source.atoms event.token.chargeReceiver-
    (event.before.graph.formalCharge event.token.chargeReceiver+
      (Finsupp.single event.token.chargeDonor 1-Finsupp.single event.token.chargeReceiver 1 : Charges cursor) event.token.chargeReceiver) = _
  rw [Finsupp.sub_apply,Finsupp.single_eq_of_ne (Ne.symm event.safe.2.2.1),Finsupp.single_eq_same]
  unfold electronInventory
  ring

theorem charged_electron_other {source : Common before step raw} {current : NativeCurrent source}
    (event : SourceChargedStep source current) (origin : AtomOrigin cursor)
    (notDonor : origin ≠ event.token.chargeDonor) (notReceiver : origin ≠ event.token.chargeReceiver) :
    electronInventory source event.after.graph origin = electronInventory source event.before.graph origin := by
  rw [charged_step_graph]
  simp [electronInventory,applyChargedToken,ChargedToken.delta,notDonor,notReceiver]

theorem charged_electron_ready {source : Common before step raw} {current : NativeCurrent source}
    (event : SourceChargedStep source current) : electronReady source event.after.graph := by
  intro origin held
  by_cases donor : origin = event.token.chargeDonor
  · subst origin
    rw [charged_electron_debit]
    exact sub_nonneg.mpr event.electronPaid
  · by_cases receiver : origin = event.token.chargeReceiver
    · subst origin
      rw [charged_electron_credit]
      have prior := event.ready _ held
      omega
    · rw [charged_electron_other event origin donor receiver]
      exact event.ready origin held

theorem charged_bond_distinct {source : Common before step raw} {current : NativeCurrent source}
    (event : SourceChargedStep source current) (action : SourceBondAction cursor)
    (selected : event.token.bond = some action) (credit : SourceBond cursor) (credited : action.credit = some credit) :
    action.debit ≠ credit := by
  have debitHeld : action.debit ∈ event.token.debits := by simp [ChargedToken.debits,selected]
  have creditHeld : credit ∈ event.token.credits := by simp [ChargedToken.credits,selected,credited]
  intro same
  have paid := event.debitPaid action.debit debitHeld
  rw [same,event.creditFree credit creditHeld] at paid
  norm_num at paid

theorem charged_bond_debit {source : Common before step raw} {current : NativeCurrent source}
    (event : SourceChargedStep source current) (action : SourceBondAction cursor)
    (selected : event.token.bond = some action) :
    event.after.graph.incidence action.debit = event.before.graph.incidence action.debit-1 := by
  have delta : event.token.incidenceDelta = action.delta := by simp [ChargedToken.incidenceDelta,selected]
  rw [charged_step_graph]
  change event.before.graph.incidence action.debit+event.token.incidenceDelta action.debit = _
  rw [delta]
  cases credited : action.credit with
  | none => simp [SourceBondAction.delta,credited,sub_eq_add_neg]
  | some credit =>
    have distinct := charged_bond_distinct event action selected credit credited
    simp [SourceBondAction.delta,credited,distinct,sub_eq_add_neg]

theorem charged_bond_credit {source : Common before step raw} {current : NativeCurrent source}
    (event : SourceChargedStep source current) (action : SourceBondAction cursor)
    (selected : event.token.bond = some action) (credit : SourceBond cursor) (credited : action.credit = some credit) :
    event.after.graph.incidence credit = 1 := by
  have delta : event.token.incidenceDelta = action.delta := by simp [ChargedToken.incidenceDelta,selected]
  have held : credit ∈ event.token.credits := by simp [ChargedToken.credits,selected,credited]
  have distinct := charged_bond_distinct event action selected credit credited
  rw [charged_step_graph]
  change event.before.graph.incidence credit+event.token.incidenceDelta credit = _
  rw [delta]
  simp [SourceBondAction.delta,credited,Ne.symm distinct,event.creditFree credit held]

theorem charged_deprotonate_data (source : Common before step raw) (hydrogen donor : AtomOrigin cursor) :
    prepareCharged? source (.deprotonate hydrogen donor) =
      (sourceHydrogenBond? source hydrogen donor).map (fun old => ⟨hydrogen,donor,some ⟨old,none⟩⟩) := by
  cases found : sourceHydrogenBond? source hydrogen donor with
  | none => simp [prepareCharged?,Bind.bind,found]
  | some old => simp [prepareCharged?,Bind.bind,found]

theorem charged_proton_data (source : Common before step raw) (hydrogen donor receiver : AtomOrigin cursor) :
    prepareCharged? source (.proton hydrogen donor receiver) =
      (sourceHydrogenBond? source hydrogen donor).map (fun old =>
        ⟨receiver,donor,some ⟨old,some {old with left := receiver,right := hydrogen}⟩⟩) := by
  cases found : sourceHydrogenBond? source hydrogen donor with
  | none => simp [prepareCharged?,Bind.bind,found]
  | some old => simp [prepareCharged?,Bind.bind,found]

theorem charged_token_total (token : ChargedToken cursor) : totalCharge token.delta = 0 := by
  simp [totalCharge,chargeWeight,ChargedToken.delta]

theorem charged_token_boundary (token : ChargedToken cursor) :
    reactionCharge token.delta = reactionWeight token.chargeDonor-reactionWeight token.chargeReceiver := by
  simp [reactionCharge,chargeWeight,ChargedToken.delta]

private theorem charged_fold_charge {atoms : List (Atom cursor)} (graph : OriginGraph atoms)
    (tokens : List (ChargedToken cursor)) :
    (tokens.foldl applyChargedToken graph).formalCharge = graph.formalCharge+(tokens.map ChargedToken.delta).sum := by
  induction tokens generalizing graph with
  | nil => simp
  | cons token rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp only [applyChargedToken,List.map_cons,List.sum_cons]
    abel

theorem charged_state_total (source : Common before step raw) (current : NativeCurrent source)
    (state : ChargedState source current) :
    totalCharge state.graph.formalCharge = totalCharge (chargeInventory source.atoms) := by
  rw [ChargedState.graph,charged_fold_charge,map_add,map_list_sum]
  simp only [List.map_map,Function.comp_def,charged_token_total]
  simp [sourceGraph]

theorem charged_state_boundary (source : Common before step raw) (current : NativeCurrent source)
    (state : ChargedState source current) :
    reactionCharge state.graph.formalCharge = reactionCharge (chargeInventory source.atoms)+state.boundaryFlow := by
  rw [ChargedState.graph,charged_fold_charge,map_add,map_list_sum]
  simp only [ChargedState.boundaryFlow,List.map_map,Function.comp_def,sourceGraph]

theorem charged_state_electron_total (source : Common before step raw) (current : NativeCurrent source)
    (state : ChargedState source current) : totalElectrons source state.graph = totalElectrons source (sourceGraph source) := by
  unfold totalElectrons
  rw [charged_state_total]
  rfl

structure SourceChargedRun (source : Common before step raw) (current : NativeCurrent source) where
  fired : List (SourceChargedStep source current)
  remaining : ChargedSourceWord cursor
  state : ChargedState source current
  residual : Option (ChargedResidual cursor)

private def runChargedFrom (source : Common before step raw) (current : NativeCurrent source)
    (word : ChargedSourceWord cursor) (state : ChargedState source current) : SourceChargedRun source current :=
  match word with
  | [] => ⟨[],[],state,none⟩
  | instruction :: rest => match stepCharged? source current state instruction with
    | .error failure => ⟨[],instruction :: rest,state,some failure⟩
    | .ok event =>
      let next := runChargedFrom source current rest event.after
      ⟨event :: next.fired,next.remaining,next.state,next.residual⟩

def runChargedWord (source : Common before step raw) (current : NativeCurrent source)
    (word : ChargedSourceWord cursor) : SourceChargedRun source current :=
  runChargedFrom source current word (chargedInitial source current)

private theorem run_charged_from_unique (source : Common before step raw) (current : NativeCurrent source)
    (word : ChargedSourceWord cursor) (state : ChargedState source current) (unique : state.spent.Nodup) :
    (runChargedFrom source current word state).state.spent.Nodup := by
  induction word generalizing state with
  | nil => exact unique
  | cons instruction rest ih =>
    cases actual : stepCharged? source current state instruction with
    | error failure => simpa only [runChargedFrom,actual] using unique
    | ok event =>
      have before := charged_step_before source current state instruction event actual
      have nextUnique := charged_step_spent_unique event (before.symm ▸ unique)
      simpa only [runChargedFrom,actual] using ih event.after nextUnique

theorem charged_run_unique (source : Common before step raw) (current : NativeCurrent source)
    (word : ChargedSourceWord cursor) : (runChargedWord source current word).state.spent.Nodup :=
  run_charged_from_unique source current word (chargedInitial source current) List.nodup_nil

theorem charged_run_whole (source : Common before step raw) (current : NativeCurrent source)
    (word : ChargedSourceWord cursor) :
    (runChargedWord source current word).state.whole.1 = current ∧
    (runChargedWord source current word).state.whole.1.nodes = current.nodes ∧
    (runChargedWord source current word).state.whole.1.occupied = current.occupied ∧
    (runChargedWord source current word).state.whole.1.remaining = current.remaining := ⟨rfl,rfl,rfl,rfl⟩

theorem charged_run_total (source : Common before step raw) (current : NativeCurrent source)
    (word : ChargedSourceWord cursor) :
    totalCharge (runChargedWord source current word).state.graph.formalCharge = totalCharge (chargeInventory source.atoms) ∧
      totalElectrons source (runChargedWord source current word).state.graph = totalElectrons source (sourceGraph source) :=
  ⟨charged_state_total source current _,charged_state_electron_total source current _⟩

private theorem charged_weight_atoms (weight : AtomOrigin cursor → ℤ) (value : Atom cursor → ℤ)
    (atoms : List (Atom cursor)) :
    chargeWeight weight ((atoms.map (fun atom => Finsupp.single atom.origin (value atom))).sum) =
      (atoms.map (fun atom => value atom*weight atom.origin)).sum := by
  induction atoms with
  | nil => simp
  | cons atom rest ih =>
    change chargeWeight weight (Finsupp.single atom.origin (value atom)+
      (rest.map (fun atom => Finsupp.single atom.origin (value atom))).sum) =
      value atom*weight atom.origin+(rest.map (fun atom => value atom*weight atom.origin)).sum
    rw [map_add,ih]
    simp [chargeWeight]

private theorem charged_reaction_weight (value : Atom cursor → ℤ) (atoms : List (Atom cursor)) :
    (atoms.map (fun atom => value atom*reactionWeight atom.origin)).sum =
      ((reactionAtoms atoms).map value).sum := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
    by_cases selected : reactionOrigin atom.origin
    · simpa [reactionAtoms,reactionWeight,selected] using ih
    · simpa [reactionAtoms,reactionWeight,selected] using ih

theorem charged_reaction_initial (source : Common before step raw) :
    reactionCharge (chargeInventory source.atoms) = descriptorCharge ((reactionAtoms source.atoms).map Atom.descriptor) := by
  change chargeWeight reactionWeight ((source.atoms.map (fun atom =>
    Finsupp.single atom.origin atom.descriptor.source.charge)).sum) = _
  rw [charged_weight_atoms,charged_reaction_weight]
  simp only [descriptorCharge,List.map_map,Function.comp_def]

theorem charged_reaction_nuclei (source : Common before step raw) :
    reactionCharge (nuclearInventory source.atoms) =
      ((reactionAtoms source.atoms).map (fun atom => (Charged.atomicNumber atom.descriptor.source.element : ℤ))).sum := by
  change chargeWeight reactionWeight ((source.atoms.map (fun atom =>
    Finsupp.single atom.origin (Charged.atomicNumber atom.descriptor.source.element : ℤ))).sum) = _
  rw [charged_weight_atoms,charged_reaction_weight]

theorem first_reaction_nucleus_budget :
    ((reactionDescriptors firstFuel).map (fun atom => (Charged.atomicNumber atom.source.element : ℤ))).sum = 553 := by decide

theorem charged_run_reaction_budget (source : Common before step raw) (current : NativeCurrent source)
    (word : ChargedSourceWord cursor) (fuel : raw.fuel = firstFuel) :
    (reactionAtoms source.atoms).length = 95 ∧
      reactionCharge (runChargedWord source current word).state.graph.formalCharge =
        -9+(runChargedWord source current word).state.boundaryFlow ∧
      reactionElectrons source (runChargedWord source current word).state.graph =
        562-(runChargedWord source current word).state.boundaryFlow := by
  have sourceBudget : (reactionAtoms source.atoms).length = 95 ∧
      descriptorCharge ((reactionAtoms source.atoms).map Atom.descriptor) = -9 := by
    rw [source.atomSource,fuel]
    exact ⟨(first_reaction_atoms_budget before.packet.source).1,
      (first_reaction_atoms_budget before.packet.source).2.1⟩
  have nuclei : reactionCharge (nuclearInventory source.atoms) = 553 := by
    rw [charged_reaction_nuclei,source.atomSource,fuel]
    have descriptors := reaction_descriptors_source before.packet.source firstFuel
    have measured := congrArg (fun atoms : List Graph.Atom =>
      (atoms.map (fun atom => (Charged.atomicNumber atom.source.element : ℤ))).sum) descriptors
    simp only [List.map_map,Function.comp_def] at measured
    exact measured.trans first_reaction_nucleus_budget
  have charge : reactionCharge (runChargedWord source current word).state.graph.formalCharge =
      -9+(runChargedWord source current word).state.boundaryFlow := by
    rw [charged_state_boundary,charged_reaction_initial,sourceBudget.2]
  refine ⟨sourceBudget.1,charge,?_⟩
  unfold reactionElectrons
  rw [nuclei,charge]
  ring

theorem charged_source_hydrogen (source : Common before step raw) (hydrogen donor : AtomOrigin cursor)
    (bond : SourceBond cursor) (actual : sourceHydrogenBond? source hydrogen donor = some bond) :
    ∃ atom ∈ source.atoms, atom.origin = hydrogen ∧ atom.descriptor.source.element = .H ∧ bond ∈ source.bonds := by
  unfold sourceHydrogenBond? at actual
  simp only [Bind.bind] at actual
  cases found : source.atoms.find? (fun atom => atom.origin == hydrogen) with
  | none => rw [found,Option.bind_none] at actual; cases actual
  | some atom =>
    rw [found,Option.bind_some] at actual
    split at actual
    · rename_i hydrogenElement
      refine ⟨atom,List.mem_of_find?_eq_some found,?_,?_,List.mem_of_find?_eq_some actual⟩
      · exact beq_iff_eq.mp (List.find?_some (p := fun candidate : Atom cursor => candidate.origin == hydrogen) found)
      · exact beq_iff_eq.mp hydrogenElement
    · cases actual

end
end CPS1MaterialIncidence
