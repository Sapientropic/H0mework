import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.AtomSectors

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence
noncomputable section
open CPS1PhosphorylExchange CPS1ElectronicSource CPS1AtomicDynamics
open scoped BigOperators InnerProductSpace Matrix

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : CPS1SameEventFunction.Classical.Raw}
  {before : CPS1SameEventFunction.Classical.Current cursor priorRaw}
  {step : CPS1SameEventFunction.Classical.NativeStep before priorRaw.time}
  {raw : Raw}

def nuclearSector? (source : Common before step raw) (address : Charged.Address) : Option (AtomSector source) :=
  match address with
  | .nucleus slot => if bounded : slot < source.atoms.length then some ⟨slot,bounded⟩ else none
  | .electron .. => none

theorem nuclear_sector_actual (source : Common before step raw) (current : NativeCurrent source)
    (address : Charged.Address) (index : AtomSector source) (actual : nuclearSector? source address = some index) :
    address = .nucleus index.val ∧ originAt? source.atoms address = some (sectorOrigin current index) := by
  unfold nuclearSector? at actual
  cases address with
  | electron slot orbital => cases actual
  | nucleus slot =>
    by_cases bounded : slot < source.atoms.length
    · have same : (⟨slot,bounded⟩ : AtomSector source) = index := by
        simpa only [dif_pos bounded,Option.some.injEq] using actual
      have addressSame : Charged.Address.nucleus slot = .nucleus index.val :=
        congrArg Charged.Address.nucleus (congrArg Fin.val same)
      refine ⟨addressSame,?_⟩
      rw [addressSame]
      simpa only [sector_nucleus_address] using sector_origin_actual current index
    · simp only [dif_neg bounded,reduceCtorEq] at actual

inductive NativeIncidenceResidual (cursor : CPS1ReactiveNuclear.SourceCursor frame)
  | unresolvedNucleus (address : Charged.Address)
  | noSourceBond
  | unsafeSourceToken
  | negativeElectronResource
  | electronShortage (origin : AtomOrigin cursor) (inventory : ℤ)
  | reusedSourceBond
  | bondShortage
  | occupiedBond
  | occupiedAtomPair

structure IncidenceSelection (source : Common before step raw) (current : NativeCurrent source) where
  centre : AtomSector source
  leaving : AtomSector source
  attacking : AtomSector source
  centreActual : nuclearSector? source current.channel.phosphorus = some centre
  leavingActual : nuclearSector? source current.channel.leavingOxygen = some leaving
  attackingActual : nuclearSector? source current.channel.attackingOxygen = some attacking
  bond : BondToken cursor
  bondActual : sourceToken? source current = some bond

def selectIncidence? (source : Common before step raw) (current : NativeCurrent source) :
    Except (NativeIncidenceResidual cursor) (IncidenceSelection source current) := by
  classical
  exact match centreActual : nuclearSector? source current.channel.phosphorus with
  | none => .error (.unresolvedNucleus current.channel.phosphorus)
  | some centre => match leavingActual : nuclearSector? source current.channel.leavingOxygen with
    | none => .error (.unresolvedNucleus current.channel.leavingOxygen)
    | some leaving => match attackingActual : nuclearSector? source current.channel.attackingOxygen with
      | none => .error (.unresolvedNucleus current.channel.attackingOxygen)
      | some attacking => match bondActual : sourceToken? source current with
        | none => .error .noSourceBond
        | some bond => .ok ⟨centre,leaving,attacking,centreActual,leavingActual,attackingActual,bond,bondActual⟩

def IncidenceSelection.token {source : Common before step raw} {current : NativeCurrent source}
    (selection : IncidenceSelection source current) : ChargedToken cursor :=
  ⟨sectorOrigin current selection.attacking,sectorOrigin current selection.leaving,
    some ⟨selection.bond.debit,some selection.bond.credit⟩⟩

theorem selected_source_bond_shape {source : Common before step raw} {current : NativeCurrent source}
    (selection : IncidenceSelection source current) :
    selection.bond.credit.left = sectorOrigin current selection.centre ∧
      selection.bond.credit.right = sectorOrigin current selection.attacking ∧
      selection.bond.debit.order = "SING" ∧ selection.bond.credit.order = "SING" ∧
      ((selection.bond.debit.left = sectorOrigin current selection.centre ∧
        selection.bond.debit.right = sectorOrigin current selection.leaving) ∨
       (selection.bond.debit.left = sectorOrigin current selection.leaving ∧
        selection.bond.debit.right = sectorOrigin current selection.centre)) := by
  have actual := selection.bondActual
  unfold sourceToken? at actual
  simp only [Bind.bind,Option.bind_eq_some_iff,Pure.pure,Option.some.injEq] at actual
  obtain ⟨centre,centreFound,leaving,leavingFound,attacking,attackingFound,old,oldFound,same⟩ := actual
  have centreSame : centre = sectorOrigin current selection.centre :=
    Option.some.inj (centreFound.symm.trans (nuclear_sector_actual source current _ _ selection.centreActual).2)
  have leavingSame : leaving = sectorOrigin current selection.leaving :=
    Option.some.inj (leavingFound.symm.trans (nuclear_sector_actual source current _ _ selection.leavingActual).2)
  have attackingSame : attacking = sectorOrigin current selection.attacking :=
    Option.some.inj (attackingFound.symm.trans (nuclear_sector_actual source current _ _ selection.attackingActual).2)
  have paid : ((old.left = centre ∧ old.right = leaving) ∨ (old.left = leaving ∧ old.right = centre)) ∧
      old.order = "SING" := by
    simpa only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] using List.find?_some oldFound
  rw [← same]
  simp only [centreSame,leavingSame,attackingSame] at paid ⊢
  exact ⟨True.intro,True.intro,paid.2,paid.2,paid.1⟩

-- This is the SING-grade boundary; every unselected source edge remains in the full graph.
def singBondBoundary (bond : SourceBond cursor) : Charges cursor :=
  if bond.order = "SING" then Finsupp.single bond.left 1+Finsupp.single bond.right 1 else 0

def singIncidenceBoundary : Incidence cursor →ₗ[ℤ] Charges cursor :=
  Finsupp.linearCombination ℤ singBondBoundary

theorem selected_incidence_delta {source : Common before step raw} {current : NativeCurrent source}
    (selection : IncidenceSelection source current) : selection.token.incidenceDelta = selection.bond.delta := by
  simp [IncidenceSelection.token,ChargedToken.incidenceDelta,SourceBondAction.delta,BondToken.delta]

theorem selected_valence_charge {source : Common before step raw} {current : NativeCurrent source}
    (selection : IncidenceSelection source current) :
    singIncidenceBoundary selection.token.incidenceDelta = selection.token.delta := by
  rw [selected_incidence_delta]
  obtain ⟨creditLeft,creditRight,debitOrder,creditOrder,debitEnds⟩ := selected_source_bond_shape selection
  simp only [singIncidenceBoundary,BondToken.delta,map_sub,Finsupp.linearCombination_single,one_smul,
    singBondBoundary,if_pos debitOrder,if_pos creditOrder]
  simp only [IncidenceSelection.token,ChargedToken.delta,creditLeft,creditRight]
  rcases debitEnds with ⟨left,right⟩ | ⟨left,right⟩
  · rw [left,right]
    abel
  · rw [left,right]
    abel

def IncidenceSelection.block {source : Common before step raw} {current : NativeCurrent source}
    (selection : IncidenceSelection source current) : Module.End ℂ SourceFermion :=
  ∑ pair : RawIndex current × RawIndex current,
    effectiveSourceFock current pair.1 pair.2 •
      physicalPair (atomCut current selection.leaving (rawField current pair.1))
        (atomCut current selection.attacking (rawField current pair.2))

def IncidenceSelection.complement {source : Common before step raw} {current : NativeCurrent source}
    (selection : IncidenceSelection source current) : Module.End ℂ SourceFermion :=
  sourceFockCAR current-selection.block

theorem selected_full_operator {source : Common before step raw} {current : NativeCurrent source}
    (selection : IncidenceSelection source current) : selection.block+selection.complement = sourceFockCAR current := by
  unfold IncidenceSelection.complement
  abel

theorem selected_literal_charge {source : Common before step raw} {current : NativeCurrent source}
    (selection : IncidenceSelection source current) (observed : AtomSector source) :
    selection.token.delta (sectorOrigin current observed) =
      -atomDelta current observed selection.leaving selection.attacking := by
  classical
  have originEqual (first second : AtomSector source) :
      sectorOrigin current first = sectorOrigin current second ↔ first = second :=
    (source_origin_injective source).eq_iff
  simp only [IncidenceSelection.token,ChargedToken.delta,Finsupp.sub_apply,Finsupp.single_apply,originEqual,atomDelta]
  by_cases leave : observed = selection.leaving <;> by_cases attack : observed = selection.attacking <;>
    simp [leave,attack,eq_comm]

theorem selected_physical_charge_commuting {source : Common before step raw} {current : NativeCurrent source}
    (selection : IncidenceSelection source current) (observed : AtomSector source) (state : SourceFermion) :
    atomNumber current observed (selection.block state)-selection.block (atomNumber current observed state) =
      (-(selection.token.delta (sectorOrigin current observed)) : ℂ) • selection.block state := by
  simp only [IncidenceSelection.block,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul]
  rw [← Finset.sum_sub_distrib,selected_literal_charge]
  simp only [Int.cast_neg,neg_neg,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro pair _
  rw [← smul_sub,atom_pair_integer,smul_smul,mul_comm]

structure NativeIncidenceTrace (source : Common before step raw) (current : NativeCurrent source) where
  selection : IncidenceSelection source current
  before : ChargedState source current
  safe : selection.token.safe source
  ready : electronReady source before.graph
  electronPaid : 1 ≤ electronInventory source before.graph selection.token.chargeDonor
  unused : ∀ bond ∈ selection.token.debits, bond ∉ before.spent
  debitPaid : ∀ bond ∈ selection.token.debits, 1 ≤ before.graph.incidence bond
  creditFree : ∀ bond ∈ selection.token.credits, before.graph.incidence bond = 0
  pairFree : ∀ bond ∈ selection.token.credits, adjacent before.graph bond.left bond.right = false

private def checkNativeIncidence? (source : Common before step raw) (current : NativeCurrent source)
    (selection : IncidenceSelection source current) (state : ChargedState source current) :
    Except (NativeIncidenceResidual cursor) (NativeIncidenceTrace source current) := by
  classical
  exact if safe : selection.token.safe source then
    if ready : electronReady source state.graph then
      if paid : 1 ≤ electronInventory source state.graph selection.token.chargeDonor then
        if unused : ∀ bond ∈ selection.token.debits, bond ∉ state.spent then
          if debit : ∀ bond ∈ selection.token.debits, 1 ≤ state.graph.incidence bond then
            if credit : ∀ bond ∈ selection.token.credits, state.graph.incidence bond = 0 then
              if pairFree : ∀ bond ∈ selection.token.credits, adjacent state.graph bond.left bond.right = false then
                .ok ⟨selection,state,safe,ready,paid,unused,debit,credit,pairFree⟩
              else .error .occupiedAtomPair
            else .error .occupiedBond
          else .error .bondShortage
        else .error .reusedSourceBond
      else .error (.electronShortage selection.token.chargeDonor (electronInventory source state.graph selection.token.chargeDonor))
    else .error .negativeElectronResource
  else .error .unsafeSourceToken

def nativeIncidence? (source : Common before step raw) (current : NativeCurrent source) :
    Except (NativeIncidenceResidual cursor) (NativeIncidenceTrace source current) :=
  match selectIncidence? source current with
  | .error residual => .error residual
  | .ok selection => checkNativeIncidence? source current selection (chargedInitial source current)

def NativeIncidenceTrace.after {source : Common before step raw} {current : NativeCurrent source}
    (trace : NativeIncidenceTrace source current) : ChargedState source current := trace.before.record trace.selection.token

def NativeIncidenceTrace.whole {source : Common before step raw} {current : NativeCurrent source}
    (trace : NativeIncidenceTrace source current) : NativeCurrent source × OriginGraph source.atoms :=
  (current,trace.after.graph)

def NativeIncidenceTrace.word {source : Common before step raw} {current : NativeCurrent source}
    (_trace : NativeIncidenceTrace source current) : List (AtomCARMonomial current) :=
  sourceAtomCARWord current

def NativeIncidenceTrace.phaseAt {source : Common before step raw} {current : NativeCurrent source}
    (_trace : NativeIncidenceTrace source current) (time : ℝ) :=
  atomUpdatedOccupation current time

def NativeIncidenceTrace.remaining {source : Common before step raw} {current : NativeCurrent source}
    (_trace : NativeIncidenceTrace source current) := current.remaining

theorem native_incidence_graph {source : Common before step raw} {current : NativeCurrent source}
    (trace : NativeIncidenceTrace source current) :
    trace.after.graph = applyChargedToken trace.before.graph trace.selection.token :=
  charged_record_graph _ _

theorem native_incidence_valence_charge {source : Common before step raw} {current : NativeCurrent source}
    (trace : NativeIncidenceTrace source current) :
    singIncidenceBoundary (trace.after.graph.incidence-trace.before.graph.incidence) =
      trace.after.graph.formalCharge-trace.before.graph.formalCharge := by
  rw [native_incidence_graph]
  simp only [applyChargedToken,add_sub_cancel_left]
  exact selected_valence_charge trace.selection

theorem native_incidence_full_phase {source : Common before step raw} {current : NativeCurrent source}
    (trace : NativeIncidenceTrace source current) :
    ((trace.word).map AtomCARMonomial.operator).sum =
      trace.selection.block+trace.selection.complement := by
  rw [selected_full_operator]
  exact source_atom_word_operator current

theorem native_incidence_atom_charge {source : Common before step raw} {current : NativeCurrent source}
    (trace : NativeIncidenceTrace source current) (observed : AtomSector source) (state : SourceFermion) :
    atomNumber current observed (trace.selection.block state)-
      trace.selection.block (atomNumber current observed state) =
        (-(singIncidenceBoundary (trace.after.graph.incidence-trace.before.graph.incidence)
          (sectorOrigin current observed)) : ℂ) • trace.selection.block state := by
  rw [native_incidence_graph]
  simp only [applyChargedToken,add_sub_cancel_left,selected_valence_charge]
  exact selected_physical_charge_commuting trace.selection observed state

theorem native_incidence_phase_gram {source : Common before step raw} {current : NativeCurrent source}
    (trace : NativeIncidenceTrace source current) (time : ℝ) :
    (trace.phaseAt time).conjTranspose * trace.phaseAt time = 1 :=
  atom_updated_gram current time

theorem native_incidence_phase_zero {source : Common before step raw} {current : NativeCurrent source}
    (trace : NativeIncidenceTrace source current) : trace.phaseAt 0 = atomOccupation current :=
  atom_updated_zero current

theorem native_incidence_cayley {source : Common before step raw} {current : NativeCurrent source}
    (trace : NativeIncidenceTrace source current) (time : ℝ) (slot : Electron source.nodes) :
    let after := CPS1ElectronicEvolution.fields (addressedBasis current) (trace.phaseAt time) slot
    after+(Complex.I*((time/2 : ℝ) : ℂ)) • physicalFock current after =
      currentField current slot-(Complex.I*((time/2 : ℝ) : ℂ)) • physicalFock current (currentField current slot) :=
  atom_actual_cayley current time slot

theorem native_incidence_whole {source : Common before step raw} {current : NativeCurrent source}
    (trace : NativeIncidenceTrace source current) :
    trace.whole.1 = current ∧ trace.whole.1.nodes = current.nodes ∧
      trace.whole.1.occupied = current.occupied ∧ trace.whole.1.materializedRaw = current.materializedRaw ∧
        trace.remaining = current.remaining := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem native_incidence_checked_before (source : Common before step raw) (current : NativeCurrent source)
    (trace : NativeIncidenceTrace source current) (actual : nativeIncidence? source current = .ok trace) :
    trace.before = chargedInitial source current := by
  unfold nativeIncidence? at actual
  split at actual
  · cases actual
  · unfold checkNativeIncidence? at actual
    repeat' split at actual
    all_goals cases actual
    all_goals rfl

theorem native_incidence_starts_full (source : Common before step raw) (current : NativeCurrent source)
    (trace : NativeIncidenceTrace source current) (actual : nativeIncidence? source current = .ok trace) :
    trace.before.graph = sourceGraph source ∧ trace.before.spent = [] := by
  rw [native_incidence_checked_before source current trace actual]
  exact ⟨rfl,rfl⟩

def resumeNativeIncidence? {source : Common before step raw} {current : NativeCurrent source}
    (trace : NativeIncidenceTrace source current) :
    Except (NativeIncidenceResidual cursor) (NativeIncidenceTrace source current) :=
  checkNativeIncidence? source current trace.selection trace.after

end
end CPS1MaterialIncidence
