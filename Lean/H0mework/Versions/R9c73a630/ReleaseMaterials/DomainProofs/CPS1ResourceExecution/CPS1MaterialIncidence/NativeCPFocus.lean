import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualNativePaidReturn

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeCPContinuationProbe
noncomputable section
open CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange
open NativePaidEvent NativeCarbamoyl NativeAmmoniaDynamics NativeProducts

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}

structure EdgeFocus (source : Common before step raw) (bond : SourceBond cursor) where
  left : AtomSector source
  right : AtomSector source
  leftActual : originAt source left = bond.left
  rightActual : originAt source right = bond.right

private theorem sector_for_origin (origin : AtomOrigin cursor) (held : origin ∈ vertices source) :
    ∃ index : AtomSector source, originAt source index = origin := by
  obtain ⟨atom,member,actual⟩ := List.mem_map.mp held
  obtain ⟨slot,found⟩ := List.getElem?_of_mem member
  let index : AtomSector source := ⟨slot,(List.getElem?_eq_some_iff.mp found).1⟩
  refine ⟨index,?_⟩
  have same : source.atoms.get index = atom := (List.getElem?_eq_some_iff.mp found).2
  change (source.atoms.get index).origin = origin
  rw [same]
  exact actual

private theorem edge_focus_nonempty (bond : SourceBond cursor)
    (left : bond.left ∈ vertices source) (right : bond.right ∈ vertices source) :
    Nonempty (EdgeFocus source bond) := by
  obtain ⟨first,firstActual⟩ := sector_for_origin bond.left left
  obtain ⟨second,secondActual⟩ := sector_for_origin bond.right right
  exact ⟨⟨first,second,firstActual,secondActual⟩⟩

private theorem debit_focus {state : ChargedState source current} {token : ChargedToken cursor}
    (event : TokenStep state token) (bond : SourceBond cursor) (held : bond ∈ token.debits) :
    Nonempty (EdgeFocus source bond) := by
  have vertices := event.safe.2.2.2.1 bond held
  exact edge_focus_nonempty bond vertices.2.1 vertices.2.2

private theorem credit_focus {state : ChargedState source current} {token : ChargedToken cursor}
    (event : TokenStep state token) (bond : SourceBond cursor) (held : bond ∈ token.credits) :
    Nonempty (EdgeFocus source bond) := by
  have vertices := event.safe.2.2.2.2 bond held
  exact edge_focus_nonempty bond vertices.1 vertices.2.1

structure CPFocus (paid : SourceGeneratedPaidReturn source current) where
  protonLeaving : EdgeFocus source (nitrogenHydrogen source)
  protonForming : EdgeFocus source
    (protonCredit source paid.parent.products.dynamics.origin.material.products.bicarbonate)
  hydroxylLeaving : EdgeFocus source
    (oxygenHydrogen paid.parent.products.dynamics.origin.material.products.bicarbonate)
  atpLeaving : EdgeFocus source (sourceDebit paid.parent.products.serial.sites.atp)
  atpForming : EdgeFocus source (phosphorylationCredit paid.parent.products.serial.sites.atp
    paid.parent.products.dynamics.origin.material.products.bicarbonate)
  protonActual : type_of% paid.parent.products.serial.proton_actual
  deprotonateActual : type_of% paid.parent.products.serial.deprotonate_actual
  phosphorylateActual : type_of% paid.parent.products.serial.phosphorylate_actual

theorem source_cp_focus (paid : SourceGeneratedPaidReturn source current) : Nonempty (CPFocus paid) := by
  let serial := paid.parent.products.serial
  let bct := paid.parent.products.dynamics.origin.material.products.bicarbonate
  obtain ⟨protonLeaving⟩ := debit_focus serial.proton (nitrogenHydrogen source)
    (by simp only [protonToken,ChargedToken.debits,Option.toList_some,List.map_cons,List.map_nil,List.mem_singleton])
  obtain ⟨protonForming⟩ := credit_focus serial.proton (protonCredit source bct)
    (by simp [bct,protonToken,ChargedToken.credits,protonCredit])
  obtain ⟨hydroxylLeaving⟩ := debit_focus serial.deprotonate (oxygenHydrogen bct)
    (by simp [bct,deprotonateToken,ChargedToken.debits])
  obtain ⟨atpLeaving⟩ := debit_focus serial.phosphorylate (sourceDebit serial.sites.atp)
    (by simp [phosphorylationToken,ChargedToken.debits])
  obtain ⟨atpForming⟩ := credit_focus serial.phosphorylate (phosphorylationCredit serial.sites.atp bct)
    (by simp [bct,phosphorylationToken,ChargedToken.credits])
  exact ⟨⟨protonLeaving,protonForming,hydroxylLeaving,atpLeaving,atpForming,
    serial.proton_actual,serial.deprotonate_actual,serial.phosphorylate_actual⟩⟩

def EdgeFocus.read {bond : SourceBond cursor} (focus : EdgeFocus source bond) (state : PostState current) : ℝ :=
  bondRead state focus.left focus.right

def StrictDirection {paid : SourceGeneratedPaidReturn source current} (focus : CPFocus paid)
    (before after : PostState current) : Prop :=
  focus.protonLeaving.read after < focus.protonLeaving.read before ∧
    focus.protonForming.read before < focus.protonForming.read after ∧
    focus.hydroxylLeaving.read after < focus.hydroxylLeaving.read before ∧
    focus.atpLeaving.read after < focus.atpLeaving.read before ∧
    focus.atpForming.read before < focus.atpForming.read after

theorem strict_direction_irrefl {paid : SourceGeneratedPaidReturn source current}
    (focus : CPFocus paid) (state : PostState current) : ¬ StrictDirection focus state state := by
  intro strict
  exact lt_irrefl _ strict.1

end
end CPS1MaterialIncidence.NativeCPContinuationProbe
