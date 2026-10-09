import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicSource.Current
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicSource.SourceBudget

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1AtomicSource.Contract
open CPS1ResourceExecution CPS1LocalChemicalExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

def selectChain (frame : CPS1Recycling.Frame) : CPS1LocalChemicalExecution.Species frame → Option (Chain frame)
  | .chain source => some source
  | _ => none

def chains (frame : CPS1Recycling.Frame) (stock : CPS1LocalChemicalExecution.Stock frame) : List (Chain frame) :=
  stock.filterMap (selectChain frame)

theorem held_chain_readout (frame : CPS1Recycling.Frame) (stock : CPS1LocalChemicalExecution.Stock frame) :
    CPS1LocalChemicalExecution.Source.heldChain frame stock = (chains frame stock).head? := by
  induction stock with
  | nil => rfl
  | cons species rest ih => cases species <;> first | exact ih | rfl

theorem chains_retained (frame : CPS1Recycling.Frame) (stock : CPS1Reinitiation.Stock frame) :
    chains frame (stock.map CPS1LocalChemicalExecution.Species.retained) = [] := by
  induction stock with
  | nil => rfl
  | cons species rest ih => exact ih

theorem captured_chain (frame : CPS1Recycling.Frame) (stock : CPS1Reinitiation.Stock frame)
    (present : Actual.species frame ∈ stock) :
    chains frame (CPS1LocalChemicalExecution.Source.start frame stock).stock = [Chain.initial frame] := by
  have paid := CPS1LocalChemicalExecution.Source.start_consumes_current frame stock present
  have filtered := paid.1.filterMap (selectChain frame)
  change (chains frame (CPS1LocalChemicalExecution.Source.start frame stock).stock).Perm
    (Chain.initial frame :: chains frame ((stock.erase (Actual.species frame)).map Species.retained)) at filtered
  rw [chains_retained] at filtered
  exact List.perm_singleton.mp filtered

theorem filterMap_erase_none {A B : Type} [DecidableEq A] (f : A → Option B)
    (stock : List A) (removed : A) (none : f removed = Option.none) :
    (stock.erase removed).filterMap f = stock.filterMap f := by
  induction stock with
  | nil => rfl
  | cons head rest ih =>
    by_cases same : head = removed
    · subst head
      simp [none]
    · simp [same,List.filterMap_cons,ih]

theorem chemical_chains_unchanged (frame : CPS1Recycling.Frame)
    (stock next : CPS1LocalChemicalExecution.Stock frame)
    (paid : next.Perm (CPS1LocalChemicalExecution.Source.chemistryProducts frame ++
      stock.erase (molecule frame .ammonia))) : (chains frame next).Perm (chains frame stock) := by
  have filtered := paid.filterMap (selectChain frame)
  have ammonia : selectChain frame (molecule frame .ammonia) = none := rfl
  have erased := filterMap_erase_none (selectChain frame) stock (molecule frame .ammonia) ammonia
  have products : chains frame (CPS1LocalChemicalExecution.Source.chemistryProducts frame) = [] := rfl
  change (chains frame next).Perm (chains frame (CPS1LocalChemicalExecution.Source.chemistryProducts frame ++
    stock.erase (molecule frame .ammonia))) at filtered
  simp only [chains,List.filterMap_append] at filtered
  change (chains frame next).Perm (chains frame (CPS1LocalChemicalExecution.Source.chemistryProducts frame) ++
    chains frame (stock.erase (molecule frame .ammonia))) at filtered
  rw [products,List.nil_append] at filtered
  change (chains frame next).Perm ((stock.erase (molecule frame .ammonia)).filterMap (selectChain frame)) at filtered
  rw [erased] at filtered
  exact filtered

theorem editing_chains_empty (frame : CPS1Recycling.Frame) (stock : CPS1ResourceExecution.Stock) :
    chains frame (stock.map (CPS1EditingChemicalJoin.Source.editingSpecies frame)) = [] := by
  induction stock with
  | nil => rfl
  | cons species rest ih => exact ih

theorem joined_chains (frame : CPS1Recycling.Frame)
    (previous : CPS1LocalChemicalExecution.Source.Occurrence frame)
    (edits : Target.Edits) (water additional : Nat) :
    chains frame (CPS1EditingChemicalJoin.Source.fromActual frame previous edits water additional).current.stock =
      chains frame previous.current.stock := by
  simp only [CPS1EditingChemicalJoin.Source.fromActual,chains,List.filterMap_append]
  change chains frame previous.current.stock ++
    chains frame ((CPS1Deamination.Continuation.sourceContinuation edits water additional).stock.map
      (CPS1EditingChemicalJoin.Source.editingSpecies frame)) = _
  rw [editing_chains_empty,List.append_nil]
  rfl

theorem chemical_initial_chain (frame : CPS1Recycling.Frame)
    (previous : CPS1LocalChemicalExecution.Source.Occurrence frame)
    (edits : Target.Edits) (water additional : Nat) (next : CPS1EditingChemicalJoin.Source.Occurrence frame)
    (initial : chains frame previous.current.stock = [Chain.initial frame])
    (updated : next.current.stock.Perm (CPS1LocalChemicalExecution.Source.chemistryProducts frame ++
      (CPS1EditingChemicalJoin.Source.fromActual frame previous edits water additional).current.stock.erase
        (molecule frame .ammonia))) :
    CPS1LocalChemicalExecution.Source.heldChain frame next.current.stock = some (Chain.initial frame) := by
  have kept := chemical_chains_unchanged frame _ _ updated
  rw [joined_chains,initial] at kept
  have singleton := List.perm_singleton.mp kept
  rw [held_chain_readout,singleton]
  rfl

theorem actual_atomic_complete (edits : Target.Edits) (water additional : Nat)
    (path : CPS1Recycling.SplitSite)
    (recycleFeed recycleExtra : List CPS1Recycling.RawMaterial)
    (recyclingRaw : recycleFeed.Perm (CPS1Recycling.freshFuel ++ recycleExtra))
    (scanFeed scanExtra : List CPS1Reinitiation.RawMaterial)
    (scanningRaw : scanFeed.Perm (CPS1Reinitiation.rawFuel 151 ++ scanExtra))
    (bodyFeed bodyExtra : List CPS1Reinitiation.Handover.RawMaterial)
    (bodyRaw : bodyFeed.Perm (CPS1Reinitiation.Handover.rawFuel Program.originalPeptide.2 ++ bodyExtra))
    (depth : Nat) (generated : 0 < CPS1EditingChemicalJoin.EditingStock.paid edits water additional) :
    ∃ (frame : CPS1Recycling.Frame) (next : Current.Occurrence frame) (surplus : Current.Stock frame),
      Current.execution edits water additional path recycleFeed scanFeed bodyFeed depth = some ⟨frame,next⟩ ∧
      next.source = some (Chain.initial frame) ∧
      next.current.fired = [.atomize (Chain.initial frame)] ∧
      next.current.remaining = [] ∧ next.current.missing = none ∧
      next.current.stock.Perm (.atomic (Chain.initial frame) :: surplus) ∧
      (next.previous.current.stock.map Current.Species.retained).Perm
        (.retained (.chain (Chain.initial frame)) ::
          List.replicate (Current.protonDebt frame) (Current.proton frame) ++ surplus) ∧
      Current.ChainValid frame (Chain.initial frame) ∧
      (∀ element, (Graph.atoms (Current.graph frame (Chain.initial frame)) element : Int) =
        (Chain.initial frame).atoms frame element +
          (if element = .H then (Current.protonDebt frame : Int) else 0)) ∧
      Graph.charge (Current.graph frame (Chain.initial frame)) = (Current.protonDebt frame : Int) ∧
      Graph.dangling (Current.graph frame (Chain.initial frame)) = [] := by
  let frame := CPS1Recycling.Source.frame edits water additional
  let recycled := CPS1Recycling.run frame (CPS1Recycling.productiveEvents path) recycleFeed
  let prior := CPS1Reinitiation.run frame recycled path.after Molecules.mrna scanFeed
  let previous := CPS1Reinitiation.Handover.execute frame
    (CPS1Reinitiation.Handover.fullProgram path Molecules.mrna 151 Program.originalPeptide.2)
    (prior.stock ++ bodyFeed.map (CPS1Reinitiation.Handover.RawMaterial.species frame))
  let requested := CPS1StockRecursion.Source.requested frame path depth previous.stock
  let captured := CPS1LocalChemicalExecution.Source.fromCurrent frame requested
  let joined := CPS1EditingChemicalJoin.Source.fromActual frame captured edits water additional
  let chemical := CPS1EditingChemicalJoin.Source.advance frame joined
    CPS1LocalChemicalExecution.Source.chemicalActions CPS1EditingChemicalJoin.Source.rawFuel
  let next := Current.fromActual frame chemical
  have capture := CPS1LocalChemicalExecution.Source.actual_capture_complete edits water additional path
    recycleFeed recycleExtra recyclingRaw scanFeed scanExtra scanningRaw bodyFeed bodyExtra bodyRaw depth
  have present : Actual.species frame ∈ requested.current.stock := Actual.current_free_cps1 edits water additional path
    recycleFeed recycleExtra recyclingRaw scanFeed scanExtra scanningRaw bodyFeed bodyExtra bodyRaw depth
  have initial : chains frame captured.current.stock = [Chain.initial frame] := captured_chain frame _ present
  have chemicalPaid := CPS1EditingChemicalJoin.Source.execution_from_actual_capture edits water additional path
    recycleFeed scanFeed bodyFeed depth frame captured capture.1 generated capture.2.2.1 rfl
  have updated : chemical.current.stock.Perm (CPS1LocalChemicalExecution.Source.chemistryProducts frame ++
    joined.current.stock.erase (molecule frame .ammonia)) := chemicalPaid.2.1
  have held := chemical_initial_chain frame captured edits water additional chemical initial updated
  have budget : Current.protonDebt frame ≤ captured.current.stock.count (molecule frame .proton) :=
    SourceBudget.actual_capture_proton_budget edits water additional path
      recycleFeed recycleExtra recyclingRaw scanFeed scanExtra scanningRaw bodyFeed bodyExtra bodyRaw depth
  have enough : Current.protonDebt frame ≤
      (chemical.current.stock.map Current.Species.retained).count (Current.proton frame) := by
    rw [SourceBudget.retained_proton_count]
    exact budget.trans (SourceBudget.chemical_carries_protons frame captured edits water additional chemical updated)
  rcases Current.source_proton_payment frame chemical (Chain.initial frame) held enough with
    ⟨surplus,fired,remaining,noCut,inventory,debit⟩
  refine ⟨frame,next,surplus,?_,?_,fired,remaining,noCut,inventory,debit,
    Current.initial_valid frame,Current.chain_material frame _ (Current.initial_valid frame),
    Current.chain_charge frame _,Current.chain_no_dangling frame _⟩
  · simp only [Current.execution,Current.sourceExecution,chemicalPaid.1]
    rfl
  · simp only [next,Current.fromActual,held]

end CPS1AtomicSource.Contract

namespace CPS1AtomicSource

structure AtomicContract : Prop where
  actualAtomic : type_of% Contract.actual_atomic_complete
  atomMaterial : type_of% Current.chain_material
  charge : type_of% Current.chain_charge
  noDangling : type_of% Current.chain_no_dangling
  sourceProtonBudget : type_of% SourceBudget.actual_capture_proton_budget
  actualDebitInventory : type_of% Current.source_proton_payment
  inventoryBalance : type_of% Current.atomic_inventory_balance
  cut : type_of% Current.atomic_cut
  advanceSourceIdentity : type_of% Current.advance_retains_source
  originalAtoms : type_of% Graph.source_atom_payload
  originalComponentBonds : type_of% Graph.source_component_bond
  sourceChainValidity : type_of% Current.cleave_valid

theorem sourceGeneratedAtomic : AtomicContract :=
  ⟨Contract.actual_atomic_complete,Current.chain_material,Current.chain_charge,
    Current.chain_no_dangling,SourceBudget.actual_capture_proton_budget,
    Current.source_proton_payment,Current.atomic_inventory_balance,Current.atomic_cut,
    Current.advance_retains_source,Graph.source_atom_payload,Graph.source_component_bond,
    Current.cleave_valid⟩

end CPS1AtomicSource
