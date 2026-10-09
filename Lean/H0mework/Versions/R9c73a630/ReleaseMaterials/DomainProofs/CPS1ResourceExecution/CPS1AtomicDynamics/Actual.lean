import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Source

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1AtomicDynamics.Actual
noncomputable section
open CPS1ResourceExecution CPS1LocalChemicalExecution CPS1AtomicSource
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

def select (frame : CPS1Recycling.Frame) : Current.Species frame → Option (Chain frame)
  | .atomic chain => some chain | _ => none

def atomicChains (frame : CPS1Recycling.Frame) (stock : Current.Stock frame) : List (Chain frame) :=
  stock.filterMap (select frame)

theorem retained_empty (frame : CPS1Recycling.Frame) (stock : CPS1LocalChemicalExecution.Stock frame) :
    atomicChains frame (stock.map Current.Species.retained) = [] := by
  induction stock with
  | nil => rfl
  | cons species rest ih => exact ih

theorem held_readout (frame : CPS1Recycling.Frame) (stock : Current.Stock frame) :
    Source.heldAtomic frame stock = (atomicChains frame stock).head? := by
  induction stock with
  | nil => rfl
  | cons species rest ih => cases species <;> first | exact ih | rfl

theorem single_source (frame : CPS1Recycling.Frame) (next : Current.Occurrence frame)
    (chain : Chain frame) (surplus : Current.Stock frame)
    (input : (next.previous.current.stock.map Current.Species.retained).Perm
      (.retained (.chain chain) :: List.replicate (Current.protonDebt frame) (Current.proton frame) ++ surplus))
    (output : next.current.stock.Perm (.atomic chain :: surplus)) :
    Source.heldAtomic frame next.current.stock = some chain := by
  have before := input.filterMap (select frame)
  have protons : (List.replicate (Current.protonDebt frame) (Current.proton frame)).filterMap (select frame) = [] := by
    simp [Current.proton,molecule,select]
  change (atomicChains frame (next.previous.current.stock.map Current.Species.retained)).Perm
    ((.retained (.chain chain) :: List.replicate (Current.protonDebt frame) (Current.proton frame) ++ surplus).filterMap (select frame)) at before
  rw [retained_empty] at before
  simp only [List.filterMap_cons,select,List.filterMap_append,protons,List.nil_append] at before
  have empty : surplus.filterMap (select frame) = [] := List.perm_nil.mp before.symm
  have after := output.filterMap (select frame)
  change (atomicChains frame next.current.stock).Perm
    ((.atomic chain :: surplus).filterMap (select frame)) at after
  simp only [List.filterMap_cons,select,empty] at after
  have singleton := List.perm_singleton.mp after
  rw [held_readout,singleton]
  rfl

theorem actual_start (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed recycleExtra : List CPS1Recycling.RawMaterial)
    (recyclingRaw : recycleFeed.Perm (CPS1Recycling.freshFuel ++ recycleExtra))
    (scanFeed scanExtra : List CPS1Reinitiation.RawMaterial)
    (scanningRaw : scanFeed.Perm (CPS1Reinitiation.rawFuel 151 ++ scanExtra))
    (bodyFeed bodyExtra : List CPS1Reinitiation.Handover.RawMaterial)
    (bodyRaw : bodyFeed.Perm (CPS1Reinitiation.Handover.rawFuel Program.originalPeptide.2 ++ bodyExtra))
    (depth : Nat) (generated : 0 < CPS1EditingChemicalJoin.EditingStock.paid edits water additional)
    (actions : List Source.RawAction) :
    ∃ (frame : CPS1Recycling.Frame) (next : Source.Occurrence frame),
      Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth actions = some ⟨frame,next⟩ ∧
      next.current = Source.advance frame (Source.start frame next.previous) actions ∧
      (Source.start frame next.previous).stock.Perm (.body ⟨Chain.initial frame,[],0⟩ ::
        (next.previous.current.stock.erase (.atomic (Chain.initial frame))).map Species.retained) ∧
      (Source.start frame next.previous).captureRemaining = [] ∧
      (Source.start frame next.previous).cut = none ∧
      Current.ChainValid frame (Chain.initial frame) ∧
      Charged.charge (Body.particles frame ⟨Chain.initial frame,[],0⟩) = (Current.protonDebt frame : Int) := by
  rcases Contract.actual_atomic_complete edits water additional path recycleFeed recycleExtra recyclingRaw
    scanFeed scanExtra scanningRaw bodyFeed bodyExtra bodyRaw depth generated with
    ⟨frame,previous,surplus,actual,identity,fired,remaining,missing,output,input,valid,material,charge,dangling⟩
  have held := single_source frame previous (Chain.initial frame) surplus input output
  have paid := Source.start_current frame previous (Chain.initial frame) held
  refine ⟨frame,⟨previous,Source.advance frame (Source.start frame previous) actions⟩,?_,rfl,paid.1,paid.2.1,paid.2.2,valid,?_⟩
  · simp only [Source.execution,actual]
    rfl
  · exact Charged.generated_charge (CPS1LocalChemicalExecution.Actual.cps1 frame).word (Chain.initial frame).bonds

end
end CPS1AtomicDynamics.Actual
