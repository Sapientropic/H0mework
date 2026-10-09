import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.AtomicIngress
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Partner

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
namespace CPS1SameEventFunction
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing CPS1EnzymeBath.BathAccounting
variable {frame : CPS1Recycling.Frame}

theorem singleton_products_head {S R : Type} [DecidableEq S]
    (reactants products : R → List S) (reaction : R) (stock : List S) (head : S) (tail : List S)
    (produced : products reaction = head :: tail)
    (fired : (Inventory.execute reactants products [reaction] stock).fired = [reaction]) :
    ∃ remainder, (Inventory.execute reactants products [reaction] stock).stock = head :: (tail ++ remainder) ∧
      ∀ item ∈ remainder, item ∈ stock := by
  rw [Inventory.execute_cons] at fired ⊢
  cases actual : Inventory.fire reactants products reaction stock with
  | error missing => simp only [actual] at fired; cases fired
  | ok next =>
    change ∃ remainder, next = head :: (tail ++ remainder) ∧ ∀ item ∈ remainder, item ∈ stock
    unfold Inventory.fire at actual
    cases consumed : Inventory.consume (reactants reaction) stock with
    | error missing => simp only [consumed] at actual; cases actual
    | ok remainder =>
      simp only [consumed,Except.ok.injEq] at actual
      subst next
      rw [produced]
      refine ⟨remainder,rfl,?_⟩
      intro item held
      exact (Inventory.consume_perm _ _ _ consumed).mem_iff.mpr (List.mem_append_right _ held)

theorem seed_atomic_head {current : CPS1ReactiveField.Occurrence frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} (seed : SourceSeed current water raw path [] [])
    (complete : seed.translation.native.missing = none) :
    ∃ surplus, seed.atomic.current.stock = .atomic (CPS1LocalChemicalExecution.Chain.initial seed.translation.generatedFrame) :: surplus ∧
      ∀ item ∈ surplus, ∃ material, item = CPS1AtomicSource.Current.Species.retained material := by
  obtain ⟨_,fired,_,_,_⟩ := seed_paid_atomic seed complete
  rw [seed.actualAtomic] at fired ⊢
  unfold CPS1AtomicSource.Current.fromActual at fired ⊢
  rw [seed_held_chain seed complete] at fired ⊢
  obtain ⟨surplus,head,subset⟩ := singleton_products_head
    (CPS1AtomicSource.Current.Reaction.reactants seed.translation.generatedFrame)
    (CPS1AtomicSource.Current.Reaction.products seed.translation.generatedFrame)
    (.atomize (CPS1LocalChemicalExecution.Chain.initial seed.translation.generatedFrame))
    (seed.joined.current.stock.map CPS1AtomicSource.Current.Species.retained) _ [] rfl fired
  refine ⟨surplus,head,?_⟩
  intro item held
  obtain ⟨material,_,same⟩ := List.mem_map.mp (subset item held)
  exact ⟨material,same.symm⟩

theorem seed_atomic_no_cp {current : CPS1ReactiveField.Occurrence frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} (seed : SourceSeed current water raw path [] [])
    (complete : seed.translation.native.missing = none) : seed.atomic.current.stock.count (atomicCp seed.translation.generatedFrame) = 0 := by
  rw [seed.actualAtomic,atomic_cp_count,seed.noReload,seed.actualCapture]
  have captured := CPS1LocalChemicalExecution.Source.start_consumes_current seed.translation.generatedFrame
    seed.observed.current.stock (seed_released_member seed complete)
  have counts := captured.1.count_eq (sourceCp seed.translation.generatedFrame)
  have remaining : ((seed.observed.current.stock.erase (CPS1LocalChemicalExecution.Actual.species seed.translation.generatedFrame)).map
      CPS1LocalChemicalExecution.Species.retained).count (sourceCp seed.translation.generatedFrame) = 0 := by
    apply List.count_eq_zero.mpr
    simp [sourceCp,CPS1LocalChemicalExecution.molecule]
  simp only [List.count_cons,remaining] at counts
  exact counts

theorem atomic_advance_empty (cursor : CPS1AtomicDynamics.Source.Cursor frame)
    (captured : cursor.captureRemaining = []) (pending : cursor.pending = []) :
    (CPS1AtomicDynamics.Source.advance frame cursor []).stock = cursor.stock ∧
      (CPS1AtomicDynamics.Source.advance frame cursor []).pending = [] := by
  unfold CPS1AtomicDynamics.Source.advance
  simp only [List.flatMap_nil,List.append_nil,List.nil_append,captured,pending]
  cases CPS1AtomicDynamics.Source.heldBody frame cursor.stock <;>
    simp [CPS1AtomicDynamics.Source.program,CPS1AtomicDynamics.execute,Inventory.execute]

theorem seed_body_head {current : CPS1ReactiveField.Occurrence frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} (seed : SourceSeed current water raw path [] [])
    (complete : seed.translation.native.missing = none) :
    ∃ surplus, (CPS1AtomicDynamics.Source.resume seed.translation.generatedFrame
      (CPS1AtomicDynamics.Source.fromActual seed.translation.generatedFrame seed.atomic) []).current.stock =
        .body ⟨CPS1LocalChemicalExecution.Chain.initial seed.translation.generatedFrame,[],0⟩ :: surplus ∧
      (CPS1AtomicDynamics.Source.resume seed.translation.generatedFrame
        (CPS1AtomicDynamics.Source.fromActual seed.translation.generatedFrame seed.atomic) []).current.pending = [] := by
  obtain ⟨surplus,head,_⟩ := seed_atomic_head seed complete
  have held : CPS1AtomicDynamics.Source.heldAtomic seed.translation.generatedFrame seed.atomic.current.stock =
      some (CPS1LocalChemicalExecution.Chain.initial seed.translation.generatedFrame) := by rw [head]; rfl
  have captured := CPS1AtomicDynamics.Source.start_current seed.translation.generatedFrame seed.atomic _ held
  have unchanged := atomic_advance_empty (CPS1AtomicDynamics.Source.start seed.translation.generatedFrame seed.atomic) captured.2.1 rfl
  refine ⟨surplus.map CPS1AtomicDynamics.Species.retained,?_,unchanged.2⟩
  change (CPS1AtomicDynamics.Source.advance seed.translation.generatedFrame
    (CPS1AtomicDynamics.Source.start seed.translation.generatedFrame seed.atomic) []).stock = _
  rw [unchanged.1]
  unfold CPS1AtomicDynamics.Source.start
  rw [held,head]
  simp [CPS1AtomicDynamics.execute,Inventory.execute,Inventory.fire,CPS1AtomicDynamics.Reaction.reactants,
    CPS1AtomicDynamics.Reaction.products,Inventory.consume]

end
end CPS1SameEventFunction
