import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.AmmoniaCurrent
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicSource.SourceBudget
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.Release

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
namespace CPS1SameEventFunction
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing CPS1BiologicalUpdate
variable {frame : CPS1Recycling.Frame}

theorem native_reactants_no_proton (reaction : Reaction) : reaction.reactants.count .proton = 0 := by
  cases reaction <;> simp [Reaction.reactants,factorStock]

private theorem charge_proton_credit (tail : List AA) : (credit (tail.map Reaction.charge)).count .proton = 0 := by
  induction tail with
  | nil => rfl
  | cons aa rest ih => simpa [credit,Inventory.credit,Reaction.products] using ih

private theorem elongation_proton_credit (chain : Peptide) (tail : List AA) :
    (credit (Program.compileElongation chain tail)).count .proton = 2*tail.length := by
  induction tail generalizing chain with
  | nil => rfl
  | cons aa rest ih =>
    have paid := ih (chain.extend aa)
    simp [credit,Inventory.credit,Program.compileElongation,Reaction.products] at paid ⊢
    omega

private theorem boundary_elongation_proton_credit (tail : List AA) :
    (credit (CPS1InitiationTermination.UnifiedBoundary.elongation tail)).count .proton = 2*tail.length := by
  cases tail with
  | nil => rfl
  | cons aa rest =>
    have paid := elongation_proton_credit (.M,[aa]) rest
    simp [CPS1InitiationTermination.UnifiedBoundary.elongation,credit,Inventory.credit,
      Reaction.products] at paid ⊢
    omega

theorem compiled_proton_credit (tail : List AA) :
    (credit (CPS1InitiationTermination.UnifiedBoundary.compile tail)).count .proton = 2*tail.length+3 := by
  have charge := charge_proton_credit tail
  have elongation := boundary_elongation_proton_credit tail
  cases tail <;>
    simp [CPS1InitiationTermination.UnifiedBoundary.compile,CPS1InitiationTermination.UnifiedBoundary.termination,
      credit,Inventory.credit,Reaction.products,factorStock,List.flatMap_append] at charge elongation ⊢ <;> omega

theorem translation_proton_budget {current : CPS1ReactiveField.Occurrence frame} {water : Nat} {raw : List RawSupply}
    (event : TranslationEvent current water raw) (complete : event.native.missing = none) :
    2*event.peptide.2.length+3 ≤ event.native.stock.count .proton := by
  have fired := (translation_release_is_new current water raw event complete).1
  have balance := event.whole.count_eq Species.proton
  have debited := CPS1EnzymeBath.BathAccounting.trace_count_zero Reaction.reactants Species.proton
    native_reactants_no_proton event.native.fired
  change (debit event.native.fired).count .proton = 0 at debited
  have credited : (credit event.native.fired).count .proton = 2*event.peptide.2.length+3 := by
    rw [fired,event.programSource]
    exact compiled_proton_credit event.peptide.2
  simp only [List.count_append,debited,Nat.add_zero,credited] at balance
  omega

theorem seed_observed_stock {current : CPS1ReactiveField.Occurrence frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} (seed : SourceSeed current water raw path [] []) :
    seed.observed.current.stock = seed.translation.native.stock.map
      (fun species => CPS1Reinitiation.Species.retained (CPS1Recycling.Species.old species)) := by
  have observed := congrArg (fun value : CPS1StockRecursion.Source.Observation seed.translation.generatedFrame => value.current.stock) seed.observedSource
  change seed.observed.current.stock = seed.recycled.stock.map CPS1Reinitiation.Species.retained at observed
  have recycled := congrArg (fun value : CPS1Recycling.ExecutionAt seed.translation.generatedFrame => value.stock) seed.actualRecycling
  simp only [CPS1Recycling.run,CPS1Recycling.compile,CPS1Recycling.currentStock,List.map_nil,List.append_nil,Inventory.execute] at recycled
  have native := congrArg (fun value : CPS1Recycling.Frame => value.native.stock) seed.translation.frameSource
  rw [native] at recycled
  rw [recycled,List.map_map] at observed
  exact observed

theorem seed_released_member {current : CPS1ReactiveField.Occurrence frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} (seed : SourceSeed current water raw path [] [])
    (complete : seed.translation.native.missing = none) :
    CPS1LocalChemicalExecution.Actual.species seed.translation.generatedFrame ∈ seed.observed.current.stock := by
  have born := (translation_release_is_new current water raw seed.translation complete).2.2
  have present : Species.releasedPeptide seed.translation.peptide ∈ seed.translation.native.stock :=
    List.count_pos_iff.mp (by omega)
  have same : CPS1LocalChemicalExecution.Actual.cps1 seed.translation.generatedFrame = seed.translation.peptide := by
    rw [seed.translation.frameSource]
    exact Prod.ext seed.translation.initiator.symm rfl
  rw [seed_observed_stock]
  change CPS1Reinitiation.Species.retained (CPS1Recycling.Species.old (.releasedPeptide
    (CPS1LocalChemicalExecution.Actual.cps1 seed.translation.generatedFrame))) ∈ _
  rw [same]
  exact List.mem_map_of_mem present

theorem seed_held_chain {current : CPS1ReactiveField.Occurrence frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} (seed : SourceSeed current water raw path [] [])
    (complete : seed.translation.native.missing = none) :
    CPS1LocalChemicalExecution.Source.heldChain seed.translation.generatedFrame seed.joined.current.stock =
      some (CPS1LocalChemicalExecution.Chain.initial seed.translation.generatedFrame) := by
  rw [seed.noReload,seed.actualCapture]
  dsimp only [CPS1LocalChemicalExecution.Source.fromCurrent]
  rw [CPS1AtomicSource.Contract.held_chain_readout]
  rw [CPS1AtomicSource.Contract.captured_chain _ _ (seed_released_member seed complete)]
  rfl

theorem seed_atomic_budget {current : CPS1ReactiveField.Occurrence frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} (seed : SourceSeed current water raw path [] [])
    (complete : seed.translation.native.missing = none) :
    CPS1AtomicSource.Current.protonDebt seed.translation.generatedFrame ≤
      (seed.joined.current.stock.map CPS1AtomicSource.Current.Species.retained).count
        (CPS1AtomicSource.Current.proton seed.translation.generatedFrame) := by
  have paid := translation_proton_budget seed.translation complete
  have bounded := CPS1AtomicSource.SourceBudget.required_proton_bound
    (CPS1LocalChemicalExecution.Actual.cps1 seed.translation.generatedFrame).word
  have length : (CPS1LocalChemicalExecution.Actual.cps1 seed.translation.generatedFrame).word.length =
      seed.translation.peptide.2.length+1 := by rw [seed.translation.frameSource]; rfl
  rw [length] at bounded
  change CPS1AtomicSource.Current.protonDebt seed.translation.generatedFrame ≤ _ at bounded
  have observed := congrArg (fun stock => stock.count (CPS1StockRecursion.Dictionary.old seed.translation.generatedFrame .proton))
    (seed_observed_stock seed)
  have mapped : (seed.translation.native.stock.map
      (fun species => CPS1Reinitiation.Species.retained (CPS1Recycling.Species.old species))).count
      (CPS1StockRecursion.Dictionary.old seed.translation.generatedFrame .proton) = seed.translation.native.stock.count .proton :=
    List.count_map_of_injective _ _ (fun _ _ same => CPS1Recycling.Species.old.inj (CPS1Reinitiation.Species.retained.inj same)) _
  rw [mapped] at observed
  rw [seed.noReload,seed.actualCapture]
  change _ ≤ ((CPS1LocalChemicalExecution.Source.start seed.translation.generatedFrame seed.observed.current.stock).stock.map
    CPS1AtomicSource.Current.Species.retained).count (CPS1AtomicSource.Current.proton seed.translation.generatedFrame)
  dsimp only [CPS1AtomicSource.Current.proton]
  rw [List.count_map_of_injective _ _ (fun _ _ same => CPS1AtomicSource.Current.Species.retained.inj same)]
  rw [CPS1AtomicSource.SourceBudget.capture_preserves_protons _ _ (seed_released_member seed complete),observed]
  omega

theorem seed_paid_atomic {current : CPS1ReactiveField.Occurrence frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} (seed : SourceSeed current water raw path [] [])
    (complete : seed.translation.native.missing = none) :
    ∃ surplus, seed.atomic.current.fired = [.atomize (CPS1LocalChemicalExecution.Chain.initial seed.translation.generatedFrame)] ∧
      seed.atomic.current.remaining = [] ∧ seed.atomic.current.missing = none ∧
      seed.atomic.current.stock.Perm (.atomic (CPS1LocalChemicalExecution.Chain.initial seed.translation.generatedFrame) :: surplus) := by
  rw [seed.actualAtomic]
  obtain ⟨surplus,fired,remaining,missing,stock,_⟩ := CPS1AtomicSource.Current.source_proton_payment
    seed.translation.generatedFrame seed.joined (CPS1LocalChemicalExecution.Chain.initial seed.translation.generatedFrame)
    (seed_held_chain seed complete) (seed_atomic_budget seed complete)
  exact ⟨surplus,fired,remaining,missing,stock⟩

end
end CPS1SameEventFunction
