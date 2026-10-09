import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicSource.Current

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CPS1AtomicSource.SourceBudget
open CPS1ResourceExecution CPS1LocalChemicalExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

theorem additional_proton_bound (aa : AA) : Primary.additionalProtons aa ≤ 1 := by
  cases aa <;> decide +kernel

theorem required_proton_bound (word : List AA) : Graph.requiredProtons word ≤ word.length := by
  induction word with
  | nil => rfl
  | cons aa rest ih =>
    have head := additional_proton_bound aa
    simp only [Graph.requiredProtons,List.map_cons,List.sum_cons,List.length_cons] at ih ⊢
    omega

theorem actual_debt_bound (edits : Target.Edits) (water additional : Nat) :
    Current.protonDebt (CPS1Recycling.Source.frame edits water additional) ≤ 1500 := by
  have bound := required_proton_bound (Actual.cps1 (CPS1Recycling.Source.frame edits water additional)).word
  have length : (Actual.cps1 (CPS1Recycling.Source.frame edits water additional)).word.length =
      (CPS1EndogenousTranslation.selectedPeptide edits water additional).word.length := rfl
  rw [length] at bound
  apply bound.trans
  unfold CPS1EndogenousTranslation.selectedPeptide
  split
  · exact CPS1EndogenousTranslation.endogenous_lengths.1.le
  · have small := CPS1EndogenousTranslation.endogenous_lengths.2.1
    omega

theorem editor_proton_floor : 1500 ≤ 2 * Program.originalPeptide.2.length := by decide +kernel

theorem currency_proton_count (frame : CPS1Recycling.Frame) (tail : List AA) :
    ((CPS1StockRecursion.currencyWaste tail).map (CPS1StockRecursion.Dictionary.old frame)).count
      (CPS1StockRecursion.Dictionary.old frame .proton) = 2 * tail.length := by
  induction tail with
  | nil => rfl
  | cons aa rest ih =>
    change (([.gdp,.phosphate,.proton,.gdp,.phosphate,.proton] : CPS1ResourceExecution.Stock).map
      (CPS1StockRecursion.Dictionary.old frame) ++
      (CPS1StockRecursion.currencyWaste rest).map (CPS1StockRecursion.Dictionary.old frame)).count
      (CPS1StockRecursion.Dictionary.old frame .proton) = _
    rw [List.count_append,ih]
    have head : (([.gdp,.phosphate,.proton,.gdp,.phosphate,.proton] : CPS1ResourceExecution.Stock).map
      (CPS1StockRecursion.Dictionary.old frame)).count (CPS1StockRecursion.Dictionary.old frame .proton) = 2 := rfl
    rw [head]
    simp only [List.length_cons]
    omega

theorem initial_surplus_protons (frame : CPS1Recycling.Frame) (tail : List AA)
    (recycleExtra : List CPS1Recycling.RawMaterial) (scanExtra : List CPS1Reinitiation.RawMaterial)
    (bodyExtra : List CPS1Reinitiation.Handover.RawMaterial) :
    2 * tail.length ≤ (CPS1StockRecursion.Initial.surplus frame tail recycleExtra scanExtra bodyExtra).count
      (CPS1StockRecursion.Dictionary.old frame .proton) := by
  have currency := currency_proton_count frame tail
  simp only [CPS1StockRecursion.Initial.surplus,List.map_append,List.count_append,List.map_cons,List.map_nil,
    List.count_cons,List.count_nil] at currency ⊢
  omega

theorem requested_proton_floor (frame : CPS1Recycling.Frame) (tail : List AA) (depth : Nat)
    (recycleExtra : List CPS1Recycling.RawMaterial) (scanExtra : List CPS1Reinitiation.RawMaterial)
    (bodyExtra : List CPS1Reinitiation.Handover.RawMaterial) (stock : CPS1Reinitiation.Stock frame)
    (inventory : stock.Perm (CPS1StockRecursion.Native.reusable frame tail ++
      CPS1StockRecursion.Source.wastes frame depth ++
      CPS1StockRecursion.Initial.surplus frame tail recycleExtra scanExtra bodyExtra)) :
    2 * tail.length ≤ stock.count (CPS1StockRecursion.Dictionary.old frame .proton) := by
  have all := inventory.count_eq (CPS1StockRecursion.Dictionary.old frame .proton)
  have floor := initial_surplus_protons frame tail recycleExtra scanExtra bodyExtra
  simp only [List.count_append] at all
  omega

theorem capture_preserves_protons (frame : CPS1Recycling.Frame) (stock : CPS1Reinitiation.Stock frame)
    (present : Actual.species frame ∈ stock) :
    (CPS1LocalChemicalExecution.Source.start frame stock).stock.count (molecule frame .proton) =
      stock.count (CPS1StockRecursion.Dictionary.old frame .proton) := by
  have captured := (CPS1LocalChemicalExecution.Source.start_consumes_current frame stock present).1.count_eq
    (molecule frame .proton)
  have distinct : Actual.species frame ≠ CPS1StockRecursion.Dictionary.old frame .proton := by
    simp [Actual.species,Actual.cps1,CPS1StockRecursion.Dictionary.old]
  have injective : Function.Injective (Species.retained (frame := frame)) :=
    fun _ _ same => Species.retained.inj same
  have counted := List.count_map_of_injective (stock.erase (Actual.species frame))
    (Species.retained (frame := frame)) injective (CPS1StockRecursion.Dictionary.old frame .proton)
  simp only [List.count_cons] at captured
  have head : ((Species.chain (Chain.initial frame) : Species frame) == molecule frame .proton) = false := rfl
  rw [head] at captured
  simp only [Bool.false_eq_true,if_false,Nat.add_zero] at captured
  change List.count (molecule frame .proton)
      ((stock.erase (Actual.species frame)).map (Species.retained (frame := frame))) = _ at counted
  rw [counted,List.count_erase_of_ne distinct.symm] at captured
  exact captured

theorem actual_capture_proton_budget (edits : Target.Edits) (water additional : Nat)
    (path : CPS1Recycling.SplitSite)
    (recycleFeed recycleExtra : List CPS1Recycling.RawMaterial)
    (recyclingRaw : recycleFeed.Perm (CPS1Recycling.freshFuel ++ recycleExtra))
    (scanFeed scanExtra : List CPS1Reinitiation.RawMaterial)
    (scanningRaw : scanFeed.Perm (CPS1Reinitiation.rawFuel 151 ++ scanExtra))
    (bodyFeed bodyExtra : List CPS1Reinitiation.Handover.RawMaterial)
    (bodyRaw : bodyFeed.Perm (CPS1Reinitiation.Handover.rawFuel Program.originalPeptide.2 ++ bodyExtra))
    (depth : Nat) :
    let frame := CPS1Recycling.Source.frame edits water additional
    let recycled := CPS1Recycling.run frame (CPS1Recycling.productiveEvents path) recycleFeed
    let prior := CPS1Reinitiation.run frame recycled path.after Molecules.mrna scanFeed
    let previous := CPS1Reinitiation.Handover.execute frame
      (CPS1Reinitiation.Handover.fullProgram path Molecules.mrna 151 Program.originalPeptide.2)
      (prior.stock ++ bodyFeed.map (CPS1Reinitiation.Handover.RawMaterial.species frame))
    let result := CPS1StockRecursion.Source.requested frame path depth previous.stock
    Current.protonDebt frame ≤ (CPS1LocalChemicalExecution.Source.start frame result.current.stock).stock.count
      (molecule frame .proton) := by
  have generated := CPS1StockRecursion.Source.actual_requested_complete edits water additional path
    recycleFeed recycleExtra recyclingRaw scanFeed scanExtra scanningRaw bodyFeed bodyExtra bodyRaw depth
  have present := Actual.current_free_cps1 edits water additional path
    recycleFeed recycleExtra recyclingRaw scanFeed scanExtra scanningRaw bodyFeed bodyExtra bodyRaw depth
  dsimp only at generated present ⊢
  have floor := requested_proton_floor _ Program.originalPeptide.2 depth recycleExtra scanExtra bodyExtra _ generated.2.1
  have captured := capture_preserves_protons _ _ present
  have debt := actual_debt_bound edits water additional
  have abundance := editor_proton_floor
  omega

theorem chemical_carries_protons (frame : CPS1Recycling.Frame)
    (previous : CPS1LocalChemicalExecution.Source.Occurrence frame)
    (edits : Target.Edits) (water additional : Nat)
    (next : CPS1EditingChemicalJoin.Source.Occurrence frame)
    (updated : next.current.stock.Perm (CPS1LocalChemicalExecution.Source.chemistryProducts frame ++
      (CPS1EditingChemicalJoin.Source.fromActual frame previous edits water additional).current.stock.erase
        (molecule frame .ammonia))) :
    previous.current.stock.count (molecule frame .proton) ≤ next.current.stock.count (molecule frame .proton) := by
  have count := updated.count_eq (molecule frame .proton)
  rw [List.count_append,List.count_erase_of_ne (show molecule frame .proton ≠ molecule frame .ammonia from by
    simp [molecule,CPS1StockRecursion.Dictionary.old])] at count
  have produced : (CPS1LocalChemicalExecution.Source.chemistryProducts frame).count (molecule frame .proton) = 1 := rfl
  rw [produced] at count
  simp only [CPS1EditingChemicalJoin.Source.fromActual,List.count_append] at count
  omega

theorem retained_proton_count (frame : CPS1Recycling.Frame) (stock : CPS1LocalChemicalExecution.Stock frame) :
    (stock.map Current.Species.retained).count (Current.proton frame) = stock.count (molecule frame .proton) := by
  exact List.count_map_of_injective stock (Current.Species.retained (frame := frame))
    (fun _ _ same => Current.Species.retained.inj same) (molecule frame .proton)

end CPS1AtomicSource.SourceBudget
