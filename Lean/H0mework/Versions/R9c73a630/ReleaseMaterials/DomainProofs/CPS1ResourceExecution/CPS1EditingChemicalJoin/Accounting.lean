import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EditingChemicalJoin.Source

set_option autoImplicit false
set_option maxHeartbeats 0

namespace CPS1EditingChemicalJoin.Accounting
open CPS1ResourceExecution CPS1LocalChemicalExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

abbrev dnaWord (edits : Target.Edits) (water additional : Nat) : List CPS1Deamination.Base :=
  CPS1Deamination.ExecutionReadout.prefixWord CPS1Deamination.Source.originalMinusAligned
    ((CPS1Deamination.Source.sourceProgram edits).steps.take (water+additional))

theorem joined_counts (frame : CPS1Recycling.Frame)
    (previous : CPS1LocalChemicalExecution.Source.Occurrence frame)
    (edits : Target.Edits) (water additional : Nat) :
    let joined := Source.fromActual frame previous edits water additional
    joined.current.stock.count (molecule frame .ammonia) =
      previous.current.stock.count (molecule frame .ammonia) + EditingStock.paid edits water additional ∧
    joined.current.stock.count (molecule frame .water) =
      previous.current.stock.count (molecule frame .water) +
        (water+additional-(CPS1Deamination.Source.sourceProgram edits).steps.length) ∧
    joined.current.stock.count (Source.editingSpecies frame (.dna (dnaWord edits water additional))) =
      previous.current.stock.count (Source.editingSpecies frame (.dna (dnaWord edits water additional))) + 1 := by
  dsimp only [Source.fromActual]
  simp only [List.count_append]
  exact ⟨congrArg (previous.current.stock.count (molecule frame .ammonia) + ·)
      (EditingStock.ammonia_count frame edits water additional),
    congrArg (previous.current.stock.count (molecule frame .water) + ·)
      (EditingStock.water_count frame edits water additional),
    congrArg (previous.current.stock.count (Source.editingSpecies frame (.dna (dnaWord edits water additional))) + ·)
      (EditingStock.dna_count frame edits water additional)⟩

theorem actual_chemical_counts (frame : CPS1Recycling.Frame)
    (previous : CPS1LocalChemicalExecution.Source.Occurrence frame)
    (edits : Target.Edits) (water additional : Nat)
    (generated : 0 < EditingStock.paid edits water additional)
    (captured : previous.current.captureRemaining = []) (pending : previous.current.pending = []) :
    let joined := Source.fromActual frame previous edits water additional
    let next := Source.advance frame joined CPS1LocalChemicalExecution.Source.chemicalActions Source.rawFuel
    next.current.stock.count (molecule frame .ammonia) =
      previous.current.stock.count (molecule frame .ammonia) + EditingStock.paid edits water additional - 1 ∧
    next.current.stock.count (molecule frame .water) =
      previous.current.stock.count (molecule frame .water) +
        (water+additional-(CPS1Deamination.Source.sourceProgram edits).steps.length) ∧
    next.current.stock.count (Source.editingSpecies frame (.dna (dnaWord edits water additional))) =
      previous.current.stock.count (Source.editingSpecies frame (.dna (dnaWord edits water additional))) + 1 ∧
    next.current.stock.count (molecule frame .carbamoylPhosphate) =
      joined.current.stock.count (molecule frame .carbamoylPhosphate) + 1 := by
  have paid := (Source.actual_chemical_from_join frame previous edits water additional generated captured pending).1
  have source := joined_counts frame previous edits water additional
  dsimp only
  have products (species : Species frame) :
      (CPS1LocalChemicalExecution.Source.chemistryProducts frame ++
        (Source.fromActual frame previous edits water additional).current.stock.erase (molecule frame .ammonia)).count species =
      (CPS1LocalChemicalExecution.Source.chemistryProducts frame).count species +
        ((Source.fromActual frame previous edits water additional).current.stock.erase (molecule frame .ammonia)).count species :=
    List.count_append
  constructor
  · have counted := paid.count_eq (molecule frame .ammonia)
    rw [products,List.count_erase_self] at counted
    have empty : (CPS1LocalChemicalExecution.Source.chemistryProducts frame).count (molecule frame .ammonia) = 0 := rfl
    rw [empty,Nat.zero_add,source.1] at counted
    exact counted
  constructor
  · have counted := paid.count_eq (molecule frame .water)
    rw [products,List.count_erase_of_ne (show molecule frame .water ≠ molecule frame .ammonia from by
      simp [molecule,CPS1StockRecursion.Dictionary.old])] at counted
    have empty : (CPS1LocalChemicalExecution.Source.chemistryProducts frame).count (molecule frame .water) = 0 := rfl
    rw [empty,Nat.zero_add,source.2.1] at counted
    exact counted
  constructor
  · have counted := paid.count_eq (Source.editingSpecies frame (.dna (dnaWord edits water additional)))
    rw [products,List.count_erase_of_ne (show Source.editingSpecies frame (.dna (dnaWord edits water additional)) ≠
        molecule frame .ammonia from by
      simp [molecule,Source.editingSpecies,CPS1StockRecursion.Dictionary.old])] at counted
    have empty : (CPS1LocalChemicalExecution.Source.chemistryProducts frame).count
        (Source.editingSpecies frame (.dna (dnaWord edits water additional))) = 0 := rfl
    rw [empty,Nat.zero_add,source.2.2] at counted
    exact counted
  · have counted := paid.count_eq (molecule frame .carbamoylPhosphate)
    rw [products,List.count_erase_of_ne (show molecule frame .carbamoylPhosphate ≠ molecule frame .ammonia from by
      simp [molecule])] at counted
    have one : (CPS1LocalChemicalExecution.Source.chemistryProducts frame).count (molecule frame .carbamoylPhosphate) = 1 := rfl
    rw [one,Nat.add_comm] at counted
    exact counted

end CPS1EditingChemicalJoin.Accounting
