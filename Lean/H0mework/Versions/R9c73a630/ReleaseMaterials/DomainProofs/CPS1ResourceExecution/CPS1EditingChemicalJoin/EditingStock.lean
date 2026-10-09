import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deamination.Continuation
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LocalChemicalExecution.Source

set_option autoImplicit false
set_option maxHeartbeats 0

namespace CPS1EditingChemicalJoin.EditingStock
open CPS1ResourceExecution CPS1LocalChemicalExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

def sourceSpecies (frame : CPS1Recycling.Frame) (species : CPS1ResourceExecution.Species) : Species frame :=
  .retained (CPS1StockRecursion.Dictionary.old frame species)

theorem sourceSpecies_injective (frame : CPS1Recycling.Frame) : Function.Injective (sourceSpecies frame) := by
  intro a b same
  simpa only [sourceSpecies,CPS1StockRecursion.Dictionary.old,
    Species.retained.injEq,CPS1Reinitiation.Species.retained.injEq,CPS1Recycling.Species.old.injEq] using same

def actualStock (frame : CPS1Recycling.Frame) (edits : Target.Edits) (water additional : Nat) : Stock frame :=
  (CPS1Deamination.Continuation.sourceContinuation edits water additional).stock.map (sourceSpecies frame)

abbrev paid (edits : Target.Edits) (water additional : Nat) : Nat :=
  min (water+additional) (CPS1Deamination.Source.sourceProgram edits).steps.length

theorem ammonia_count (frame : CPS1Recycling.Frame) (edits : Target.Edits) (water additional : Nat) :
    (actualStock frame edits water additional).count (molecule frame .ammonia) = paid edits water additional := by
  change ((CPS1Deamination.Continuation.sourceContinuation edits water additional).stock.map
    (sourceSpecies frame)).count (sourceSpecies frame .ammonia) = _
  rw [List.count_map_of_injective _ _ (sourceSpecies_injective frame)]
  exact (CPS1Deamination.Continuation.source_continuation_actual_readout edits water additional).2.1

theorem ammonia_present (frame : CPS1Recycling.Frame) (edits : Target.Edits) (water additional : Nat)
    (generated : 0 < paid edits water additional) :
    molecule frame .ammonia ∈ actualStock frame edits water additional := by
  apply List.count_pos_iff.mp
  rw [ammonia_count]
  exact generated

theorem reserve_one (frame : CPS1Recycling.Frame) (edits : Target.Edits) (water additional : Nat)
    (generated : 0 < paid edits water additional) :
    (actualStock frame edits water additional).Perm (molecule frame .ammonia ::
      ((CPS1Deamination.Continuation.sourceContinuation edits water additional).stock.erase
        CPS1ResourceExecution.Species.ammonia).map (sourceSpecies frame)) := by
  have present := ammonia_present frame edits water additional generated
  have reserved := List.perm_cons_erase present
  change ((CPS1Deamination.Continuation.sourceContinuation edits water additional).stock.map
    (sourceSpecies frame)).Perm (sourceSpecies frame .ammonia ::
      (((CPS1Deamination.Continuation.sourceContinuation edits water additional).stock.map
        (sourceSpecies frame)).erase (sourceSpecies frame .ammonia))) at reserved
  rw [← List.map_erase (sourceSpecies_injective frame)] at reserved
  exact reserved

theorem remaining_ammonia_count (frame : CPS1Recycling.Frame) (edits : Target.Edits) (water additional : Nat) :
    ((actualStock frame edits water additional).erase (molecule frame .ammonia)).count
      (molecule frame .ammonia) = paid edits water additional - 1 := by
  rw [List.count_erase_self,ammonia_count]

theorem dna_present (frame : CPS1Recycling.Frame) (edits : Target.Edits) (water additional : Nat) :
    sourceSpecies frame (.dna (CPS1Deamination.ExecutionReadout.prefixWord
      CPS1Deamination.Source.originalMinusAligned
      ((CPS1Deamination.Source.sourceProgram edits).steps.take (water+additional)))) ∈
      actualStock frame edits water additional := by
  unfold actualStock
  rw [(CPS1Deamination.Continuation.source_continuation_update edits water additional).2.2.1]
  apply List.mem_map.mpr
  exact ⟨_,List.mem_cons_self,rfl⟩

theorem dna_count (frame : CPS1Recycling.Frame) (edits : Target.Edits) (water additional : Nat) :
    (actualStock frame edits water additional).count
      (sourceSpecies frame (.dna (CPS1Deamination.ExecutionReadout.prefixWord
        CPS1Deamination.Source.originalMinusAligned
        ((CPS1Deamination.Source.sourceProgram edits).steps.take (water+additional))))) = 1 := by
  unfold actualStock
  rw [List.count_map_of_injective _ _ (sourceSpecies_injective frame)]
  rw [(CPS1Deamination.Continuation.source_continuation_update edits water additional).2.2.1]
  exact (CPS1Deamination.ExecutionReadout.working_stock_counts _ _ _).1

theorem water_count (frame : CPS1Recycling.Frame) (edits : Target.Edits) (water additional : Nat) :
    (actualStock frame edits water additional).count (molecule frame .water) =
      water+additional-(CPS1Deamination.Source.sourceProgram edits).steps.length := by
  change ((CPS1Deamination.Continuation.sourceContinuation edits water additional).stock.map
    (sourceSpecies frame)).count (sourceSpecies frame .water) = _
  rw [List.count_map_of_injective _ _ (sourceSpecies_injective frame)]
  exact (CPS1Deamination.Continuation.source_continuation_actual_readout edits water additional).2.2

end CPS1EditingChemicalJoin.EditingStock
