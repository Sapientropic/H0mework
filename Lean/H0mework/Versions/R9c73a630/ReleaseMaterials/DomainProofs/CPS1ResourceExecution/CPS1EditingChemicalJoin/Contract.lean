import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EditingChemicalJoin.Accounting
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EditingChemicalJoin.Continuation

set_option autoImplicit false

namespace CPS1EditingChemicalJoin

structure EditingChemicalContract : Prop where
  actualSource : type_of% Source.actual_chemical_complete
  joinedInventory : type_of% Source.actual_join_stock
  sourceAmmonia : type_of% EditingStock.ammonia_count
  wholeDna : type_of% EditingStock.dna_count
  remainingWater : type_of% EditingStock.water_count
  actualUpdate : type_of% Source.advance_chemical_complete
  materialCounts : type_of% Accounting.actual_chemical_counts
  noRejoin : type_of% Continuation.advance_does_not_rejoin
  finiteCycles : type_of% Continuation.complete_cycles

theorem sourceGeneratedEditingChemical : EditingChemicalContract :=
  ⟨Source.actual_chemical_complete,Source.actual_join_stock,EditingStock.ammonia_count,
    EditingStock.dna_count,EditingStock.water_count,Source.advance_chemical_complete,
    Accounting.actual_chemical_counts,Continuation.advance_does_not_rejoin,Continuation.complete_cycles⟩

end CPS1EditingChemicalJoin
