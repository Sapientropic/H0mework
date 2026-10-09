import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LocalChemicalExecution.Source

set_option autoImplicit false
set_option maxHeartbeats 0

namespace CPS1EditingChemicalJoin
open CPS1ResourceExecution CPS1LocalChemicalExecution

/-- These are only external substrates. The ammonia is reserved from the
actual incoming inventory, and every other incoming token is retained. -/
def externalSubstrates (frame : CPS1Recycling.Frame) : Stock frame :=
  [molecule frame .atp,molecule frame .atp,molecule frame .bicarbonate]

theorem consume_existing_ammonia (frame : CPS1Recycling.Frame)
    (stock : Stock frame) (present : molecule frame .ammonia ∈ stock) :
    let result := execute frame (Source.chemistryProgram frame) (stock ++ externalSubstrates frame)
    result.fired = Source.chemistryProgram frame ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm (Source.chemistryProducts frame ++ stock.erase (molecule frame .ammonia)) := by
  apply Source.chemistry_complete
  apply ((List.perm_cons_erase present).append_right _).trans
  apply List.perm_iff_count.mpr
  intro species
  simp only [externalSubstrates,Source.chemistryInput,Chemistry.ammoniaInput,
    List.map_cons,List.map_nil,List.count_append,List.count_cons,List.count_nil]
  omega

end CPS1EditingChemicalJoin
