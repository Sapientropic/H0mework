import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority.SourceFamily
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.OriginalRows
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Origin

/-! Dynamic instructions keep their actual trace ordinal inside the original
interpreter responsibility.  They do not borrow a fixed registration slot or
allocate an economic ledger of their own. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority.RootFace

open Program ProgrammeFace ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)

abbrev Visit := ActualBirth.Visit input
abbrev Item (visit : Visit input) := OriginalItem input.law
  (Root.ProgrammeSource.rawCurrent input visit.current) (Root.ProgrammeSource.rawEvent input visit.current)

omit [DecidableEq Port] in
theorem original_item_at_own_index (visit : Visit input) (item : Item input visit) :
    Registered.traceInstruction? input visit.current item.val.index = some item.val := by
  let actual : ContinuingEventAt (Root.ProgrammeSource.ledgerSource input) visit.current :=
    ⟨Root.ProgrammeSource.emitted input visit.current, rfl⟩
  have bound : item.val.index < (Registered.traceItems input visit.current).length := by
    simpa only [Registered.traceItems, RawLaw.rawItems, RawLaw.inventory_length] using
      original_index_bound input actual item
  unfold Registered.traceInstruction?
  rw [List.getElem?_eq_getElem bound]
  exact congrArg some (original_index_get input actual item)

def original (visit : Visit input) (item : Item input visit) : Root.Financial.InstructionOrigin input where
  visit := visit
  item := Registered.traceRow input visit.current
  traceIndex? := some item.val.index

omit [DecidableEq Port] in
theorem original_decodes_exact_item (visit : Visit input) (item : Item input visit) :
    (original input visit item).instruction? input = some item.val := by
  simp only [Root.Financial.InstructionOrigin.instruction?, original,
    Registered.traceRow_is_original_interpreter]
  exact original_item_at_own_index input visit item

def originalDisposition (visit : Visit input) (item : Item input visit) :=
  (original input visit item).disposition input

omit [DecidableEq Port] in
theorem original_row_is_same_interpreter (visit : Visit input) (item : Item input visit) :
    (original input visit item).row input = Registered.traceRow input visit.current := rfl

#print axioms original_decodes_exact_item
#print axioms original_row_is_same_interpreter

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority.RootFace
