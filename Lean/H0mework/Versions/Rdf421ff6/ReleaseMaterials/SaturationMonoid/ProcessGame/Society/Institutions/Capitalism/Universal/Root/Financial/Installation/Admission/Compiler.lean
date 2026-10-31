import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission.Patch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : NativeFrame input) {origin : frame.V.Current}
  (registered : Registration input frame origin)

def terminalRowSource : LedgerTerminalRowSourceAt (source input frame registered) where
  IncidenceOccurrenceAt := fun _ _ => PEmpty
  compile := fun impossible => impossible.elim

noncomputable def ledgerCompiler : SourceNativeLedgerCompiler (source input frame registered) where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := RawRowAt input frame registered
  exact_incidence := fun _ => ()
  exact_lineage := by
    intro current occurrence targetSupport before after raw
    cases raw with
    | generated seed => exact (rowEvolution input frame registered _ seed).toDebtLineage.lineage_eq
  writeRowSource := rowSource input frame registered
  terminalRowSource := terminalRowSource input frame registered
  compile := by
    intro current occurrence
    cases occurrence_eq_emitted input frame registered occurrence
    exact .nativeWrite () rfl (emitted input frame registered (next input frame registered current))
      (patch input frame registered current).toLedgerWriteEvolution
  compilePatch := by
    intro current occurrence
    cases occurrence_eq_emitted input frame registered occurrence
    exact ⟨patch input frame registered current, rfl⟩

noncomputable def ledgerSource : SourceNativeLedgerSource (N input frame registered) (V input frame registered) where
  source := source input frame registered
  ledgerCompiler := ledgerCompiler input frame registered

theorem original_joint_update_is_the_actual_next (current : Current input frame registered) :
    (V input frame registered).nativeTarget (current := current) () = next input frame registered current := rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission
