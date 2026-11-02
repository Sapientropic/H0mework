import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Patch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.AccountSource

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (start : Cursor.State input) (startPositive : 0 < Cursor.physicalVisitIndex input start)

def terminalRowSource : LedgerTerminalRowSourceAt (source input start startPositive) where
  IncidenceOccurrenceAt := fun _ _ => PEmpty
  compile := fun impossible => impossible.elim

noncomputable def ledgerCompiler : SourceNativeLedgerCompiler (source input start startPositive) where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := RawRowAt input start startPositive
  exact_incidence := fun _ => ()
  exact_lineage := by
    intro current occurrence targetSupport before after raw
    cases raw with
    | generated seed => exact (rowEvolution input start _ seed).toDebtLineage.lineage_eq
  writeRowSource := rowSource input start startPositive
  terminalRowSource := terminalRowSource input start startPositive
  compile := by
    intro current occurrence
    cases occurrence_eq_emitted input start startPositive occurrence
    exact .nativeWrite () rfl (emitted input start startPositive (next input start current))
      (patch input start startPositive current).toLedgerWriteEvolution
  compilePatch := by
    intro current occurrence
    cases occurrence_eq_emitted input start startPositive occurrence
    exact ⟨patch input start startPositive current, rfl⟩

noncomputable def ledgerSource : SourceNativeLedgerSource (N input start) (V input start) where
  source := source input start startPositive
  ledgerCompiler := ledgerCompiler input start startPositive

theorem original_whole_account_is_the_actual_next (current : Current input start) :
    (V input start).nativeTarget (current := current) () = next input start current := rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.AccountSource
