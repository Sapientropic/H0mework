import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public.Rows

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (start : Cursor Party Good Port Technology Instrument)

def terminalRowSource : LedgerTerminalRowSourceAt (sourceAt input depth count prefixLimit renewalLimit oldPast start) where
  IncidenceOccurrenceAt := fun _ _ => PEmpty
  compile := fun impossible => impossible.elim

def ledgerCompiler : SourceNativeLedgerCompiler (sourceAt input depth count prefixLimit renewalLimit oldPast start) where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := RawRowAt input depth count prefixLimit renewalLimit oldPast start
  exact_incidence := fun _ => ()
  exact_lineage := by
    intro current occurrence targetSupport before after raw
    cases raw with
    | generated index => exact (rowEvolution input depth count prefixLimit renewalLimit oldPast _ index).toDebtLineage.lineage_eq
  writeRowSource := rowSource input depth count prefixLimit renewalLimit oldPast start
  terminalRowSource := terminalRowSource input depth count prefixLimit renewalLimit oldPast start
  compile := by
    intro current occurrence
    cases occurrence_eq_emitted input depth count prefixLimit renewalLimit oldPast start current occurrence
    by_cases written : materialWrite input depth count prefixLimit renewalLimit oldPast current = true
    · exact .nativeWrite ⟨written⟩ (by rw [compiler_eq_source_choice]; exact dif_pos written)
        (emitted input depth count prefixLimit renewalLimit oldPast start (next current))
        (patch input depth count prefixLimit renewalLimit oldPast start current).toLedgerWriteEvolution
    · exact .continuedTransport ⟨Bool.eq_false_of_not_eq_true written⟩ (by rw [compiler_eq_source_choice]; exact dif_neg written)
        (emitted input depth count prefixLimit renewalLimit oldPast start (next current))
        (patch input depth count prefixLimit renewalLimit oldPast start current).toLedgerWriteEvolution
  compilePatch := by
    intro current occurrence
    cases occurrence_eq_emitted input depth count prefixLimit renewalLimit oldPast start current occurrence
    simp only []
    split <;> exact ⟨patch input depth count prefixLimit renewalLimit oldPast start current, rfl⟩

def ledgerSource : SourceNativeLedgerSource (N input depth count) (V input depth count prefixLimit renewalLimit oldPast) where
  source := sourceAt input depth count prefixLimit renewalLimit oldPast start
  ledgerCompiler := ledgerCompiler input depth count prefixLimit renewalLimit oldPast start

def ledgerRoot : SourceNativeLedgerRootClosure (N input depth count) (V input depth count prefixLimit renewalLimit oldPast) where
  source := ledgerSource input depth count prefixLimit renewalLimit oldPast start
  emitted := emitted input depth count prefixLimit renewalLimit oldPast start
  compiler_commutes := by
    intro current
    change ((ledgerCompiler input depth count prefixLimit renewalLimit oldPast start).compile
      (emitted input depth count prefixLimit renewalLimit oldPast start current)).CommutesWith _
    dsimp only [ledgerCompiler]
    split <;> rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public
