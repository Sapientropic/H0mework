import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission.Ledger
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.FiniteRows

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  {origin : frame.V.Current}
  (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame origin)

def rowsData : FiniteRows.Data (source frame registered) where
  emitted := emitted frame registered
  next := next frame registered
  evolution := wholeEvolution frame registered
  finite := entry_finite frame registered

abbrev patch := FiniteRows.patch (rowsData frame registered)

theorem source_choice (current : Current frame registered) :
    (source frame registered).toRootSource.actual.compile (emitted frame registered current) =
      if active : (frame.item? current.1).isSome = true then
        EvolutionAt.nativeWrite (V := V frame registered) ⟨active⟩
      else .continuedTransport ⟨Bool.eq_false_of_not_eq_true active⟩ := rfl

def terminalRowSource : LedgerTerminalRowSourceAt (source frame registered) where
  IncidenceOccurrenceAt := fun _ _ => PEmpty
  compile := fun impossible => impossible.elim

def sourcePacket {current : (V frame registered).Current}
    (occurrence : (source frame registered).toRootSource.actual.OccurrenceAt current) :
    Σ image : SourceNativeLedgerEvolutionAt (source frame registered) occurrence,
      SourceNativeFiniteLedgerPatchAt (source frame registered) (FiniteRows.RawRowAt (rowsData frame registered))
        (FiniteRows.rowSource (rowsData frame registered)) (terminalRowSource frame registered) image := by
  cases occurrence_eq_emitted frame registered occurrence
  exact if active : (frame.item? current.1).isSome = true then
    ⟨.nativeWrite ⟨active⟩ (by rw [source_choice]; exact dif_pos active)
      (emitted frame registered (next frame registered current)) (patch frame registered current).toLedgerWriteEvolution,
      ⟨patch frame registered current, rfl⟩⟩
  else
    ⟨.continuedTransport ⟨Bool.eq_false_of_not_eq_true active⟩ (by rw [source_choice]; exact dif_neg active)
      (emitted frame registered (next frame registered current)) (patch frame registered current).toLedgerWriteEvolution,
      ⟨patch frame registered current, rfl⟩⟩

def ledgerCompiler : SourceNativeLedgerCompiler (source frame registered) where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := FiniteRows.RawRowAt (rowsData frame registered)
  exact_incidence := fun _ => ()
  exact_lineage := by
    intro current occurrence targetSupport before after raw
    cases raw with
    | generated seed => exact (FiniteRows.rowEvolution (rowsData frame registered) _ seed).toDebtLineage.lineage_eq
  writeRowSource := FiniteRows.rowSource (rowsData frame registered)
  terminalRowSource := terminalRowSource frame registered
  compile := fun occurrence => (sourcePacket frame registered occurrence).1
  compilePatch := fun occurrence => (sourcePacket frame registered occurrence).2

def ledgerSource : SourceNativeLedgerSource (N frame registered) (V frame registered) where
  source := source frame registered
  ledgerCompiler := ledgerCompiler frame registered

def ledgerRoot : SourceNativeLedgerRootClosure (N frame registered) (V frame registered) where
  source := ledgerSource frame registered
  emitted := emitted frame registered
  compiler_commutes := by
    intro current
    change ((ledgerCompiler frame registered).compile (emitted frame registered current)).CommutesWith _
    dsimp only [ledgerCompiler, sourcePacket]
    split <;> rfl

theorem patch_destination (current : Current frame registered) :
    (patch frame registered current).toLedgerWriteEvolution.destination = (wholeEvolution frame registered current).destination :=
  FiniteRows.patch_destination (rowsData frame registered) current

theorem patch_origin (current : Current frame registered) :
    (patch frame registered current).toLedgerWriteEvolution.origin = (wholeEvolution frame registered current).origin :=
  FiniteRows.patch_origin (rowsData frame registered) current

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission
