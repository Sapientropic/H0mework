import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Continuation.Patch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Continuation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : Financial.Installation.Runtime.Frame input)
  (request : Request Party Good Port Technology Instrument)

def terminalRowSource : LedgerTerminalRowSourceAt (source input frame request) where
  IncidenceOccurrenceAt := fun _ _ => PEmpty
  compile := fun impossible => impossible.elim

def ledgerCompiler : SourceNativeLedgerCompiler (source input frame request) where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := RawRowAt input frame request
  exact_incidence := fun _ => ()
  exact_lineage := by
    intro current occurrence targetSupport before after raw
    cases raw with
    | generated index => exact (rowEvolution input frame request _ index).toDebtLineage.lineage_eq
  writeRowSource := rowSource input frame request
  terminalRowSource := terminalRowSource input frame request
  compile := by
    intro current occurrence
    cases occurrence_eq_emitted input frame request occurrence
    exact .nativeWrite () rfl (emitted input frame request (next input request current))
      (patch input frame request current).toLedgerWriteEvolution
  compilePatch := by
    intro current occurrence
    cases occurrence_eq_emitted input frame request occurrence
    exact ⟨patch input frame request current, rfl⟩

def ledgerSource : SourceNativeLedgerSource (N input frame) (V input frame request) where
  source := source input frame request
  ledgerCompiler := ledgerCompiler input frame request

def restructuringLaw : SourceNativeLedgerRestructuringLaw (source input frame request) :=
  identityOnlyWorldLedgerRestructuringLaw (source input frame request)
    ((N input frame).anchorAt (supportAt input frame (initial input frame)))
    (fun support responsibility => frame.native.openAt_subsingleton support.1 responsibility)

def restructuringCertification {current : (V input frame request).Current}
    (occurrence : (source input frame request).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt (restructuringLaw input frame request)
      ((ledgerCompiler input frame request).compile occurrence) := by
  cases occurrence_eq_emitted input frame request occurrence
  apply ExactLedgerRestructuringCertificationAt.ofInjective
  · change Function.Injective (fun entry =>
      ((patch input frame request current).toLedgerWriteEvolution.origin entry).1)
    intro left right same
    exact (origin_is_original_entry input frame request current left).symm.trans
      (same.trans (origin_is_original_entry input frame request current right))
  · change Function.Injective (fun entry =>
      ((patch input frame request current).toLedgerWriteEvolution.destination entry).1)
    intro left right same
    exact (destination_is_original_entry input frame request current left).symm.trans
      (same.trans (destination_is_original_entry input frame request current right))

def restructuringSource : SourceNativeRestructuringLedgerSource (N input frame) (V input frame request) where
  source := source input frame request
  compiler := {
    ledgerCompiler := ledgerCompiler input frame request
    restructuringLaw := restructuringLaw input frame request
    certifyRestructuring := restructuringCertification input frame request }

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Continuation
