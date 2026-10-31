import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Decision.Controller.Patch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Decision.Controller

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat) (datum : Admission.Datum input (Admission.frame input depth count))
  (limit : Nat)

def terminalRowSource : LedgerTerminalRowSourceAt (source input depth count datum limit) where
  IncidenceOccurrenceAt := fun _ _ => PEmpty
  compile := fun impossible => impossible.elim

def ledgerCompiler : SourceNativeLedgerCompiler (source input depth count datum limit) where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := RawRowAt input depth count datum limit
  exact_incidence := fun _ => ()
  exact_lineage := by
    intro current occurrence targetSupport before after raw
    cases raw with
    | generated index => exact (rowEvolution input depth count datum limit _ index).toDebtLineage.lineage_eq
  writeRowSource := rowSource input depth count datum limit
  terminalRowSource := terminalRowSource input depth count datum limit
  compile := by
    intro current occurrence
    cases occurrence_eq_emitted input depth count datum limit occurrence
    exact .nativeWrite () rfl (emitted input depth count datum limit (next input depth count datum limit current))
      (patch input depth count datum limit current).toLedgerWriteEvolution
  compilePatch := by
    intro current occurrence
    cases occurrence_eq_emitted input depth count datum limit occurrence
    exact ⟨patch input depth count datum limit current, rfl⟩

def ledgerSource : SourceNativeLedgerSource (N input depth count) (V input depth count datum limit) where
  source := source input depth count datum limit
  ledgerCompiler := ledgerCompiler input depth count datum limit

def restructuringLaw : SourceNativeLedgerRestructuringLaw (source input depth count datum limit) :=
  identityOnlyWorldLedgerRestructuringLaw (source input depth count datum limit)
    ((N input depth count).anchorAt (supportAt input depth count datum (initial input depth count datum)))
    (fun support responsibility => (Admission.frame input depth count).native.openAt_subsingleton support.1 responsibility)

def restructuringCertification {current : (V input depth count datum limit).Current}
    (occurrence : (source input depth count datum limit).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt (restructuringLaw input depth count datum limit)
      ((ledgerCompiler input depth count datum limit).compile occurrence) := by
  cases occurrence_eq_emitted input depth count datum limit occurrence
  apply ExactLedgerRestructuringCertificationAt.ofInjective
  · change Function.Injective (fun entry =>
      ((patch input depth count datum limit current).toLedgerWriteEvolution.origin entry).1)
    intro left right same
    exact (origin_is_original_entry input depth count datum limit current left).symm.trans
      (same.trans (origin_is_original_entry input depth count datum limit current right))
  · change Function.Injective (fun entry =>
      ((patch input depth count datum limit current).toLedgerWriteEvolution.destination entry).1)
    intro left right same
    exact (destination_is_original_entry input depth count datum limit current left).symm.trans
      (same.trans (destination_is_original_entry input depth count datum limit current right))

def restructuringSource : SourceNativeRestructuringLedgerSource (N input depth count) (V input depth count datum limit) where
  source := source input depth count datum limit
  compiler := {
    ledgerCompiler := ledgerCompiler input depth count datum limit
    restructuringLaw := restructuringLaw input depth count datum limit
    certifyRestructuring := restructuringCertification input depth count datum limit }

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Decision.Controller
