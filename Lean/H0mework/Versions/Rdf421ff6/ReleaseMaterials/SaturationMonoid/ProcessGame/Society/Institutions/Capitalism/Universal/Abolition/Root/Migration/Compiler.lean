import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Migration.Rows

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Migration

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)

def terminalRowSource : LedgerTerminalRowSourceAt (source input depth count prefixLimit renewalLimit) where
  IncidenceOccurrenceAt := fun _ _ => PEmpty
  compile := fun impossible => impossible.elim

def ledgerCompiler : SourceNativeLedgerCompiler (source input depth count prefixLimit renewalLimit) where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := RawRowAt input depth count prefixLimit renewalLimit
  exact_incidence := fun _ => ()
  exact_lineage := by
    intro current occurrence targetSupport before after raw
    cases raw with
    | generated index => exact (rowEvolution input depth count prefixLimit renewalLimit _ index).toDebtLineage.lineage_eq
  writeRowSource := rowSource input depth count prefixLimit renewalLimit
  terminalRowSource := terminalRowSource input depth count prefixLimit renewalLimit
  compile := by
    intro current occurrence
    cases occurrence_eq_emitted input depth count prefixLimit renewalLimit occurrence
    exact .nativeWrite () rfl (emitted input depth count prefixLimit renewalLimit (current + 1))
      (patch input depth count prefixLimit renewalLimit current).toLedgerWriteEvolution
  compilePatch := by
    intro current occurrence
    cases occurrence_eq_emitted input depth count prefixLimit renewalLimit occurrence
    exact ⟨patch input depth count prefixLimit renewalLimit current, rfl⟩

def ledgerSource : SourceNativeLedgerSource (N input depth count) (V input depth count prefixLimit renewalLimit) where
  source := source input depth count prefixLimit renewalLimit
  ledgerCompiler := ledgerCompiler input depth count prefixLimit renewalLimit

def restructuringLaw : SourceNativeLedgerRestructuringLaw (source input depth count prefixLimit renewalLimit) :=
  identityOnlyWorldLedgerRestructuringLaw (source input depth count prefixLimit renewalLimit)
    ((N input depth count).anchorAt (supportAt input depth count prefixLimit renewalLimit 0))
    (fun support responsibility => (frame input depth count).native.openAt_subsingleton support.1 responsibility)

def restructuringCertification {current : (V input depth count prefixLimit renewalLimit).Current}
    (occurrence : (source input depth count prefixLimit renewalLimit).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt (restructuringLaw input depth count prefixLimit renewalLimit)
      ((ledgerCompiler input depth count prefixLimit renewalLimit).compile occurrence) := by
  cases occurrence_eq_emitted input depth count prefixLimit renewalLimit occurrence
  apply ExactLedgerRestructuringCertificationAt.ofInjective
  · change Function.Injective (fun entry =>
      ((patch input depth count prefixLimit renewalLimit current).toLedgerWriteEvolution.origin entry).1)
    intro left right same
    exact (origin_is_original_entry input depth count prefixLimit renewalLimit current left).symm.trans
      (same.trans (origin_is_original_entry input depth count prefixLimit renewalLimit current right))
  · change Function.Injective (fun entry =>
      ((patch input depth count prefixLimit renewalLimit current).toLedgerWriteEvolution.destination entry).1)
    intro left right same
    exact (destination_is_original_entry input depth count prefixLimit renewalLimit current left).symm.trans
      (same.trans (destination_is_original_entry input depth count prefixLimit renewalLimit current right))

def restructuringSource : SourceNativeRestructuringLedgerSource (N input depth count) (V input depth count prefixLimit renewalLimit) where
  source := source input depth count prefixLimit renewalLimit
  compiler := {
    ledgerCompiler := ledgerCompiler input depth count prefixLimit renewalLimit
    restructuringLaw := restructuringLaw input depth count prefixLimit renewalLimit
    certifyRestructuring := restructuringCertification input depth count prefixLimit renewalLimit }

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Migration
