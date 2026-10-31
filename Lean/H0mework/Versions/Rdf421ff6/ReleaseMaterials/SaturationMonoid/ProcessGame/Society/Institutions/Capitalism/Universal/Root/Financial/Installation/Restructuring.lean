import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Compiler
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Keys

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.AccountSource

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (start : Cursor.State input) (startPositive : 0 < Cursor.physicalVisitIndex input start)

noncomputable def restructuringLaw : SourceNativeLedgerRestructuringLaw (source input start startPositive) :=
  identityOnlyWorldLedgerRestructuringLaw (source input start startPositive)
    ((N input start).anchorAt (supportAt input start (initial input start startPositive)))
    (world_openAt_subsingleton input start.account.generated)

noncomputable def restructuringCertification {current : Current input start}
    (occurrence : (source input start startPositive).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt (restructuringLaw input start startPositive)
      ((ledgerCompiler input start startPositive).compile occurrence) := by
  cases occurrence_eq_emitted input start startPositive occurrence
  apply ExactLedgerRestructuringCertificationAt.ofInjective
  · change Function.Injective (fun entry =>
      ((patch input start startPositive current).toLedgerWriteEvolution.origin entry).1)
    rw [patch_origin]
    exact whole_origin_injective input start current
  · change Function.Injective (fun entry =>
      ((patch input start startPositive current).toLedgerWriteEvolution.destination entry).1)
    rw [patch_destination]
    exact whole_destination_injective input start current

noncomputable def restructuringSource : SourceNativeRestructuringLedgerSource (N input start) (V input start) where
  source := source input start startPositive
  compiler := {
    ledgerCompiler := ledgerCompiler input start startPositive
    restructuringLaw := restructuringLaw input start startPositive
    certifyRestructuring := restructuringCertification input start startPositive }

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.AccountSource
