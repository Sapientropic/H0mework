import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.RestructuringRestriction.Law

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringRestriction
open MotherFullCompiler MotherSourcePrograms MotherRestructuringOrigin MotherObligationOrigin MotherRestructuringReceipts
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)
    (old : SourceNativeRestructuringLedgerCompiler original)
    (actual : SourceNativeRestructuringLedgerCompiler generated)
    {sortsOut : Sorts} {familiesOut : Families sortsOut} (ops : Operations sortsOut familiesOut)
    (sorts : ∀ index, sortsOf old.restructuringLaw.vocabulary.base index ≃ sortsOut index)
    (families : FamilyMap sorts (familiesOf old.restructuringLaw.vocabulary) familiesOut)
    (across : OperationsAcross sorts families (operationsOf old.restructuringLaw.vocabulary) ops)

def readCertificate
    (ledger : MotherAdmissionAlignment.CompilerPresentation p old.ledgerCompiler actual.ledgerCompiler)
    (law_eq : actual.restructuringLaw = sourceLaw (worldLaw p old.restructuringLaw) ops sorts families across)
    (point : Point original) :
    SourceNativeLedgerRestructuringCertificationAt old.restructuringLaw (old.ledgerCompiler.compile point.2) :=
  (completeCertificateAtEquiv p old (originalCompilations actual.ledgerCompiler) ledger.compilation
    ops sorts families across point).symm
    (Equiv.cast (congrArg (fun law : SourceNativeLedgerRestructuringLaw generated =>
      SourceNativeLedgerRestructuringCertificationAt law (actual.ledgerCompiler.compile (pointEquiv p point).2)) law_eq)
      (actual.certifyRestructuring (pointEquiv p point).2))

/-- Coverage-side data already provided by the actual signed compiler
formation. The recovery equation concerns every complete native certificate. -/
structure Presentation where
  ledger : MotherAdmissionAlignment.CompilerPresentation p old.ledgerCompiler actual.ledgerCompiler
  law_eq : actual.restructuringLaw = sourceLaw (worldLaw p old.restructuringLaw) ops sorts families across
  certificate : ∀ point : Point original,
    readCertificate p old actual ops sorts families across ledger law_eq point = old.certifyRestructuring point.2

namespace Presentation

variable {p old actual ops sorts families across}
    (presentation : Presentation p old actual ops sorts families across)

def restrictCompiler : SourceNativeRestructuringLedgerCompiler original where
  ledgerCompiler := presentation.ledger.restrictLedgerCompiler
  restructuringLaw := restrictLaw p old.restructuringLaw ops sorts families across actual.restructuringLaw presentation.law_eq
  certifyRestructuring := fun {current} event =>
    Equiv.cast (congrArg₂ (fun (law : SourceNativeLedgerRestructuringLaw original)
      (ledger : SourceNativeLedgerCompiler original) => SourceNativeLedgerRestructuringCertificationAt law (ledger.compile event))
        (restrictLaw_eq p old.restructuringLaw ops sorts families across actual.restructuringLaw presentation.law_eq).symm
        presentation.ledger.restrictLedgerCompiler_eq.symm)
      (readCertificate p old actual ops sorts families across presentation.ledger presentation.law_eq ⟨current, event⟩)

private theorem assembled_restriction_eq (compiler : SourceNativeRestructuringLedgerCompiler original)
    (ledger : SourceNativeLedgerCompiler original) (ledger_eq : ledger = compiler.ledgerCompiler)
    (law : SourceNativeLedgerRestructuringLaw original) (law_eq : law = compiler.restructuringLaw)
    (certificates : (point : Point original) →
      SourceNativeLedgerRestructuringCertificationAt compiler.restructuringLaw (compiler.ledgerCompiler.compile point.2))
    (certificates_eq : certificates = fun (point : Point original) => compiler.certifyRestructuring point.2) :
    (show SourceNativeRestructuringLedgerCompiler original from {
      ledgerCompiler := ledger
      restructuringLaw := law
      certifyRestructuring := fun {current} event =>
        Equiv.cast (congrArg₂ (fun (l : SourceNativeLedgerRestructuringLaw original)
          (c : SourceNativeLedgerCompiler original) => SourceNativeLedgerRestructuringCertificationAt l (c.compile event))
            law_eq.symm ledger_eq.symm) (certificates ⟨current, event⟩) }) = compiler := by
  cases ledger_eq
  cases law_eq
  cases certificates_eq
  rfl

theorem restrictCompiler_eq : presentation.restrictCompiler = old :=
  assembled_restriction_eq old presentation.ledger.restrictLedgerCompiler presentation.ledger.restrictLedgerCompiler_eq
    (restrictLaw p old.restructuringLaw ops sorts families across actual.restructuringLaw presentation.law_eq)
    (restrictLaw_eq p old.restructuringLaw ops sorts families across actual.restructuringLaw presentation.law_eq)
    (readCertificate p old actual ops sorts families across presentation.ledger presentation.law_eq)
    (funext presentation.certificate)

end Presentation
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringRestriction
