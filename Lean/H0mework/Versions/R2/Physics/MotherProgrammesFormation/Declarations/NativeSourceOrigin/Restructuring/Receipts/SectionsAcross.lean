import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.FullTransport

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open MotherFullCompiler MotherSourcePrograms MotherObligationOrigin MotherRestructuringOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)
    (old : SourceNativeRestructuringLedgerCompiler original) (compiled : CompilationSection generated)
    (recover : ∀ point : Point original,
      (fullCompilationEquiv p point.2).symm (compiled (pointEquiv p point)) = old.ledgerCompiler.compile point.2)

def worldCertificateAtEquiv (point : Point original) :
    SourceNativeLedgerRestructuringCertificationAt old.restructuringLaw (old.ledgerCompiler.compile point.2) ≃
      SourceNativeLedgerRestructuringCertificationAt (worldLaw p old.restructuringLaw) (compiled (pointEquiv p point)) :=
  (fullCertificateEquiv p old.restructuringLaw point (old.ledgerCompiler.compile point.2)).trans
    (Equiv.cast (congrArg (SourceNativeLedgerRestructuringCertificationAt (worldLaw p old.restructuringLaw))
      ((congrArg (fullCompilationEquiv p point.2) (recover point)).symm.trans
        ((fullCompilationEquiv p point.2).apply_symm_apply (compiled (pointEquiv p point))))))

variable {sortsOut : Sorts} {familiesOut : Families sortsOut} (ops : Operations sortsOut familiesOut)
    (sorts : ∀ i, sortsOf old.restructuringLaw.vocabulary.base i ≃ sortsOut i)
    (families : FamilyMap sorts (familiesOf old.restructuringLaw.vocabulary) familiesOut)
    (across : OperationsAcross sorts families (operationsOf old.restructuringLaw.vocabulary) ops)

def completeCertificateAtEquiv (point : Point original) :
    SourceNativeLedgerRestructuringCertificationAt old.restructuringLaw (old.ledgerCompiler.compile point.2) ≃
      SourceNativeLedgerRestructuringCertificationAt (sourceLaw (worldLaw p old.restructuringLaw) ops sorts families across)
        (compiled (pointEquiv p point)) :=
  (worldCertificateAtEquiv p old compiled recover point).trans
    (nativeCertificationEquiv (worldLaw p old.restructuringLaw) ops sorts families across (compiled (pointEquiv p point)))

def completeCertificateSection :
    CertificationSection (law := sourceLaw (worldLaw p old.restructuringLaw) ops sorts families across) compiled :=
  Equiv.piCongr (pointEquiv p) (completeCertificateAtEquiv p old compiled recover ops sorts families across)
    (fun point => old.certifyRestructuring point.2)

theorem completeCertificateSection_recovers (point : Point original) :
    (completeCertificateAtEquiv p old compiled recover ops sorts families across point).symm
      (completeCertificateSection p old compiled recover ops sorts families across (pointEquiv p point)) =
        old.certifyRestructuring point.2 :=
  (congrArg (completeCertificateAtEquiv p old compiled recover ops sorts families across point).symm
    (Equiv.piCongr_apply_apply
      (Z := fun point : Point generated => SourceNativeLedgerRestructuringCertificationAt
        (sourceLaw (worldLaw p old.restructuringLaw) ops sorts families across) (compiled point))
      (pointEquiv p) (completeCertificateAtEquiv p old compiled recover ops sorts families across)
      (fun point => old.certifyRestructuring point.2) point)).trans
    ((completeCertificateAtEquiv p old compiled recover ops sorts families across point).symm_apply_apply _)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
