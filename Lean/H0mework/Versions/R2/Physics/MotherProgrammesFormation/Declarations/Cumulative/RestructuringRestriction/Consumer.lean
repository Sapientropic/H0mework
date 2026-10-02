import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.RestructuringRestriction.Source

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringRestriction
open MotherFullCompiler MotherSourcePrograms MotherRestructuringOrigin MotherObligationOrigin MotherRestructuringReceipts
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
    {original : SourceNativeSource N V}
    (output : SourceNativeLedgerRootClosure G W)
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original output.source.source)
    (old : SourceNativeRestructuringLedgerCompiler original)
    (ledger : MotherAdmissionAlignment.CompilerPresentation p old.ledgerCompiler output.source.ledgerCompiler)
    (projection : SourceNativeProjectionLaw output.source)
    {sortsOut : Sorts} {familiesOut : Families sortsOut} (ops : Operations sortsOut familiesOut)
    (sorts : ∀ index, sortsOf old.restructuringLaw.vocabulary.base index ≃ sortsOut index)
    (families : FamilyMap sorts (familiesOf old.restructuringLaw.vocabulary) familiesOut)
    (across : OperationsAcross sorts families (operationsOf old.restructuringLaw.vocabulary) ops)

/-- The signed `compilerOf / completeCertificateSection` output supplies
every input to full restriction directly. No additional coverage assumption
is introduced between the formed source and the original compiler. -/
def presentationOfSections :
    let compiled := originalCompilations output.source.ledgerCompiler
    let law := sourceLaw (worldLaw p old.restructuringLaw) ops sorts families across
    let lawValue : LawValue := ⟨⟨⟨G, W, output⟩, projection⟩, law⟩
    let certificates := completeCertificateSection p old compiled ledger.compilation ops sorts families across
    Presentation p old (compilerOf lawValue certificates) ops sorts families across where
  ledger := ledger
  law_eq := rfl
  certificate := fun point =>
    completeCertificateSection_recovers p old (originalCompilations output.source.ledgerCompiler)
      ledger.compilation ops sorts families across point

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringRestriction
