import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.ClassificationAcross

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open MotherNetworkFactory MotherRestructuringOrigin MotherObligationOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (old : SourceNativeRestructuringLedgerCompiler source)
    {generated : Sorts} {outputFamilies : Families generated} (ops : Operations generated outputFamilies)
    (sorts : ∀ i, sortsOf old.restructuringLaw.vocabulary.base i ≃ generated i)
    (families : FamilyMap sorts (familiesOf old.restructuringLaw.vocabulary) outputFamilies)
    (p : OperationsAcross sorts families (operationsOf old.restructuringLaw.vocabulary) ops)

def vocabularyCompiler : SourceNativeRestructuringLedgerCompiler source where
  ledgerCompiler := old.ledgerCompiler
  restructuringLaw := sourceLaw old.restructuringLaw ops sorts families p
  certifyRestructuring := fun {_current} event =>
    nativeCertificationEquiv old.restructuringLaw ops sorts families p (old.ledgerCompiler.compile event) (old.certifyRestructuring event)

theorem certificate_recovers {current : V.Current} (event : source.toRootSource.actual.OccurrenceAt current) :
    (nativeCertificationEquiv old.restructuringLaw ops sorts families p (old.ledgerCompiler.compile event)).symm
      ((vocabularyCompiler old ops sorts families p).certifyRestructuring event) = old.certifyRestructuring event :=
  (nativeCertificationEquiv old.restructuringLaw ops sorts families p (old.ledgerCompiler.compile event)).symm_apply_apply _

/-- The formed vocabulary is consumed by the original whole compiler. Its
complete certification, including original branch choices and sealed
split/merge receipts, recovers at every original event. -/
theorem formed_vocabulary_consumes_full_original_compiler
    (sortCode : (Σ index, sortsOf old.restructuringLaw.vocabulary.base index) ↪ B)
    (familyCode : FamilyTotal (familiesOf old.restructuringLaw.vocabulary) ↪ B) :
    ∃ material base families : M,
      ∃ ops : Operations (formedSorts base) (formedFamilies base families),
      ∃ sorts : (index : Fin 12) → sortsOf old.restructuringLaw.vocabulary.base index ≃ formedSorts base index,
      ∃ familyMap : FamilyMap sorts (familiesOf old.restructuringLaw.vocabulary) (formedFamilies base families),
      ∃ p : OperationsAcross sorts familyMap (operationsOf old.restructuringLaw.vocabulary) ops,
        let compiler := vocabularyCompiler old ops sorts familyMap p
        formVocabulary material = some compiler.restructuringLaw.vocabulary ∧
        compiler.ledgerCompiler = old.ledgerCompiler ∧
        (∀ {current : V.Current} (event : source.toRootSource.actual.OccurrenceAt current),
          (nativeCertificationEquiv old.restructuringLaw ops sorts familyMap p (old.ledgerCompiler.compile event)).symm
            (compiler.certifyRestructuring event) = old.certifyRestructuring event) := by
  obtain ⟨material, base, families, ops, sorts, familyMap, p, formed⟩ :=
    every_original_vocabulary old.restructuringLaw.vocabulary sortCode familyCode
  exact ⟨material, base, families, ops, sorts, familyMap, p, formed, rfl,
    fun {_} event => certificate_recovers old ops sorts familyMap p event⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
