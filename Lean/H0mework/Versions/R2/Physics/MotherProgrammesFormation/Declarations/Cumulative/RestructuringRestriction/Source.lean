import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.RestructuringRestriction.Compiler

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringRestriction.Presentation
open MotherFullCompiler MotherSourcePrograms MotherRestructuringOrigin MotherObligationOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    {p : MotherNativeSourceOrigin.Presentation n v original generated}
    {old : SourceNativeRestructuringLedgerCompiler original}
    {actual : SourceNativeRestructuringLedgerCompiler generated}
    {sortsOut : Sorts} {familiesOut : Families sortsOut} {ops : Operations sortsOut familiesOut}
    {sorts : ∀ index, sortsOf old.restructuringLaw.vocabulary.base index ≃ sortsOut index}
    {families : FamilyMap sorts (familiesOf old.restructuringLaw.vocabulary) familiesOut}
    {across : OperationsAcross sorts families (operationsOf old.restructuringLaw.vocabulary) ops}
    (presentation : Presentation p old actual ops sorts families across)

def restrictSource : SourceNativeRestructuringLedgerSource N V :=
  ⟨MotherAdmissionAlignment.restrictSource p,
    Equiv.cast (congrArg SourceNativeRestructuringLedgerCompiler (MotherAdmissionAlignment.restrictSource_eq p).symm)
      presentation.restrictCompiler⟩

private theorem source_eq {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {first last : SourceNativeSource N V} (same : first = last)
    (compiler : SourceNativeRestructuringLedgerCompiler last)
    (restored : SourceNativeRestructuringLedgerCompiler last) (restored_eq : restored = compiler) :
    (⟨first, Equiv.cast (congrArg SourceNativeRestructuringLedgerCompiler same.symm) restored⟩ :
      SourceNativeRestructuringLedgerSource N V) = ⟨last, compiler⟩ := by
  cases same
  cases restored_eq
  rfl

theorem restrictSource_eq : presentation.restrictSource = ⟨original, old⟩ :=
  source_eq (MotherAdmissionAlignment.restrictSource_eq p) old presentation.restrictCompiler presentation.restrictCompiler_eq

def restrictHeader : Σ vocab : ConstructiveRoot.Vocabulary.{0}, SourceNativeRestructuringLedgerSource N vocab :=
  ⟨MotherAdmissionAlignment.restrictVocabulary v,
    Equiv.cast (congrArg (SourceNativeRestructuringLedgerSource N) (MotherAdmissionAlignment.restrictVocabulary_eq v).symm)
      presentation.restrictSource⟩

private theorem actual_cast_heq {A B : Type 1} (same : A = B) (value : A) :
    HEq (Equiv.cast same value) value := by
  cases same
  rfl

theorem restrictHeader_eq : presentation.restrictHeader = ⟨V, ⟨original, old⟩⟩ := by
  have same : presentation.restrictHeader = ⟨V, presentation.restrictSource⟩ :=
    Sigma.ext (MotherAdmissionAlignment.restrictVocabulary_eq v)
      (actual_cast_heq (congrArg (SourceNativeRestructuringLedgerSource N)
        (MotherAdmissionAlignment.restrictVocabulary_eq v).symm) presentation.restrictSource)
  exact same.trans (congrArg (Sigma.mk V) presentation.restrictSource_eq)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringRestriction.Presentation
