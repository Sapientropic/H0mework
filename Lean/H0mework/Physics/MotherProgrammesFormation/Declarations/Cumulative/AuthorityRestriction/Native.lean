import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AuthorityRestriction.Assembly

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityRestriction
open MotherInventoryAdmission MotherAdmissionAlignment MotherAdmissionRestriction MotherProjectionOrigin MotherRestructuringOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (old : SourceNativeAuthoritySource N V)
    (value : SourcePair) (data : PresentationData value)
    (surface : TheoryState value.1.1.1.1.1)
    (n : MotherNetworkOrigin.Presentation N value.1.1.1.1.1)
    (v : MotherVocabularyOrigin.Presentation V (RepresentedV value))
    (w : MotherVocabularyOrigin.Presentation old.eventInventoryAdmission.ActualV value.2.1)
    (p : MotherNativeSourceOrigin.Presentation n v old.restructuringSource.source (Represented value).source)
    (a : MotherNativeSourceOrigin.Presentation n w old.eventInventoryAdmission.actualSource.source value.2.2.source)
    (actual : CompilerPresentation a old.eventInventoryAdmission.actualSource.ledgerCompiler value.2.2.ledgerCompiler)
    {sortsOut : Sorts} {familiesOut : Families sortsOut} (ops : Operations sortsOut familiesOut)
    (sorts : ∀ index, sortsOf old.restructuringSource.compiler.restructuringLaw.vocabulary.base index ≃ sortsOut index)
    (families : FamilyMap sorts (familiesOf old.restructuringSource.compiler.restructuringLaw.vocabulary) familiesOut)
    (across : OperationsAcross sorts families (operationsOf old.restructuringSource.compiler.restructuringLaw.vocabulary) ops)
    (source : MotherRestructuringRestriction.Presentation p old.restructuringSource.compiler
      (Represented value).compiler ops sorts families across)
    (projection : Across p old.projectionLaw value.1.1.1.2)
    (theory : MotherTheoryTransport.Presentation n old.lawSurface surface)
    (dataSame : data = AdmissionTransport.transportedData old.eventInventoryAdmission value n v w p a)

/-- The four original authority fields are all actual inverse readouts:
whole restructuring source, full admission, full theory, and full projection. -/
def restrictSource : SourceNativeAuthoritySource N V :=
  assemble old source.restrictSource source.restrictSource_eq
    (restrictAdmission old.restructuringSource
      ⟨old.eventInventoryAdmission.ActualV, old.eventInventoryAdmission.actualSource⟩ value n v w p a actual
      (originalDataInImage old.eventInventoryAdmission value n v w p a data dataSame))
    theory.restrictTheory (MotherProjectionRestriction.restrictProjection projection)

theorem restrictSource_eq :
    restrictSource old value data surface n v w p a actual ops sorts families across source projection theory dataSame = old :=
  assemble_eq old source.restrictSource source.restrictSource_eq
    _ (original_admission_restricted old.eventInventoryAdmission value n v w p a actual data dataSame)
    _ theory.restrictTheory_eq _ (MotherProjectionRestriction.restrictProjection_eq projection)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityRestriction
