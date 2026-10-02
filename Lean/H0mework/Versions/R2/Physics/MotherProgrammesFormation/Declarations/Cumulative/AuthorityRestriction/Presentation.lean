import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.AuthorityRestriction.Native

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityRestriction
open MotherInventoryAdmission MotherAdmissionAlignment MotherRestructuringOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- The actual generated declaration supplies all four inverse readouts at
their common source indices. The original types specify the restriction. -/
structure Presentation {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (old : SourceNativeAuthoritySource N V) (value : SourcePair)
    (data : PresentationData value) (surface : TheoryState value.1.1.1.1.1) where
  network : MotherNetworkOrigin.Presentation N value.1.1.1.1.1
  vocabulary : MotherVocabularyOrigin.Presentation V (RepresentedV value)
  actualVocabulary : MotherVocabularyOrigin.Presentation old.eventInventoryAdmission.ActualV value.2.1
  represented : MotherNativeSourceOrigin.Presentation network vocabulary
    old.restructuringSource.source (Represented value).source
  actual : MotherNativeSourceOrigin.Presentation network actualVocabulary
    old.eventInventoryAdmission.actualSource.source value.2.2.source
  actualCompiler : CompilerPresentation actual old.eventInventoryAdmission.actualSource.ledgerCompiler
    value.2.2.ledgerCompiler
  sortsOut : Sorts
  familiesOut : Families sortsOut
  operations : Operations sortsOut familiesOut
  sorts : ∀ index, sortsOf old.restructuringSource.compiler.restructuringLaw.vocabulary.base index ≃ sortsOut index
  families : FamilyMap sorts (familiesOf old.restructuringSource.compiler.restructuringLaw.vocabulary) familiesOut
  across : OperationsAcross sorts families (operationsOf old.restructuringSource.compiler.restructuringLaw.vocabulary) operations
  restructuring : MotherRestructuringRestriction.Presentation represented old.restructuringSource.compiler
    (Represented value).compiler operations sorts families across
  projection : MotherProjectionOrigin.Across represented old.projectionLaw value.1.1.1.2
  theory : MotherTheoryTransport.Presentation network old.lawSurface surface
  data_eq : data = AdmissionTransport.transportedData old.eventInventoryAdmission value
    network vocabulary actualVocabulary represented actual

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {old : SourceNativeAuthoritySource N V} {value : SourcePair}
    {data : PresentationData value} {surface : TheoryState value.1.1.1.1.1}
    (p : Presentation old value data surface)

def Presentation.restrict : SourceNativeAuthoritySource N V :=
  restrictSource old value data surface p.network p.vocabulary p.actualVocabulary p.represented
    p.actual p.actualCompiler p.operations p.sorts p.families p.across p.restructuring p.projection p.theory p.data_eq

theorem Presentation.restrict_eq : p.restrict = old :=
  restrictSource_eq old value data surface p.network p.vocabulary p.actualVocabulary p.represented
    p.actual p.actualCompiler p.operations p.sorts p.families p.across p.restructuring p.projection p.theory p.data_eq

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityRestriction
