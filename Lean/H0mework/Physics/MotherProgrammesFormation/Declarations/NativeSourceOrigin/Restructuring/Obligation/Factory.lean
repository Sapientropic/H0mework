import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Obligation.Encoding

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin
open MotherNetworkFactory MotherRestructuringOrigin MotherFullCompiler MotherSourcePrograms
open MotherLedgerRoot MotherProjectionOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} {R : RestructuringVocabulary.{0}}

def formFixedLaw (coordinates : Coordinates source) (world : WorldCoordinates N)
    (vocabulary : VocabularyCoordinates R) (material : M) : Option (SourceNativeLedgerRestructuringLaw source) :=
  if checked : FieldCheck coordinates world vocabulary material then
    let fields := generatedFields coordinates world vocabulary material checked
    if laws : FieldLaws fields then some (lawOf fields laws) else none
  else none

abbrev LawValue := Σ value : ProjectionValue, SourceNativeLedgerRestructuringLaw value.1.2.2.source.source

def formLawParts (parent vocabularyMaterial material : M) : Option LawValue :=
  (formProjection parent).pbind (fun value parentFormed =>
    (formVocabulary vocabularyMaterial).pbind (fun R vocabularyFormed =>
      let rootFormed := projection_root_formed parent value parentFormed
      let coordinates := rootCoordinates (MotherHigherLawValue.split parent).1 value.1 rootFormed
      let world := rootWorldCoordinates (MotherHigherLawValue.split parent).1 value.1 rootFormed
      let vocabulary := vocabularyCoordinates vocabularyMaterial R vocabularyFormed
      (formFixedLaw coordinates world vocabulary material).map (fun law => ⟨value, law⟩)))

/-- The native world, complete compiler/root, projection and restructuring
vocabulary are actual outputs of the same material before their registration
maps are formed. Original objects enter only the coverage theorem. -/
def formLaw (material : M) : Option LawValue :=
  let first := MotherHigherLawValue.split material
  let second := MotherHigherLawValue.split first.2
  formLawParts first.1 second.1 second.2

theorem fixedLaw_recovered (law : SourceNativeLedgerRestructuringLaw source)
    (coordinates : Coordinates source) (world : WorldCoordinates N) (vocabulary : VocabularyCoordinates law.vocabulary)
    (material : M) (hm : MotherHigherLawFormation.read material = FieldEncoding.reader coordinates world vocabulary (fieldsOf law)) :
    formFixedLaw coordinates world vocabulary material = some law := by
  have checked := FieldEncoding.checked coordinates world vocabulary (fieldsOf law) hm
  have recovered := FieldEncoding.recovered coordinates world vocabulary (fieldsOf law) hm checked
  have laws : FieldLaws (generatedFields coordinates world vocabulary material checked) := by
    rw [recovered]
    exact fieldsOf_laws law
  simp only [formFixedLaw, dif_pos checked, dif_pos laws]
  congr 1
  have same : lawOf (generatedFields coordinates world vocabulary material checked) laws =
      lawOf (fieldsOf law) (fieldsOf_laws law) := by congr 1
  exact same.trans (lawOf_original law)

theorem every_law_on_formed_parent (parent vocabularyMaterial : M) (value : ProjectionValue)
    (parentFormed : formProjection parent = some value)
    (law : SourceNativeLedgerRestructuringLaw value.1.2.2.source.source)
    (vocabularyFormed : formVocabulary vocabularyMaterial = some law.vocabulary) :
    ∃ material : M, formLaw material = some ⟨value, law⟩ := by
  let rootFormed := projection_root_formed parent value parentFormed
  let coordinates := rootCoordinates (MotherHigherLawValue.split parent).1 value.1 rootFormed
  let world := rootWorldCoordinates (MotherHigherLawValue.split parent).1 value.1 rootFormed
  let vocabulary := vocabularyCoordinates vocabularyMaterial law.vocabulary vocabularyFormed
  obtain ⟨material, hm⟩ := MotherHigherLawFormation.read_surjective
    (FieldEncoding.reader coordinates world vocabulary (fieldsOf law))
  refine ⟨MotherHigherLawValue.pack (parent, MotherHigherLawValue.pack (vocabularyMaterial, material)), ?_⟩
  simp only [formLaw, MotherHigherLawValue.split_pack, formLawParts, parentFormed, Option.pbind_some, vocabularyFormed]
  change (formFixedLaw coordinates world vocabulary material).map (fun result => (⟨value, result⟩ : LawValue)) = some ⟨value, law⟩
  rw [fixedLaw_recovered law coordinates world vocabulary material hm]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin
