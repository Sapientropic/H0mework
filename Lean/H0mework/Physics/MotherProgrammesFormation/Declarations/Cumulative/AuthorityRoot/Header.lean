import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AuthorityRoot.Consumer

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityRoot.Presentation
open MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeAuthoritativeRootClosure N V} {value : SourcePair}
    {data : PresentationData value} {surface : TheoryState value.1.1.1.1.1}
    (p : Presentation root value data surface)

/-- A terminal successor carries its vocabulary as a value. Recover that
whole declaration too, before transporting the recovered dependent root. -/
def restrictHeader : Σ vocabulary : ConstructiveRoot.Vocabulary.{0}, SourceNativeAuthoritativeRootClosure N vocabulary :=
  ⟨MotherAdmissionAlignment.restrictVocabulary p.vocabulary,
    Equiv.cast (congrArg (SourceNativeAuthoritativeRootClosure N)
      (MotherAdmissionAlignment.restrictVocabulary_eq p.vocabulary).symm) p.restrict⟩

private theorem actual_cast_heq {A B : Type 1} (same : A = B) (value : A) :
    HEq (Equiv.cast same value) value := by
  cases same
  rfl

theorem restrictHeader_eq : p.restrictHeader = ⟨V, root⟩ := by
  have same : p.restrictHeader = ⟨V, p.restrict⟩ :=
    Sigma.ext (MotherAdmissionAlignment.restrictVocabulary_eq p.vocabulary)
      (actual_cast_heq (congrArg (SourceNativeAuthoritativeRootClosure N)
        (MotherAdmissionAlignment.restrictVocabulary_eq p.vocabulary).symm) p.restrict)
  exact same.trans (congrArg (Sigma.mk V) p.restrict_eq)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityRoot.Presentation
