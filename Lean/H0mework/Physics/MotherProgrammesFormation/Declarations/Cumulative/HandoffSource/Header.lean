import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffSource.Consumer

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffSource
open MotherHandoffRestriction
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (old : SourceNativeLivingRootClosure N V) {events : EventFamily old.source.base}
    (declaration : Declaration old.source.base events) (value : JointValue rank)
    (presentation : JointPresentation old.toAuthoritativeRoot events declaration value)
    (payload : MotherHandoffPayload.Values (fun point => (declaration.continuation point).next))
    (same : payload = MotherHandoffPayload.valuesOf declaration)

/-- The original vocabulary is also an actual inverse readout; it is not
inserted as a value into a heterogeneous current declaration. -/
def restrictHeader : Σ vocabulary : ConstructiveRoot.Vocabulary.{0}, SourceNativeLivingRootClosure N vocabulary :=
  ⟨MotherAdmissionAlignment.restrictVocabulary presentation.authority.vocabulary,
    Equiv.cast (congrArg (SourceNativeLivingRootClosure N)
      (MotherAdmissionAlignment.restrictVocabulary_eq presentation.authority.vocabulary).symm)
      (restrictLiving old declaration value presentation payload same)⟩

private theorem actual_cast_heq {A B : Type 2} (same : A = B) (value : A) :
    HEq (Equiv.cast same value) value := by cases same; rfl

theorem restrictHeader_eq (lawSame : assembleLaw declaration = old.source.terminalHandoff) :
    restrictHeader old declaration value presentation payload same = ⟨V, old⟩ := by
  have headerSame : restrictHeader old declaration value presentation payload same =
      ⟨V, restrictLiving old declaration value presentation payload same⟩ :=
    Sigma.ext (MotherAdmissionAlignment.restrictVocabulary_eq presentation.authority.vocabulary)
      (actual_cast_heq (congrArg (SourceNativeLivingRootClosure N)
        (MotherAdmissionAlignment.restrictVocabulary_eq presentation.authority.vocabulary).symm) _)
  exact headerSame.trans (congrArg (Sigma.mk V)
    (restrictLiving_eq old declaration value presentation payload same lawSame))

theorem restrictHeader_of_root_eq
    (rootSame : restrictLiving old declaration value presentation payload same = old) :
    restrictHeader old declaration value presentation payload same = ⟨V, old⟩ := by
  have headerSame : restrictHeader old declaration value presentation payload same =
      ⟨V, restrictLiving old declaration value presentation payload same⟩ :=
    Sigma.ext (MotherAdmissionAlignment.restrictVocabulary_eq presentation.authority.vocabulary)
      (actual_cast_heq (congrArg (SourceNativeLivingRootClosure N)
        (MotherAdmissionAlignment.restrictVocabulary_eq presentation.authority.vocabulary).symm) _)
  exact headerSame.trans (congrArg (Sigma.mk V) rootSame)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffSource
