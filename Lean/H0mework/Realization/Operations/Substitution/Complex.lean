import H0mework.Realization.Operations.Substitution.Source
import H0mework.Realization.Operations.ScalarExact

/-! The generated witness action is a morphism of the existing exact presentation complex. -/

set_option autoImplicit false

universe r u

namespace SaturationMonoid.SourceOperationScalarPresentation.SourceSubstitution

open CategoryTheory SourceOperationEffects SourceOperationScalarRelations

noncomputable section

variable {R : Type r} [CommRing R] {Sorts : Type u}
variable {Value Var : Sorts → Type (max r u)}
  [∀ sort, AddCommGroup (Value sort)] [∀ sort, Module R (Value sort)] {s : Sorts}

def complexMorphism (binding : ∀ sort, Var sort → Expr Value Var sort) (environment : Env Value Var) :
    presentationComplex (R := R) (s := s) (sourceEnvironment binding environment) ⟶
      presentationComplex (R := R) (s := s) environment where
  τ₁ := ModuleCat.ofHom (relationWords binding environment)
  τ₂ := ModuleCat.ofHom (substitution (R := R) binding)
  τ₃ := 𝟙 _
  comm₁₂ := by
    apply ModuleCat.hom_ext
    exact boundary_square binding environment
  comm₂₃ := by
    apply ModuleCat.hom_ext
    exact evaluation_substitution (R := R) binding environment

end
end SaturationMonoid.SourceOperationScalarPresentation.SourceSubstitution
