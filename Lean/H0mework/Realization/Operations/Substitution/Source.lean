import H0mework.Realization.Operations.ScalarPresentation

/-! Substitution acts on the retained derivation trees and scalar relation constructors. -/

set_option autoImplicit false

universe r u v w

namespace SaturationMonoid.SourceOperationScalarPresentation.SourceSubstitution

open SourceOperationEffects SourceOperationDerivations SourceOperationScalarRelations
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {Sorts : Type u} {Value : Sorts → Type v} {Var : Sorts → Type w}
  [∀ sort, AddCommGroup (Value sort)] {s : Sorts}
variable (binding : ∀ sort, Var sort → Expr Value Var sort) (environment : Env Value Var)

def sourceEnvironment : Env Value Var := fun sort name => (binding sort name).eval environment

variable {R : Type r} [CommRing R] [∀ sort, Module R (Value sort)]

/-- The proof tree is substituted; scalar source relations retain their original constructor. -/
def index : RelationIndex R (sourceEnvironment binding environment) s → RelationIndex R environment s
  | .inl proof => .inl ⟨proof.1.subst binding, proof.2.1.subst binding,
      Derivation.subst binding environment proof.2.2⟩
  | .inr scalar => .inr scalar

def relationWords :
    (RelationIndex R (sourceEnvironment binding environment) s →₀ R) →ₗ[R]
      (RelationIndex R environment s →₀ R) :=
  Finsupp.lmapDomain R R (index binding environment)

omit [∀ sort, Module R (Value sort)] in
private theorem constants_fixed :
    (substitution (R := R) (s := s) binding).comp (constantMap (R := R)) = constantMap (R := R) := by
  apply Finsupp.lhom_ext
  intro value coefficient
  simp only [LinearMap.comp_apply, substitution, constantMap, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, Expr.subst]

theorem index_boundary (generator : RelationIndex R (sourceEnvironment binding environment) s) :
    relation (R := R) environment (index binding environment generator) =
      substitution (R := R) binding (relation (R := R) (sourceEnvironment binding environment) generator) := by
  cases generator with
  | inl proof =>
      simp only [index, relation, map_sub, substitution, Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_single]
  | inr scalar =>
      exact (LinearMap.congr_fun (constants_fixed (R := R) (s := s) binding)
        (ScalarRelationPresentation.relation (R := R) (Value s) scalar)).symm

theorem boundary_square :
    (relationMap (R := R) (s := s) environment).comp (relationWords binding environment) =
      (substitution (R := R) binding).comp
        (relationMap (R := R) (s := s) (sourceEnvironment binding environment)) := by
  apply Finsupp.lhom_ext
  intro generator coefficient
  simp only [LinearMap.comp_apply, relationWords, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, relationMap, Finsupp.linearCombination_single, map_smul]
  exact congrArg (fun value => coefficient • value) (index_boundary binding environment generator)

end
end SaturationMonoid.SourceOperationScalarPresentation.SourceSubstitution
