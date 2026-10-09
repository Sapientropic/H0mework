import H0mework.Realization.Perfectification.LivingLawRootGeneratedUnifiedFourFaceEvaluationCore
import H0mework.Foundation.Relations.ScalarDifferentialResidual

/-! Shared evaluator grammar for sibling faces of one source occurrence.
The coimage and action reuse ScalarDifferentialResidual; evaluator targets
retain their generated modules, including complete separating characters. -/

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace UnifiedFourFace.Evaluation

universe s a c t l r h v e z s' a' c' t' l' r' h' v' e'

variable {Source : Type s} {Algebra : Type a} {Combinatorial : Type c}
variable {Topological : Type t} {Logical : Type l} {Relation : Type r}
variable {Cochain : Type h} {Carrier : Type v} {Target : Type e}
variable [AddCommGroup Carrier] [Module ℤ Carrier]
variable [AddCommGroup Target] [Module ℤ Target]

abbrev RootEvaluation
    (input : Input Source Algebra Combinatorial Topological Logical Relation Cochain Carrier Target) :=
  input.evaluationAt input.occurrence.root

abbrev Coimage
    (input : Input Source Algebra Combinatorial Topological Logical Relation Cochain Carrier Target) :=
  SourceGeneratedScalarDifferentialResidual.ResidualCarrier (RootEvaluation input)

local instance coimageModule
    (input : Input Source Algebra Combinatorial Topological Logical Relation Cochain Carrier Target) :
    Module ℤ (Coimage input) := Submodule.Quotient.module (LinearMap.ker (RootEvaluation input))

local instance rangeModule
    (input : Input Source Algebra Combinatorial Topological Logical Relation Cochain Carrier Target) :
    Module ℤ (LinearMap.range (RootEvaluation input)) := (LinearMap.range (RootEvaluation input)).module

def canonical
    (input : Input Source Algebra Combinatorial Topological Logical Relation Cochain Carrier Target) :=
  SourceGeneratedScalarDifferentialResidual.canonicalResidual (RootEvaluation input)

def embedding
    (input : Input Source Algebra Combinatorial Topological Logical Relation Cochain Carrier Target) :
    Coimage input →ₗ[ℤ] Target :=
  (LinearMap.ker (RootEvaluation input)).liftQ (RootEvaluation input) le_rfl

theorem embedding_canonical
    (input : Input Source Algebra Combinatorial Topological Logical Relation Cochain Carrier Target) :
    (embedding input).comp (canonical input) = RootEvaluation input := by
  apply LinearMap.ext
  intro value
  rfl

theorem embedding_injective
    (input : Input Source Algebra Combinatorial Topological Logical Relation Cochain Carrier Target) :
    Function.Injective (embedding input) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl

theorem canonical_universal
    (input : Input Source Algebra Combinatorial Topological Logical Relation Cochain Carrier Target)
    {Q : Type z} [AddCommGroup Q] [Module ℤ Q]
    (map : Carrier →ₗ[ℤ] Q)
    (compatible : LinearMap.ker (RootEvaluation input) ≤ LinearMap.ker map) :
    ∃! factor : Coimage input →ₗ[ℤ] Q,
      factor.comp (canonical input) = map :=
  SourceGeneratedScalarDifferentialResidual.universal_factorization (RootEvaluation input) map compatible

structure Generated
    (input : Input Source Algebra Combinatorial Topological Logical Relation Cochain Carrier Target) where
  algebraFace : RootedAccountedUnfolding Algebra
  combinatorialFace : RootedAccountedUnfolding Combinatorial
  topologicalFace : RootedAccountedUnfolding Topological
  logicalFace : RootedAccountedUnfolding Logical
  relationFace : RootedAccountedUnfolding Relation
  cochainFace : RootedAccountedUnfolding Cochain
  evaluationFace : RootedAccountedUnfolding (Carrier →ₗ[ℤ] Target)
  faithfulFace : RootedAccountedUnfolding (Carrier →ₗ[ℤ] Carrier)
  canonical : Carrier →ₗ[ℤ] Coimage input
  embedding : Coimage input →ₗ[ℤ] Target
  rangeEquiv : Coimage input ≃ₗ[ℤ] LinearMap.range (RootEvaluation input)

def generate
    (input : Input Source Algebra Combinatorial Topological Logical Relation Cochain Carrier Target) :
    Generated input where
  algebraFace := input.occurrence.map input.algebraAt
  combinatorialFace := input.occurrence.map input.combinatorialAt
  topologicalFace := input.occurrence.map input.topologicalAt
  logicalFace := input.occurrence.map input.logicalAt
  relationFace := input.occurrence.map input.relationAt
  cochainFace := input.occurrence.map input.cochainAt
  evaluationFace := input.occurrence.map input.evaluationAt
  faithfulFace := input.occurrence.map input.faithfulAt
  canonical := canonical input
  embedding := embedding input
  rangeEquiv := SourceGeneratedScalarDifferentialResidual.residualEquivRange (RootEvaluation input)

theorem generated_equation
    (input : Input Source Algebra Combinatorial Topological Logical Relation Cochain Carrier Target) :
    (generate input).embedding.comp (generate input).canonical = RootEvaluation input :=
  embedding_canonical input

variable {Source' : Type s'} {Algebra' : Type a'} {Combinatorial' : Type c'}
variable {Topological' : Type t'} {Logical' : Type l'} {Relation' : Type r'}
variable {Cochain' : Type h'} {Carrier' : Type v'} {Target' : Type e'}
variable [AddCommGroup Carrier'] [Module ℤ Carrier']
variable [AddCommGroup Target'] [Module ℤ Target']

local instance coimageModule'
    (input : Input Source' Algebra' Combinatorial' Topological' Logical' Relation' Cochain' Carrier' Target') :
    Module ℤ (Coimage input) := Submodule.Quotient.module (LinearMap.ker (RootEvaluation input))

def move
    {input : Input Source Algebra Combinatorial Topological Logical Relation Cochain Carrier Target}
    {input' : Input Source' Algebra' Combinatorial' Topological' Logical' Relation' Cochain' Carrier' Target'}
    (action : SourceGeneratedScalarDifferentialResidual.Morphism (RootEvaluation input) (RootEvaluation input')) :=
  SourceGeneratedScalarDifferentialResidual.inducedResidualMap action

theorem generated_action
    {input : Input Source Algebra Combinatorial Topological Logical Relation Cochain Carrier Target}
    {input' : Input Source' Algebra' Combinatorial' Topological' Logical' Relation' Cochain' Carrier' Target'}
    (action : SourceGeneratedScalarDifferentialResidual.Morphism (RootEvaluation input) (RootEvaluation input'))
    (word : Carrier) :
    move (input:=input) (input':=input') action ((generate input).canonical word) =
      (generate input').canonical (action.sourceMap word) :=
  LinearMap.congr_fun
    (SourceGeneratedScalarDifferentialResidual.inducedResidualMap_comp_canonical action) word

theorem generated_action_embedding
    {input : Input Source Algebra Combinatorial Topological Logical Relation Cochain Carrier Target}
    {input' : Input Source' Algebra' Combinatorial' Topological' Logical' Relation' Cochain' Carrier' Target'}
    (action : SourceGeneratedScalarDifferentialResidual.Morphism (RootEvaluation input) (RootEvaluation input'))
    (value : Coimage input) :
    (generate input').embedding (move (input:=input) (input':=input') action value) =
      action.targetMap ((generate input).embedding value) := by
  obtain ⟨word,rfl⟩ := Submodule.mkQ_surjective (LinearMap.ker (RootEvaluation input)) value
  exact (LinearMap.congr_fun action.commutes word).symm

end UnifiedFourFace.Evaluation

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
