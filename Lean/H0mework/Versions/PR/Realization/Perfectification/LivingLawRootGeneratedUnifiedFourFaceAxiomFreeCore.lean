import Mathlib.LinearAlgebra.Dual.Defs
import H0mework.Realization.Perfectification.LivingLawRootGeneratedUnifiedFourFaceEvaluationCore
import H0mework.Foundation.Source.AccountedUnfolding

/-!
# Axiom-free unified four-face occurrence core

Algebra, combinatorics, topology, and logic are sibling views of one exact
source occurrence.  This file contains only the occurrence-preserving
projection grammar and the small laws needed by their consumers.  It does not
choose a branch, a limit, a proof, a determinant, or a perfect ambient.

Every face is obtained by `RootedAccountedUnfolding.map` from the same source
tree.  Consequently `root_map`, `map_map`, `map_id`, and `fold_unique` are the
only provenance mechanisms used here; a face cannot become a second source by
being assigned a new name.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace UnifiedFourFace

universe s a c t l r h v d o z

/-! ## One source occurrence and its sibling projections -/

structure Input
    (Source : Type s)
    (Algebra : Type a)
    (Combinatorial : Type c)
    (Topological : Type t)
    (Logical : Type l)
    (Relation : Type r)
    (Cochain : Type h)
    (Carrier : Type v)
    (DualTarget : Type d)
    [AddCommGroup Carrier] [AddCommGroup DualTarget] where
  occurrence : RootedAccountedUnfolding Source
  algebraAt : Source → Algebra
  combinatorialAt : Source → Combinatorial
  topologicalAt : Source → Topological
  logicalAt : Source → Logical
  relationAt : Source → Relation
  cochainAt : Source → Cochain
  dualEvaluationAt : Source → Carrier →ₗ[ℤ] Module.Dual ℤ DualTarget
  faithfulAt : Source → Carrier →ₗ[ℤ] Carrier

namespace Input

variable {Source : Type s} {Algebra : Type a} {Combinatorial : Type c}
variable {Topological : Type t} {Logical : Type l} {Relation : Type r}
variable {Cochain : Type h} {Carrier : Type v} {DualTarget : Type d}
variable [AddCommGroup Carrier] [AddCommGroup DualTarget]

def toEvaluationInput
    (input : UnifiedFourFace.Input Source Algebra Combinatorial Topological Logical Relation Cochain Carrier DualTarget) :
    Evaluation.Input Source Algebra Combinatorial Topological Logical Relation Cochain Carrier (Module.Dual ℤ DualTarget) where
  occurrence := input.occurrence
  algebraAt := input.algebraAt
  combinatorialAt := input.combinatorialAt
  topologicalAt := input.topologicalAt
  logicalAt := input.logicalAt
  relationAt := input.relationAt
  cochainAt := input.cochainAt
  evaluationAt := input.dualEvaluationAt
  faithfulAt := input.faithfulAt

abbrev AlgebraOccurrence
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) : RootedAccountedUnfolding Algebra :=
  input.occurrence.map input.algebraAt

abbrev CombinatorialOccurrence
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) : RootedAccountedUnfolding Combinatorial :=
  input.occurrence.map input.combinatorialAt

abbrev TopologicalOccurrence
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) : RootedAccountedUnfolding Topological :=
  input.occurrence.map input.topologicalAt

abbrev LogicalOccurrence
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) : RootedAccountedUnfolding Logical :=
  input.occurrence.map input.logicalAt

abbrev RelationOccurrence
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) : RootedAccountedUnfolding Relation :=
  input.occurrence.map input.relationAt

abbrev CochainOccurrence
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) : RootedAccountedUnfolding Cochain :=
  input.occurrence.map input.cochainAt

abbrev EvaluationOccurrence
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    RootedAccountedUnfolding (Carrier →ₗ[ℤ] Module.Dual ℤ DualTarget) :=
  input.occurrence.map input.dualEvaluationAt

abbrev FaithfulOccurrence
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    RootedAccountedUnfolding (Carrier →ₗ[ℤ] Carrier) :=
  input.occurrence.map input.faithfulAt

@[simp] theorem algebra_root
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    input.AlgebraOccurrence.root = input.algebraAt input.occurrence.root :=
  by
    exact RootedAccountedUnfolding.root_map input.algebraAt input.occurrence

@[simp] theorem combinatorial_root
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    input.CombinatorialOccurrence.root =
      input.combinatorialAt input.occurrence.root :=
  by
    exact RootedAccountedUnfolding.root_map input.combinatorialAt input.occurrence

@[simp] theorem topological_root
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    input.TopologicalOccurrence.root =
      input.topologicalAt input.occurrence.root :=
  by
    exact RootedAccountedUnfolding.root_map input.topologicalAt input.occurrence

@[simp] theorem logical_root
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    input.LogicalOccurrence.root = input.logicalAt input.occurrence.root :=
  by
    exact RootedAccountedUnfolding.root_map input.logicalAt input.occurrence

@[simp] theorem relation_root
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    input.RelationOccurrence.root = input.relationAt input.occurrence.root :=
  by
    exact RootedAccountedUnfolding.root_map input.relationAt input.occurrence

@[simp] theorem cochain_root
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    input.CochainOccurrence.root = input.cochainAt input.occurrence.root :=
  by
    exact RootedAccountedUnfolding.root_map input.cochainAt input.occurrence

@[simp] theorem evaluation_root
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    input.EvaluationOccurrence.root =
      input.dualEvaluationAt input.occurrence.root :=
  by
    exact RootedAccountedUnfolding.root_map input.dualEvaluationAt input.occurrence

@[simp] theorem faithful_root
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    input.FaithfulOccurrence.root = input.faithfulAt input.occurrence.root :=
  by
    exact RootedAccountedUnfolding.root_map input.faithfulAt input.occurrence

/-! ## Projection naturality -/

theorem map_after_projection
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget)
    (target : Type z) (transform : Algebra → target) :
    (input.AlgebraOccurrence.map transform) =
      input.occurrence.map (transform ∘ input.algebraAt) := by
  exact RootedAccountedUnfolding.map_map transform input.algebraAt
    input.occurrence

theorem projection_identity
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    input.occurrence.map id = input.occurrence :=
  RootedAccountedUnfolding.map_id input.occurrence

end Input

/-! ## Combinatorial fold contract -/

structure CombinatorialFoldLaw
    (Source : Type s)
    (Algebra : Type a)
    (Combinatorial : Type c)
    (Topological : Type t)
    (Logical : Type l)
    (Relation : Type r)
    (Cochain : Type h)
    (Carrier : Type v)
    (DualTarget : Type d)
    [AddCommGroup Carrier] [AddCommGroup DualTarget]
    (Result : Type o) where
  input : Input Source Algebra Combinatorial Topological Logical Relation
    Cochain Carrier DualTarget
  atOccurrence : Combinatorial → List Result → Result
  candidate : RootedAccountedUnfolding Combinatorial → Result
  commutes : ∀ (origin : Combinatorial)
    (branches : AccountedBranches Combinatorial),
    candidate (RootedAccountedUnfolding.occur origin branches) =
      atOccurrence origin
        (RootedAccountedUnfolding.candidateValues candidate branches)

namespace CombinatorialFoldLaw

variable {Source : Type s} {Algebra : Type a} {Combinatorial : Type c}
variable {Topological : Type t} {Logical : Type l} {Relation : Type r}
variable {Cochain : Type h} {Carrier : Type v} {DualTarget : Type d}
variable [AddCommGroup Carrier] [AddCommGroup DualTarget]

def generatedFold
    {Result : Type o}
    (law : CombinatorialFoldLaw Source Algebra Combinatorial Topological Logical
      Relation Cochain Carrier DualTarget Result) : Result :=
  law.candidate law.input.CombinatorialOccurrence

theorem candidate_eq_generatedFold
    {Result : Type o}
    (law : CombinatorialFoldLaw Source Algebra Combinatorial Topological Logical
      Relation Cochain Carrier DualTarget Result)
    (occurrence : RootedAccountedUnfolding Combinatorial) :
    law.candidate occurrence = occurrence.fold law.atOccurrence :=
  RootedAccountedUnfolding.fold_unique law.atOccurrence law.candidate
    law.commutes occurrence

end CombinatorialFoldLaw

/-! ## Topological refinement contract -/

structure TopologicalRefinementLaw
    (Source : Type s)
    (Algebra : Type a)
    (Combinatorial : Type c)
    (Topological : Type t)
    (Logical : Type l)
    (Relation : Type r)
    (Cochain : Type h)
    (Carrier : Type v)
    (DualTarget : Type d)
    [AddCommGroup Carrier] [AddCommGroup DualTarget]
    (Observation : Type z) where
  input : Input Source Algebra Combinatorial Topological Logical Relation
    Cochain Carrier DualTarget
  refineAt : Topological → Topological
  observationAt : Topological → Observation
  restrictionAt : Observation → Observation
  commutes : ∀ value,
    observationAt (refineAt value) = restrictionAt (observationAt value)

namespace TopologicalRefinementLaw

variable {Source : Type s} {Algebra : Type a} {Combinatorial : Type c}
variable {Topological : Type t} {Logical : Type l} {Relation : Type r}
variable {Cochain : Type h} {Carrier : Type v} {DualTarget : Type d}
variable [AddCommGroup Carrier] [AddCommGroup DualTarget]

def refinedOccurrence
    {Observation : Type z}
    (law : TopologicalRefinementLaw Source Algebra Combinatorial Topological
      Logical Relation Cochain Carrier DualTarget Observation) :
    RootedAccountedUnfolding Topological :=
  law.input.TopologicalOccurrence.map law.refineAt

@[simp] theorem refined_root
    {Observation : Type z}
    (law : TopologicalRefinementLaw Source Algebra Combinatorial Topological
      Logical Relation Cochain Carrier DualTarget Observation) :
    law.refinedOccurrence.root =
      law.refineAt (law.input.topologicalAt law.input.occurrence.root) :=
  by
    change
      (law.input.TopologicalOccurrence.map law.refineAt).root =
        law.refineAt (law.input.topologicalAt law.input.occurrence.root)
    rw [RootedAccountedUnfolding.root_map,
      RootedAccountedUnfolding.root_map]

theorem observation_refinement_commutes
    {Observation : Type z}
    (law : TopologicalRefinementLaw Source Algebra Combinatorial Topological
      Logical Relation Cochain Carrier DualTarget Observation)
    (value : Topological) :
    law.observationAt (law.refineAt value) =
      law.restrictionAt (law.observationAt value) :=
  law.commutes value

end TopologicalRefinementLaw

/-! ## Logical witness/counter-witness contract -/

structure LogicalDecisionLaw
    (Source : Type s)
    (Algebra : Type a)
    (Combinatorial : Type c)
    (Topological : Type t)
    (Logical : Type l)
    (Relation : Type r)
    (Cochain : Type h)
    (Carrier : Type v)
    (DualTarget : Type d)
    [AddCommGroup Carrier] [AddCommGroup DualTarget] where
  input : Input Source Algebra Combinatorial Topological Logical Relation
    Cochain Carrier DualTarget
  predicate : Logical → Prop
  decideAt : ∀ value, Decidable (predicate value)

namespace LogicalDecisionLaw

variable {Source : Type s} {Algebra : Type a} {Combinatorial : Type c}
variable {Topological : Type t} {Logical : Type l} {Relation : Type r}
variable {Cochain : Type h} {Carrier : Type v} {DualTarget : Type d}
variable [AddCommGroup Carrier] [AddCommGroup DualTarget]

theorem outcomeAt
    (law : LogicalDecisionLaw Source Algebra Combinatorial Topological Logical
      Relation Cochain Carrier DualTarget)
    (value : Logical) : law.predicate value ∨ ¬ law.predicate value :=
  match law.decideAt value with
  | isTrue proof => Or.inl proof
  | isFalse proof => Or.inr proof

theorem outcome_exhaustive
    (law : LogicalDecisionLaw Source Algebra Combinatorial Topological Logical
      Relation Cochain Carrier DualTarget)
    (value : Logical) :
    law.predicate value ∨ ¬ law.predicate value :=
  law.outcomeAt value

end LogicalDecisionLaw

end UnifiedFourFace
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
