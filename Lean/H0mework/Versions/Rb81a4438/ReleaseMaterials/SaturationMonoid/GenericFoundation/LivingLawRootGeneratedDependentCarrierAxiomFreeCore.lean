import Mathlib.LinearAlgebra.Dual.Defs
import H0mework.Foundation.Source.AccountedUnfolding

/-!
# Axiom-free dependent carrier interface

The fixed-carrier four-face interface is sufficient for one instantiated
source, but a complete source may expose a carrier and its dual target that
depend on the exact source payload.  This file lifts the same occurrence
grammar to dependent families.  Sigma-labelled face occurrences retain the
source index, so a dependent face cannot erase its origin or become a second
root.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace DependentCarrier

universe s a c t l r h v d f

structure Input
    (Source : Type s)
    (Algebra : Source → Type a)
    (Combinatorial : Source → Type c)
    (Topological : Source → Type t)
    (Logical : Source → Type l)
    (Relation : Source → Type r)
    (Cochain : Source → Type h)
    (Carrier : Source → Type v)
    (DualTarget : Source → Type d)
    (ActualTarget : Source → Type f)
    [∀ source, AddCommGroup (Carrier source)]
    [∀ source, AddCommGroup (DualTarget source)]
    [∀ source, AddCommGroup (ActualTarget source)] where
  occurrence : RootedAccountedUnfolding Source
  algebraAt : ∀ source, Algebra source
  combinatorialAt : ∀ source, Combinatorial source
  topologicalAt : ∀ source, Topological source
  logicalAt : ∀ source, Logical source
  relationAt : ∀ source, Relation source
  cochainAt : ∀ source, Cochain source
  dualEvaluationAt : ∀ source,
    Carrier source →ₗ[ℤ] Module.Dual ℤ (DualTarget source)
  faithfulAt : ∀ source, Carrier source →ₗ[ℤ] ActualTarget source

namespace Input

variable {Source : Type s}
variable {Algebra : Source → Type a} {Combinatorial : Source → Type c}
variable {Topological : Source → Type t} {Logical : Source → Type l}
variable {Relation : Source → Type r} {Cochain : Source → Type h}
variable {Carrier : Source → Type v} {DualTarget : Source → Type d}
variable {ActualTarget : Source → Type f}
variable [∀ source, AddCommGroup (Carrier source)]
variable [∀ source, AddCommGroup (DualTarget source)]
variable [∀ source, AddCommGroup (ActualTarget source)]

abbrev FaceAlgebra (_input : Input Source Algebra Combinatorial Topological
    Logical Relation Cochain Carrier DualTarget ActualTarget) :=
  Σ source, Algebra source

abbrev FaceCombinatorial (_input : Input Source Algebra Combinatorial Topological
    Logical Relation Cochain Carrier DualTarget ActualTarget) :=
  Σ source, Combinatorial source

abbrev FaceTopological (_input : Input Source Algebra Combinatorial Topological
    Logical Relation Cochain Carrier DualTarget ActualTarget) :=
  Σ source, Topological source

abbrev FaceLogical (_input : Input Source Algebra Combinatorial Topological
    Logical Relation Cochain Carrier DualTarget ActualTarget) :=
  Σ source, Logical source

abbrev FaceRelation (_input : Input Source Algebra Combinatorial Topological
    Logical Relation Cochain Carrier DualTarget ActualTarget) :=
  Σ source, Relation source

abbrev FaceCochain (_input : Input Source Algebra Combinatorial Topological
    Logical Relation Cochain Carrier DualTarget ActualTarget) :=
  Σ source, Cochain source

abbrev FaceEvaluation (_input : Input Source Algebra Combinatorial Topological
    Logical Relation Cochain Carrier DualTarget ActualTarget) :=
  Σ source, Carrier source →ₗ[ℤ] Module.Dual ℤ (DualTarget source)

abbrev FaceFaithful (_input : Input Source Algebra Combinatorial Topological
    Logical Relation Cochain Carrier DualTarget ActualTarget) :=
  Σ source, Carrier source →ₗ[ℤ] ActualTarget source

abbrev AlgebraOccurrence
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    RootedAccountedUnfolding (FaceAlgebra input) :=
  input.occurrence.map (fun source => ⟨source, input.algebraAt source⟩)

abbrev CombinatorialOccurrence
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    RootedAccountedUnfolding (FaceCombinatorial input) :=
  input.occurrence.map (fun source => ⟨source, input.combinatorialAt source⟩)

abbrev TopologicalOccurrence
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    RootedAccountedUnfolding (FaceTopological input) :=
  input.occurrence.map (fun source => ⟨source, input.topologicalAt source⟩)

abbrev LogicalOccurrence
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    RootedAccountedUnfolding (FaceLogical input) :=
  input.occurrence.map (fun source => ⟨source, input.logicalAt source⟩)

abbrev RelationOccurrence
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    RootedAccountedUnfolding (FaceRelation input) :=
  input.occurrence.map (fun source => ⟨source, input.relationAt source⟩)

abbrev CochainOccurrence
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    RootedAccountedUnfolding (FaceCochain input) :=
  input.occurrence.map (fun source => ⟨source, input.cochainAt source⟩)

abbrev EvaluationOccurrence
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    RootedAccountedUnfolding (FaceEvaluation input) :=
  input.occurrence.map (fun source =>
    ⟨source, input.dualEvaluationAt source⟩)

abbrev FaithfulOccurrence
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    RootedAccountedUnfolding (FaceFaithful input) :=
  input.occurrence.map (fun source => ⟨source, input.faithfulAt source⟩)

theorem algebra_root
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    input.AlgebraOccurrence.root =
      ⟨input.occurrence.root, input.algebraAt input.occurrence.root⟩ :=
  RootedAccountedUnfolding.root_map _ _

theorem combinatorial_root
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    input.CombinatorialOccurrence.root =
      ⟨input.occurrence.root,
        input.combinatorialAt input.occurrence.root⟩ :=
  RootedAccountedUnfolding.root_map _ _

theorem topological_root
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    input.TopologicalOccurrence.root =
      ⟨input.occurrence.root,
        input.topologicalAt input.occurrence.root⟩ :=
  RootedAccountedUnfolding.root_map _ _

theorem logical_root
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    input.LogicalOccurrence.root =
      ⟨input.occurrence.root, input.logicalAt input.occurrence.root⟩ :=
  RootedAccountedUnfolding.root_map _ _

theorem relation_root
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    input.RelationOccurrence.root =
      ⟨input.occurrence.root, input.relationAt input.occurrence.root⟩ :=
  RootedAccountedUnfolding.root_map _ _

theorem cochain_root
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    input.CochainOccurrence.root =
      ⟨input.occurrence.root, input.cochainAt input.occurrence.root⟩ :=
  RootedAccountedUnfolding.root_map _ _

theorem evaluation_root
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    input.EvaluationOccurrence.root =
      ⟨input.occurrence.root,
        input.dualEvaluationAt input.occurrence.root⟩ :=
  RootedAccountedUnfolding.root_map _ _

theorem faithful_root
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    input.FaithfulOccurrence.root =
      ⟨input.occurrence.root,
        input.faithfulAt input.occurrence.root⟩ :=
  RootedAccountedUnfolding.root_map _ _

end Input

end DependentCarrier
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
