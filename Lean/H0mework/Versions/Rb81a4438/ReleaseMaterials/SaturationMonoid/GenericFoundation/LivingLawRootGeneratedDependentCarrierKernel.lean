import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.LivingLawRootGeneratedDependentCarrierAxiomFreeCore
import H0mework.Realization.Perfectification.SourceCoimage
import H0mework.Realization.Perfectification.AmbientExtension

/-!
# Source-generated dependent-carrier producer

This layer removes the last fixed-type restriction from the unified producer.
Each exact source payload may carry its own algebraic, combinatorial,
topological, logical, relation, cochain, carrier, dual-target, and actual
target type.  Sigma-labelled sibling occurrences retain the payload index.
At the selected root payload, the same coimage/perfectification constructor
generates the canonical map, universal factorization, dual embedding,
duality/perfection disposition, and faithful residual.  No finite or
projective evidence is accepted at the input boundary.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace DependentCarrier

open SourceGeneratedPerfectification
open SourceGeneratedPerfectAmbient

noncomputable section

universe s a c t l r h v d f q

variable {Source : Type s}
variable {Algebra : Source → Type a} {Combinatorial : Source → Type c}
variable {Topological : Source → Type t} {Logical : Source → Type l}
variable {Relation : Source → Type r} {Cochain : Source → Type h}
variable {Carrier : Source → Type v} {DualTarget : Source → Type d}
variable {ActualTarget : Source → Type f}
variable [∀ source, AddCommGroup (Carrier source)]
variable [∀ source, AddCommGroup (DualTarget source)]
variable [∀ source, AddCommGroup (ActualTarget source)]

abbrev RootCarrier
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) : Type v :=
  Carrier input.occurrence.root

abbrev RootDualTarget
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) : Type d :=
  DualTarget input.occurrence.root

abbrev RootActualTarget
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) : Type f :=
  ActualTarget input.occurrence.root

abbrev RootEvaluation
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    RootCarrier input →ₗ[ℤ] Module.Dual ℤ (RootDualTarget input) :=
  input.dualEvaluationAt input.occurrence.root

abbrev RootFaithful
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    RootCarrier input →ₗ[ℤ] RootActualTarget input :=
  input.faithfulAt input.occurrence.root

abbrev Perfectification
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) : Type v :=
  SourceGeneratedPerfectification.PerfectificationCarrier (RootEvaluation input)

def canonicalMap
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    RootCarrier input →ₗ[ℤ] Perfectification input :=
  SourceGeneratedPerfectification.canonicalMap (RootEvaluation input)

def dualEmbedding
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    Perfectification input →ₗ[ℤ] Module.Dual ℤ (RootDualTarget input) :=
  SourceGeneratedPerfectification.dualEmbedding (RootEvaluation input)

@[simp] theorem dualEmbedding_comp_canonicalMap
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    (dualEmbedding input).comp (canonicalMap input) = RootEvaluation input :=
  SourceGeneratedPerfectification.dualEmbedding_comp_canonicalMap
    (RootEvaluation input)

theorem dualEmbedding_injective
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    Function.Injective (dualEmbedding input) :=
  SourceGeneratedPerfectification.dualEmbedding_injective (RootEvaluation input)

theorem canonicalMap_universal
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget)
    {Q : Type q} [AddCommGroup Q]
    (map : RootCarrier input →ₗ[ℤ] Q)
    (kernel_compatibility : LinearMap.ker (RootEvaluation input) ≤ LinearMap.ker map) :
    ∃! factor : Perfectification input →ₗ[ℤ] Q,
      factor.comp (canonicalMap input) = map :=
  SourceGeneratedPerfectification.canonicalMap_universal
    (RootEvaluation input) map kernel_compatibility

def perfectificationDisposition
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    SourceGeneratedPerfectification.PerfectificationDisposition
      (RootEvaluation input) :=
  SourceGeneratedPerfectification.settlePerfectification (RootEvaluation input)

def presentationDisposition
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    SourceGeneratedPerfectification.PerfectificationPresentationDisposition
      (RootEvaluation input) :=
  SourceGeneratedPerfectification.settlePerfectificationPresentation (RootEvaluation input)

def ambientDisposition
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    SourceGeneratedPerfectAmbient.PerfectAmbientExtensionDisposition
      (RootEvaluation input) :=
  SourceGeneratedPerfectAmbient.settlePerfectAmbientExtension (RootEvaluation input)

def faithfulDisposition
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    SourceGeneratedPerfectification.FaithfulFactorizationDisposition
      (RootEvaluation input) (RootFaithful input) :=
  SourceGeneratedPerfectification.settleFaithfulFactorization
    (RootEvaluation input) (RootFaithful input)

structure Generated
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    Type (max (max (max (max (max (max (max (max (max s a) c) t) l) r) h) v) d) f + 4) where
  algebraFace : RootedAccountedUnfolding (Input.FaceAlgebra input)
  combinatorialFace : RootedAccountedUnfolding (Input.FaceCombinatorial input)
  topologicalFace : RootedAccountedUnfolding (Input.FaceTopological input)
  logicalFace : RootedAccountedUnfolding (Input.FaceLogical input)
  relationFace : RootedAccountedUnfolding (Input.FaceRelation input)
  cochainFace : RootedAccountedUnfolding (Input.FaceCochain input)
  evaluationFace : RootedAccountedUnfolding (Input.FaceEvaluation input)
  faithfulFace : RootedAccountedUnfolding (Input.FaceFaithful input)
  canonical : RootCarrier input →ₗ[ℤ] Perfectification input
  embedding : Perfectification input →ₗ[ℤ] Module.Dual ℤ (RootDualTarget input)
  perfectification :
    SourceGeneratedPerfectification.PerfectificationDisposition
      (RootEvaluation input)
  presentation :
    SourceGeneratedPerfectification.PerfectificationPresentationDisposition
      (RootEvaluation input)
  ambient :
    SourceGeneratedPerfectAmbient.PerfectAmbientExtensionDisposition
      (RootEvaluation input)
  faithful :
    SourceGeneratedPerfectification.FaithfulFactorizationDisposition
      (RootEvaluation input) (RootFaithful input)

def generate
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) : Generated input where
  algebraFace := input.AlgebraOccurrence
  combinatorialFace := input.CombinatorialOccurrence
  topologicalFace := input.TopologicalOccurrence
  logicalFace := input.LogicalOccurrence
  relationFace := input.RelationOccurrence
  cochainFace := input.CochainOccurrence
  evaluationFace := input.EvaluationOccurrence
  faithfulFace := input.FaithfulOccurrence
  canonical := canonicalMap input
  embedding := dualEmbedding input
  perfectification := perfectificationDisposition input
  presentation := presentationDisposition input
  ambient := ambientDisposition input
  faithful := faithfulDisposition input

theorem generated_total
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) : Nonempty (Generated input) :=
  ⟨generate input⟩

@[simp] theorem generated_faces_are_projections
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    (generate input).algebraFace = input.AlgebraOccurrence ∧
      (generate input).combinatorialFace = input.CombinatorialOccurrence ∧
      (generate input).topologicalFace = input.TopologicalOccurrence ∧
      (generate input).logicalFace = input.LogicalOccurrence ∧
      (generate input).relationFace = input.RelationOccurrence ∧
      (generate input).cochainFace = input.CochainOccurrence :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem generated_dual_readback
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    (generate input).embedding.comp (generate input).canonical =
      RootEvaluation input :=
  dualEmbedding_comp_canonicalMap input

/-! ## Root-preserving dependent transport -/

structure RootMorphism
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget)
    (Source' : Type s)
    (Algebra' : Source' → Type a)
    (Combinatorial' : Source' → Type c)
    (Topological' : Source' → Type t)
    (Logical' : Source' → Type l)
    (Relation' : Source' → Type r)
    (Cochain' : Source' → Type h)
    (Carrier' : Source' → Type v)
    (DualTarget' : Source' → Type d)
    (ActualTarget' : Source' → Type f)
    [∀ source, AddCommGroup (Carrier' source)]
    [∀ source, AddCommGroup (DualTarget' source)]
    [∀ source, AddCommGroup (ActualTarget' source)]
    (input' : Input Source' Algebra' Combinatorial' Topological' Logical'
      Relation' Cochain' Carrier' DualTarget' ActualTarget') where
  sourceMap : Source → Source'
  root_map : input'.occurrence.root = sourceMap input.occurrence.root
  carrierMap : RootCarrier input →ₗ[ℤ] RootCarrier input'
  dualMap : RootDualTarget input' →ₗ[ℤ] RootDualTarget input
  actualMap : RootActualTarget input →ₗ[ℤ] RootActualTarget input'
  evaluation_naturality :
    (SourceGeneratedPerfectification.inducedDualTarget dualMap).comp
        (RootEvaluation input) =
      (RootEvaluation input').comp carrierMap
  faithful_naturality :
    actualMap.comp (RootFaithful input) =
      (RootFaithful input').comp carrierMap

namespace RootMorphism

def id
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    RootMorphism input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget input where
  sourceMap := fun value => value
  root_map := rfl
  carrierMap := LinearMap.id
  dualMap := LinearMap.id
  actualMap := LinearMap.id
  evaluation_naturality := by
    apply LinearMap.ext
    intro value
    rfl
  faithful_naturality := by
    apply LinearMap.ext
    intro value
    rfl

def comp
    {Source₁ : Type s} {Algebra₁ : Source₁ → Type a}
    {Combinatorial₁ : Source₁ → Type c} {Topological₁ : Source₁ → Type t}
    {Logical₁ : Source₁ → Type l} {Relation₁ : Source₁ → Type r}
    {Cochain₁ : Source₁ → Type h} {Carrier₁ : Source₁ → Type v}
    {DualTarget₁ : Source₁ → Type d} {ActualTarget₁ : Source₁ → Type f}
    [∀ source, AddCommGroup (Carrier₁ source)]
    [∀ source, AddCommGroup (DualTarget₁ source)]
    [∀ source, AddCommGroup (ActualTarget₁ source)]
    {Source₂ : Type s} {Algebra₂ : Source₂ → Type a}
    {Combinatorial₂ : Source₂ → Type c} {Topological₂ : Source₂ → Type t}
    {Logical₂ : Source₂ → Type l} {Relation₂ : Source₂ → Type r}
    {Cochain₂ : Source₂ → Type h} {Carrier₂ : Source₂ → Type v}
    {DualTarget₂ : Source₂ → Type d} {ActualTarget₂ : Source₂ → Type f}
    [∀ source, AddCommGroup (Carrier₂ source)]
    [∀ source, AddCommGroup (DualTarget₂ source)]
    [∀ source, AddCommGroup (ActualTarget₂ source)]
    {Source₃ : Type s} {Algebra₃ : Source₃ → Type a}
    {Combinatorial₃ : Source₃ → Type c} {Topological₃ : Source₃ → Type t}
    {Logical₃ : Source₃ → Type l} {Relation₃ : Source₃ → Type r}
    {Cochain₃ : Source₃ → Type h} {Carrier₃ : Source₃ → Type v}
    {DualTarget₃ : Source₃ → Type d} {ActualTarget₃ : Source₃ → Type f}
    [∀ source, AddCommGroup (Carrier₃ source)]
    [∀ source, AddCommGroup (DualTarget₃ source)]
    [∀ source, AddCommGroup (ActualTarget₃ source)]
    (input₁ : Input Source₁ Algebra₁ Combinatorial₁ Topological₁ Logical₁
      Relation₁ Cochain₁ Carrier₁ DualTarget₁ ActualTarget₁)
    (input₂ : Input Source₂ Algebra₂ Combinatorial₂ Topological₂ Logical₂
      Relation₂ Cochain₂ Carrier₂ DualTarget₂ ActualTarget₂)
    (input₃ : Input Source₃ Algebra₃ Combinatorial₃ Topological₃ Logical₃
      Relation₃ Cochain₃ Carrier₃ DualTarget₃ ActualTarget₃)
    (first : RootMorphism input₁ Source₂ Algebra₂ Combinatorial₂ Topological₂
      Logical₂ Relation₂ Cochain₂ Carrier₂ DualTarget₂ ActualTarget₂ input₂)
    (second : RootMorphism input₂ Source₃ Algebra₃ Combinatorial₃ Topological₃
      Logical₃ Relation₃ Cochain₃ Carrier₃ DualTarget₃ ActualTarget₃ input₃) :
    RootMorphism input₁ Source₃ Algebra₃ Combinatorial₃ Topological₃ Logical₃
      Relation₃ Cochain₃ Carrier₃ DualTarget₃ ActualTarget₃ input₃ where
  sourceMap := second.sourceMap ∘ first.sourceMap
  root_map := by
    calc
      input₃.occurrence.root = second.sourceMap input₂.occurrence.root :=
        second.root_map
      _ = second.sourceMap (first.sourceMap input₁.occurrence.root) := by
        rw [first.root_map]
  carrierMap := second.carrierMap.comp first.carrierMap
  dualMap := first.dualMap.comp second.dualMap
  actualMap := second.actualMap.comp first.actualMap
  evaluation_naturality := by
    apply LinearMap.ext
    intro value
    apply LinearMap.ext
    intro target
    change (RootEvaluation input₁ value)
        (first.dualMap (second.dualMap target)) =
      (RootEvaluation input₃
        (second.carrierMap (first.carrierMap value))) target
    have first_eval := congrArg (fun functional =>
        functional (second.dualMap target))
      (LinearMap.congr_fun first.evaluation_naturality value)
    have second_eval := congrArg (fun functional => functional target)
      (LinearMap.congr_fun second.evaluation_naturality
        (first.carrierMap value))
    exact first_eval.trans second_eval
  faithful_naturality := by
    apply LinearMap.ext
    intro value
    have first_eval := LinearMap.congr_fun first.faithful_naturality value
    have second_eval := LinearMap.congr_fun second.faithful_naturality
      (first.carrierMap value)
    exact (congrArg second.actualMap first_eval).trans second_eval

end RootMorphism

def inducedPerfectificationMap
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget)
    (Source' : Type s)
    (Algebra' : Source' → Type a)
    (Combinatorial' : Source' → Type c)
    (Topological' : Source' → Type t)
    (Logical' : Source' → Type l)
    (Relation' : Source' → Type r)
    (Cochain' : Source' → Type h)
    (Carrier' : Source' → Type v)
    (DualTarget' : Source' → Type d)
    (ActualTarget' : Source' → Type f)
    [∀ source, AddCommGroup (Carrier' source)]
    [∀ source, AddCommGroup (DualTarget' source)]
    [∀ source, AddCommGroup (ActualTarget' source)]
    (input' : Input Source' Algebra' Combinatorial' Topological' Logical'
      Relation' Cochain' Carrier' DualTarget' ActualTarget')
    (morphism : RootMorphism input Source' Algebra' Combinatorial'
      Topological' Logical' Relation' Cochain' Carrier' DualTarget' ActualTarget'
      input') :
    Perfectification input →ₗ[ℤ] Perfectification input' :=
  SourceGeneratedPerfectification.inducedPerfectificationMap
    (RootEvaluation input) (RootEvaluation input') morphism.carrierMap
    morphism.dualMap morphism.evaluation_naturality

theorem inducedPerfectificationMap_id
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget) :
    inducedPerfectificationMap input Source Algebra Combinatorial Topological
      Logical Relation Cochain Carrier DualTarget ActualTarget input
      (RootMorphism.id input) = LinearMap.id := by
  apply LinearMap.ext
  intro quotient
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective (LinearMap.ker (RootEvaluation input)) quotient
  rfl

theorem inducedPerfectificationMap_comp
    {Source₁ : Type s} {Algebra₁ : Source₁ → Type a}
    {Combinatorial₁ : Source₁ → Type c} {Topological₁ : Source₁ → Type t}
    {Logical₁ : Source₁ → Type l} {Relation₁ : Source₁ → Type r}
    {Cochain₁ : Source₁ → Type h} {Carrier₁ : Source₁ → Type v}
    {DualTarget₁ : Source₁ → Type d} {ActualTarget₁ : Source₁ → Type f}
    [∀ source, AddCommGroup (Carrier₁ source)]
    [∀ source, AddCommGroup (DualTarget₁ source)]
    [∀ source, AddCommGroup (ActualTarget₁ source)]
    {Source₂ : Type s} {Algebra₂ : Source₂ → Type a}
    {Combinatorial₂ : Source₂ → Type c} {Topological₂ : Source₂ → Type t}
    {Logical₂ : Source₂ → Type l} {Relation₂ : Source₂ → Type r}
    {Cochain₂ : Source₂ → Type h} {Carrier₂ : Source₂ → Type v}
    {DualTarget₂ : Source₂ → Type d} {ActualTarget₂ : Source₂ → Type f}
    [∀ source, AddCommGroup (Carrier₂ source)]
    [∀ source, AddCommGroup (DualTarget₂ source)]
    [∀ source, AddCommGroup (ActualTarget₂ source)]
    {Source₃ : Type s} {Algebra₃ : Source₃ → Type a}
    {Combinatorial₃ : Source₃ → Type c} {Topological₃ : Source₃ → Type t}
    {Logical₃ : Source₃ → Type l} {Relation₃ : Source₃ → Type r}
    {Cochain₃ : Source₃ → Type h} {Carrier₃ : Source₃ → Type v}
    {DualTarget₃ : Source₃ → Type d} {ActualTarget₃ : Source₃ → Type f}
    [∀ source, AddCommGroup (Carrier₃ source)]
    [∀ source, AddCommGroup (DualTarget₃ source)]
    [∀ source, AddCommGroup (ActualTarget₃ source)]
    (input₁ : Input Source₁ Algebra₁ Combinatorial₁ Topological₁ Logical₁
      Relation₁ Cochain₁ Carrier₁ DualTarget₁ ActualTarget₁)
    (input₂ : Input Source₂ Algebra₂ Combinatorial₂ Topological₂ Logical₂
      Relation₂ Cochain₂ Carrier₂ DualTarget₂ ActualTarget₂)
    (input₃ : Input Source₃ Algebra₃ Combinatorial₃ Topological₃ Logical₃
      Relation₃ Cochain₃ Carrier₃ DualTarget₃ ActualTarget₃)
    (first : RootMorphism input₁ Source₂ Algebra₂ Combinatorial₂ Topological₂
      Logical₂ Relation₂ Cochain₂ Carrier₂ DualTarget₂ ActualTarget₂ input₂)
    (second : RootMorphism input₂ Source₃ Algebra₃ Combinatorial₃ Topological₃
      Logical₃ Relation₃ Cochain₃ Carrier₃ DualTarget₃ ActualTarget₃ input₃) :
    inducedPerfectificationMap input₁ Source₃ Algebra₃ Combinatorial₃ Topological₃
      Logical₃ Relation₃ Cochain₃ Carrier₃ DualTarget₃ ActualTarget₃ input₃
      (RootMorphism.comp input₁ input₂ input₃ first second) =
      (inducedPerfectificationMap input₂ Source₃ Algebra₃ Combinatorial₃
        Topological₃ Logical₃ Relation₃ Cochain₃ Carrier₃ DualTarget₃ ActualTarget₃
        input₃ second).comp
        (inducedPerfectificationMap input₁ Source₂ Algebra₂ Combinatorial₂
          Topological₂ Logical₂ Relation₂ Cochain₂ Carrier₂ DualTarget₂ ActualTarget₂
          input₂ first) := by
  apply LinearMap.ext
  intro quotient
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective (LinearMap.ker (RootEvaluation input₁)) quotient
  rfl

theorem dualEmbedding_naturality
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget)
    (Source' : Type s)
    (Algebra' : Source' → Type a)
    (Combinatorial' : Source' → Type c)
    (Topological' : Source' → Type t)
    (Logical' : Source' → Type l)
    (Relation' : Source' → Type r)
    (Cochain' : Source' → Type h)
    (Carrier' : Source' → Type v)
    (DualTarget' : Source' → Type d)
    (ActualTarget' : Source' → Type f)
    [∀ source, AddCommGroup (Carrier' source)]
    [∀ source, AddCommGroup (DualTarget' source)]
    [∀ source, AddCommGroup (ActualTarget' source)]
    (input' : Input Source' Algebra' Combinatorial' Topological' Logical'
      Relation' Cochain' Carrier' DualTarget' ActualTarget')
    (morphism : RootMorphism input Source' Algebra' Combinatorial'
      Topological' Logical' Relation' Cochain' Carrier' DualTarget' ActualTarget'
      input') :
    (dualEmbedding input').comp
        (inducedPerfectificationMap input Source' Algebra' Combinatorial'
          Topological' Logical' Relation' Cochain' Carrier' DualTarget'
          ActualTarget' input' morphism) =
      (SourceGeneratedPerfectification.inducedDualTarget morphism.dualMap).comp
        (dualEmbedding input) :=
  SourceGeneratedPerfectification.dualEmbedding_naturality
    (RootEvaluation input) (RootEvaluation input') morphism.carrierMap
    morphism.dualMap morphism.evaluation_naturality

end
end DependentCarrier
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
