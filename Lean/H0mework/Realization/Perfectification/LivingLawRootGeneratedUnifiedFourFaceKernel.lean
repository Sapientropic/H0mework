import H0mework.Realization.Perfectification.LivingLawRootGeneratedUnifiedFourFaceAxiomFreeCore
import H0mework.Realization.Perfectification.SourceCoimage
import H0mework.Realization.Perfectification.IntegralPair
import H0mework.Realization.Perfectification.AmbientExtension

/-!
# Source-generated unified four-face producer

This is the constructive producer for one exact source occurrence.  Algebra,
combinatorics, topology, logic, relation, cochain, carrier, dual evaluation,
and faithful transport are fields of one `Input`; none is a second root.  The
producer reads the carrier and evaluation at the root payload and builds the
canonical coimage `P := C / ker(e)`.  Its universal map, injective dual
embedding, duality/perfection disposition, finite-language disposition,
faithful factorization residual, and ambient extension are all generated
without a finite, projective, nondegenerate, determinant, or inverse premise.

The finite-free branch is a bounded observation of the generated source
ambient.  The other branches retain an exact representation/compression
coordinate.  Thus an infinite carrier is not declared imperfect: only the
chosen finite language is recorded as lossy.  All sibling faces continue to
factor through the same rooted occurrence and can be consumed independently.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace UnifiedFourFace

open SourceGeneratedPerfectification
open SourceGeneratedCanonicalPerfectPair
open SourceGeneratedPerfectAmbient

noncomputable section

universe s a c t l r h v d o z

variable {Source : Type s} {Algebra : Type a} {Combinatorial : Type c}
variable {Topological : Type t} {Logical : Type l} {Relation : Type r}
variable {Cochain : Type h} {Carrier : Type v} {DualTarget : Type d}
variable [AddCommGroup Carrier] [AddCommGroup DualTarget]

abbrev RootCarrier
    (_input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) : Type v :=
  Carrier

abbrev RootDualEvaluation
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    RootCarrier input →ₗ[ℤ] Module.Dual ℤ DualTarget :=
  input.dualEvaluationAt input.occurrence.root

abbrev RootFaithful
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    RootCarrier input →ₗ[ℤ] RootCarrier input :=
  input.faithfulAt input.occurrence.root

abbrev Perfectification
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) : Type v :=
  SourceGeneratedPerfectification.PerfectificationCarrier
    (RootDualEvaluation input)

def canonicalMap
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    RootCarrier input →ₗ[ℤ] Perfectification input :=
  SourceGeneratedPerfectification.canonicalMap (RootDualEvaluation input)

def dualEmbedding
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    Perfectification input →ₗ[ℤ] Module.Dual ℤ DualTarget :=
  SourceGeneratedPerfectification.dualEmbedding (RootDualEvaluation input)

@[simp] theorem dualEmbedding_comp_canonicalMap
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    (dualEmbedding input).comp (canonicalMap input) =
      RootDualEvaluation input :=
  SourceGeneratedPerfectification.dualEmbedding_comp_canonicalMap
    (RootDualEvaluation input)

theorem dualEmbedding_injective
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    Function.Injective (dualEmbedding input) :=
  SourceGeneratedPerfectification.dualEmbedding_injective
    (RootDualEvaluation input)

theorem canonicalMap_universal
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget)
    {Q : Type z} [AddCommGroup Q]
    (map : RootCarrier input →ₗ[ℤ] Q)
    (kernel_compatibility :
      LinearMap.ker (RootDualEvaluation input) ≤ LinearMap.ker map) :
    ∃! factor : Perfectification input →ₗ[ℤ] Q,
      factor.comp (canonicalMap input) = map :=
  SourceGeneratedPerfectification.canonicalMap_universal
    (RootDualEvaluation input) map kernel_compatibility

def perfectificationDisposition
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    SourceGeneratedPerfectification.PerfectificationDisposition
      (RootDualEvaluation input) :=
  SourceGeneratedPerfectification.settlePerfectification
    (RootDualEvaluation input)

def presentationDisposition
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    SourceGeneratedPerfectification.PerfectificationPresentationDisposition
      (RootDualEvaluation input) :=
  SourceGeneratedPerfectification.settlePerfectificationPresentation
    (RootDualEvaluation input)

def ambientExtensionDisposition
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    SourceGeneratedPerfectAmbient.PerfectAmbientExtensionDisposition
      (RootDualEvaluation input) :=
  SourceGeneratedPerfectAmbient.settlePerfectAmbientExtension
    (RootDualEvaluation input)

def faithfulFactorizationDisposition
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    SourceGeneratedPerfectification.FaithfulFactorizationDisposition
      (RootDualEvaluation input) (RootFaithful input) :=
  SourceGeneratedPerfectification.settleFaithfulFactorization
    (RootDualEvaluation input) (RootFaithful input)

def ambientLiftDisposition
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    SourceGeneratedPerfectification.SourceGeneratedAmbientLiftDisposition
      (RootDualEvaluation input) (RootFaithful input) :=
  SourceGeneratedPerfectification.settleSourceGeneratedAmbientLift
    (RootDualEvaluation input) (RootFaithful input)

/-! The input carries one canonical faithful map, while downstream consumers
may present any actual additive target.  These polymorphic readouts keep that
target outside the producer's finite/perfect assumptions. -/

def faithfulFactorizationDispositionFor
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget)
    {A : Type z} [AddCommGroup A]
    (faithful : RootCarrier input →ₗ[ℤ] A) :
    SourceGeneratedPerfectification.FaithfulFactorizationDisposition
      (RootDualEvaluation input) faithful :=
  SourceGeneratedPerfectification.settleFaithfulFactorization
    (RootDualEvaluation input) faithful

def ambientLiftDispositionFor
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget)
    {A : Type z} [AddCommGroup A]
    (faithful : RootCarrier input →ₗ[ℤ] A) :
    SourceGeneratedPerfectification.SourceGeneratedAmbientLiftDisposition
      (RootDualEvaluation input) faithful :=
  SourceGeneratedPerfectification.settleSourceGeneratedAmbientLift
    (RootDualEvaluation input) faithful

/-! The complete package is generated from the input; no branch is supplied by
the caller. -/

structure Generated
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    Type (max (max (max (max (max (max (max (max s a) c) t) l) r) h) v) d + 4) where
  algebraFace : RootedAccountedUnfolding Algebra
  combinatorialFace : RootedAccountedUnfolding Combinatorial
  topologicalFace : RootedAccountedUnfolding Topological
  logicalFace : RootedAccountedUnfolding Logical
  relationFace : RootedAccountedUnfolding Relation
  cochainFace : RootedAccountedUnfolding Cochain
  evaluationFace : RootedAccountedUnfolding
    (Carrier →ₗ[ℤ] Module.Dual ℤ DualTarget)
  faithfulFace : RootedAccountedUnfolding (Carrier →ₗ[ℤ] Carrier)
  canonical : RootCarrier input →ₗ[ℤ] Perfectification input
  embedding : Perfectification input →ₗ[ℤ] Module.Dual ℤ DualTarget
  canonicalPerfectPair :
    SourceGeneratedCanonicalPerfectPair.Generated (RootDualEvaluation input)
  perfectification :
    SourceGeneratedPerfectification.PerfectificationDisposition
      (RootDualEvaluation input)
  presentation :
    SourceGeneratedPerfectification.PerfectificationPresentationDisposition
      (RootDualEvaluation input)
  ambientExtension :
    SourceGeneratedPerfectAmbient.PerfectAmbientExtensionDisposition
      (RootDualEvaluation input)
  faithful :
    SourceGeneratedPerfectification.FaithfulFactorizationDisposition
      (RootDualEvaluation input) (RootFaithful input)
  ambientLift :
    SourceGeneratedPerfectification.SourceGeneratedAmbientLiftDisposition
      (RootDualEvaluation input) (RootFaithful input)

def generate
    (input : Input Source Algebra Combinatorial Topological Logical Relation
    Cochain Carrier DualTarget) : Generated input where
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
  canonicalPerfectPair := SourceGeneratedCanonicalPerfectPair.generate
    (RootDualEvaluation input)
  perfectification := perfectificationDisposition input
  presentation := presentationDisposition input
  ambientExtension := ambientExtensionDisposition input
  faithful := faithfulFactorizationDisposition input
  ambientLift := ambientLiftDisposition input

theorem generated_total
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) : Nonempty (Generated input) :=
  ⟨generate input⟩

@[simp] theorem generated_canonical
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    (generate input).canonical = canonicalMap input :=
  rfl

@[simp] theorem generated_algebraFace
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    (generate input).algebraFace = input.AlgebraOccurrence :=
  rfl

@[simp] theorem generated_combinatorialFace
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    (generate input).combinatorialFace = input.CombinatorialOccurrence :=
  rfl

@[simp] theorem generated_topologicalFace
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    (generate input).topologicalFace = input.TopologicalOccurrence :=
  rfl

@[simp] theorem generated_logicalFace
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    (generate input).logicalFace = input.LogicalOccurrence :=
  rfl

@[simp] theorem generated_relationFace
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    (generate input).relationFace = input.RelationOccurrence :=
  rfl

@[simp] theorem generated_cochainFace
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    (generate input).cochainFace = input.CochainOccurrence :=
  rfl

@[simp] theorem generated_evaluationFace
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    (generate input).evaluationFace = input.EvaluationOccurrence :=
  rfl

@[simp] theorem generated_faithfulFace
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    (generate input).faithfulFace = input.FaithfulOccurrence :=
  rfl

@[simp] theorem generated_embedding
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    (generate input).embedding = dualEmbedding input :=
  rfl

theorem generated_dual_readback
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    ((generate input).embedding).comp (generate input).canonical =
      RootDualEvaluation input := by
  exact dualEmbedding_comp_canonicalMap input

/-! ## Finite observation and source morphism faces -/

def finiteObservationDisposition
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget)
    {O : Type z} [AddCommGroup O]
    (observation : Perfectification input →ₗ[ℤ] O) :
    SourceGeneratedPerfectification.FiniteObservationDisposition observation :=
  SourceGeneratedPerfectification.settleFiniteObservation observation

def boundedDualizableObservationDisposition
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget)
    {O : Type z} [AddCommGroup O]
    (observation : Perfectification input →ₗ[ℤ] O) :
    SourceGeneratedPerfectification.BoundedDualizableObservationDisposition
      (RootDualEvaluation input) observation :=
  SourceGeneratedPerfectification.settleBoundedDualizableObservation
    (RootDualEvaluation input) observation

structure SourceMorphism
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget)
    (Source' : Type s) (Algebra' : Type a) (Combinatorial' : Type c)
    (Topological' : Type t) (Logical' : Type l) (Relation' : Type r)
    (Cochain' : Type h) (Carrier' : Type v) (DualTarget' : Type d)
    [AddCommGroup Carrier'] [AddCommGroup DualTarget']
    (input' : Input Source' Algebra' Combinatorial' Topological' Logical'
      Relation' Cochain' Carrier' DualTarget') where
  sourceMap : Source → Source'
  occurrence_map : input'.occurrence = input.occurrence.map sourceMap
  carrierMap : RootCarrier input →ₗ[ℤ] RootCarrier input'
  dualMap : DualTarget' →ₗ[ℤ] DualTarget
  naturality :
    (SourceGeneratedPerfectification.inducedDualTarget dualMap).comp
        (RootDualEvaluation input) =
      (RootDualEvaluation input').comp carrierMap

def SourceMorphism.id
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    SourceMorphism input Source Algebra Combinatorial Topological Logical
      Relation Cochain Carrier DualTarget input where
  sourceMap := fun value => value
  occurrence_map := (RootedAccountedUnfolding.map_id input.occurrence).symm
  carrierMap := LinearMap.id
  dualMap := LinearMap.id
  naturality := by
    apply LinearMap.ext
    intro value
    rfl

theorem inducedDualTarget_comp
    {D₁ : Type d} {D₂ : Type d} {D₃ : Type d}
    [AddCommGroup D₁] [AddCommGroup D₂] [AddCommGroup D₃]
    (first : D₂ →ₗ[ℤ] D₁) (second : D₃ →ₗ[ℤ] D₂) :
    SourceGeneratedPerfectification.inducedDualTarget
        (first.comp second) =
      (SourceGeneratedPerfectification.inducedDualTarget second).comp
        (SourceGeneratedPerfectification.inducedDualTarget first) := by
  apply LinearMap.ext
  intro functional
  apply LinearMap.ext
  intro value
  rfl

theorem inducedDualTarget_id
    {D : Type d} [AddCommGroup D] :
    SourceGeneratedPerfectification.inducedDualTarget
        (LinearMap.id : D →ₗ[ℤ] D) = LinearMap.id := by
  apply LinearMap.ext
  intro functional
  apply LinearMap.ext
  intro value
  rfl

def SourceMorphism.comp
    {Source₁ : Type s} {Algebra₁ : Type a} {Combinatorial₁ : Type c}
    {Topological₁ : Type t} {Logical₁ : Type l} {Relation₁ : Type r}
    {Cochain₁ : Type h} {Carrier₁ : Type v} {DualTarget₁ : Type d}
    [AddCommGroup Carrier₁] [AddCommGroup DualTarget₁]
    {Source₂ : Type s} {Algebra₂ : Type a} {Combinatorial₂ : Type c}
    {Topological₂ : Type t} {Logical₂ : Type l} {Relation₂ : Type r}
    {Cochain₂ : Type h} {Carrier₂ : Type v} {DualTarget₂ : Type d}
    [AddCommGroup Carrier₂] [AddCommGroup DualTarget₂]
    {Source₃ : Type s} {Algebra₃ : Type a} {Combinatorial₃ : Type c}
    {Topological₃ : Type t} {Logical₃ : Type l} {Relation₃ : Type r}
    {Cochain₃ : Type h} {Carrier₃ : Type v} {DualTarget₃ : Type d}
    [AddCommGroup Carrier₃] [AddCommGroup DualTarget₃]
    (input₁ : Input Source₁ Algebra₁ Combinatorial₁ Topological₁ Logical₁
      Relation₁ Cochain₁ Carrier₁ DualTarget₁)
    (input₂ : Input Source₂ Algebra₂ Combinatorial₂ Topological₂ Logical₂
      Relation₂ Cochain₂ Carrier₂ DualTarget₂)
    (input₃ : Input Source₃ Algebra₃ Combinatorial₃ Topological₃ Logical₃
      Relation₃ Cochain₃ Carrier₃ DualTarget₃)
    (first : SourceMorphism input₁ Source₂ Algebra₂ Combinatorial₂ Topological₂
      Logical₂ Relation₂ Cochain₂ Carrier₂ DualTarget₂ input₂)
    (second : SourceMorphism input₂ Source₃ Algebra₃ Combinatorial₃ Topological₃
      Logical₃ Relation₃ Cochain₃ Carrier₃ DualTarget₃ input₃) :
    SourceMorphism input₁ Source₃ Algebra₃ Combinatorial₃ Topological₃
      Logical₃ Relation₃ Cochain₃ Carrier₃ DualTarget₃ input₃ where
  sourceMap := second.sourceMap ∘ first.sourceMap
  occurrence_map := by
    calc
      input₃.occurrence = input₂.occurrence.map second.sourceMap :=
        second.occurrence_map
      _ = (input₁.occurrence.map first.sourceMap).map second.sourceMap := by
        rw [first.occurrence_map]
      _ = input₁.occurrence.map (second.sourceMap ∘ first.sourceMap) :=
        RootedAccountedUnfolding.map_map second.sourceMap first.sourceMap
          input₁.occurrence
  carrierMap := second.carrierMap.comp first.carrierMap
  dualMap := first.dualMap.comp second.dualMap
  naturality := by
    apply LinearMap.ext
    intro value
    apply LinearMap.ext
    intro target
    change (RootDualEvaluation input₁ value)
        (first.dualMap (second.dualMap target)) =
      (RootDualEvaluation input₃
        (second.carrierMap (first.carrierMap value))) target
    have first_eval := congrArg (fun functional =>
        functional (second.dualMap target))
      (LinearMap.congr_fun first.naturality value)
    have second_eval := congrArg (fun functional => functional target)
      (LinearMap.congr_fun second.naturality
        (first.carrierMap value))
    exact first_eval.trans second_eval

@[simp] theorem SourceMorphism.root_map
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget)
    (Source' : Type s) (Algebra' : Type a) (Combinatorial' : Type c)
    (Topological' : Type t) (Logical' : Type l) (Relation' : Type r)
    (Cochain' : Type h) (Carrier' : Type v) (DualTarget' : Type d)
    [AddCommGroup Carrier'] [AddCommGroup DualTarget']
    (input' : Input Source' Algebra' Combinatorial' Topological' Logical'
      Relation' Cochain' Carrier' DualTarget')
    (morphism : SourceMorphism input Source' Algebra' Combinatorial'
      Topological' Logical' Relation' Cochain' Carrier' DualTarget' input') :
    input'.occurrence.root = morphism.sourceMap input.occurrence.root := by
  rw [morphism.occurrence_map, RootedAccountedUnfolding.root_map]

def inducedPerfectificationMap
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget)
    (Source' : Type s) (Algebra' : Type a) (Combinatorial' : Type c)
    (Topological' : Type t) (Logical' : Type l) (Relation' : Type r)
    (Cochain' : Type h) (Carrier' : Type v) (DualTarget' : Type d)
    [AddCommGroup Carrier'] [AddCommGroup DualTarget']
    (input' : Input Source' Algebra' Combinatorial' Topological' Logical'
      Relation' Cochain' Carrier' DualTarget')
    (morphism : SourceMorphism input Source' Algebra' Combinatorial'
      Topological' Logical' Relation' Cochain' Carrier' DualTarget' input') :
    Perfectification input →ₗ[ℤ] Perfectification input' :=
  SourceGeneratedPerfectification.inducedPerfectificationMap
    (RootDualEvaluation input) (RootDualEvaluation input')
    morphism.carrierMap morphism.dualMap morphism.naturality

theorem inducedPerfectificationMap_id
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget) :
    inducedPerfectificationMap input Source Algebra Combinatorial Topological
      Logical Relation Cochain Carrier DualTarget input (SourceMorphism.id input) =
      LinearMap.id := by
  apply LinearMap.ext
  intro quotient
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective
      (LinearMap.ker (RootDualEvaluation input)) quotient
  rfl

theorem inducedPerfectificationMap_comp
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget)
    (Source' : Type s) (Algebra' : Type a) (Combinatorial' : Type c)
    (Topological' : Type t) (Logical' : Type l) (Relation' : Type r)
    (Cochain' : Type h) (Carrier' : Type v) (DualTarget' : Type d)
    [AddCommGroup Carrier'] [AddCommGroup DualTarget']
    (input' : Input Source' Algebra' Combinatorial' Topological' Logical'
      Relation' Cochain' Carrier' DualTarget')
    (morphism : SourceMorphism input Source' Algebra' Combinatorial'
      Topological' Logical' Relation' Cochain' Carrier' DualTarget' input') :
    (inducedPerfectificationMap input Source' Algebra' Combinatorial'
      Topological' Logical' Relation' Cochain' Carrier' DualTarget' input'
      morphism).comp (canonicalMap input) =
      (canonicalMap input').comp morphism.carrierMap :=
  SourceGeneratedPerfectification.inducedPerfectificationMap_comp
    (RootDualEvaluation input) (RootDualEvaluation input')
    morphism.carrierMap morphism.dualMap morphism.naturality

theorem inducedPerfectificationMap_comp_morphism
    {Source₁ : Type s} {Algebra₁ : Type a} {Combinatorial₁ : Type c}
    {Topological₁ : Type t} {Logical₁ : Type l} {Relation₁ : Type r}
    {Cochain₁ : Type h} {Carrier₁ : Type v} {DualTarget₁ : Type d}
    [AddCommGroup Carrier₁] [AddCommGroup DualTarget₁]
    {Source₂ : Type s} {Algebra₂ : Type a} {Combinatorial₂ : Type c}
    {Topological₂ : Type t} {Logical₂ : Type l} {Relation₂ : Type r}
    {Cochain₂ : Type h} {Carrier₂ : Type v} {DualTarget₂ : Type d}
    [AddCommGroup Carrier₂] [AddCommGroup DualTarget₂]
    {Source₃ : Type s} {Algebra₃ : Type a} {Combinatorial₃ : Type c}
    {Topological₃ : Type t} {Logical₃ : Type l} {Relation₃ : Type r}
    {Cochain₃ : Type h} {Carrier₃ : Type v} {DualTarget₃ : Type d}
    [AddCommGroup Carrier₃] [AddCommGroup DualTarget₃]
    (input₁ : Input Source₁ Algebra₁ Combinatorial₁ Topological₁ Logical₁
      Relation₁ Cochain₁ Carrier₁ DualTarget₁)
    (input₂ : Input Source₂ Algebra₂ Combinatorial₂ Topological₂ Logical₂
      Relation₂ Cochain₂ Carrier₂ DualTarget₂)
    (input₃ : Input Source₃ Algebra₃ Combinatorial₃ Topological₃ Logical₃
      Relation₃ Cochain₃ Carrier₃ DualTarget₃)
    (first : SourceMorphism input₁ Source₂ Algebra₂ Combinatorial₂ Topological₂
      Logical₂ Relation₂ Cochain₂ Carrier₂ DualTarget₂ input₂)
    (second : SourceMorphism input₂ Source₃ Algebra₃ Combinatorial₃ Topological₃
      Logical₃ Relation₃ Cochain₃ Carrier₃ DualTarget₃ input₃) :
    inducedPerfectificationMap input₁ Source₃ Algebra₃ Combinatorial₃ Topological₃
      Logical₃ Relation₃ Cochain₃ Carrier₃ DualTarget₃ input₃
      (SourceMorphism.comp input₁ input₂ input₃ first second) =
      (inducedPerfectificationMap input₂ Source₃ Algebra₃ Combinatorial₃
        Topological₃ Logical₃ Relation₃ Cochain₃ Carrier₃ DualTarget₃ input₃
        second).comp
        (inducedPerfectificationMap input₁ Source₂ Algebra₂ Combinatorial₂
          Topological₂ Logical₂ Relation₂ Cochain₂ Carrier₂ DualTarget₂ input₂
          first) := by
  apply LinearMap.ext
  intro quotient
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective
      (LinearMap.ker (RootDualEvaluation input₁)) quotient
  rfl

theorem dualEmbedding_naturality
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget)
    (Source' : Type s) (Algebra' : Type a) (Combinatorial' : Type c)
    (Topological' : Type t) (Logical' : Type l) (Relation' : Type r)
    (Cochain' : Type h) (Carrier' : Type v) (DualTarget' : Type d)
    [AddCommGroup Carrier'] [AddCommGroup DualTarget']
    (input' : Input Source' Algebra' Combinatorial' Topological' Logical'
      Relation' Cochain' Carrier' DualTarget')
    (morphism : SourceMorphism input Source' Algebra' Combinatorial'
      Topological' Logical' Relation' Cochain' Carrier' DualTarget' input') :
    (dualEmbedding input').comp
        (inducedPerfectificationMap input Source' Algebra' Combinatorial'
          Topological' Logical' Relation' Cochain' Carrier' DualTarget' input'
          morphism) =
      (SourceGeneratedPerfectification.inducedDualTarget morphism.dualMap).comp
        (dualEmbedding input) :=
  SourceGeneratedPerfectification.dualEmbedding_naturality
    (RootDualEvaluation input) (RootDualEvaluation input')
    morphism.carrierMap morphism.dualMap morphism.naturality

def inducedGeneratedDualImageMap
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget)
    (Source' : Type s) (Algebra' : Type a) (Combinatorial' : Type c)
    (Topological' : Type t) (Logical' : Type l) (Relation' : Type r)
    (Cochain' : Type h) (Carrier' : Type v) (DualTarget' : Type d)
    [AddCommGroup Carrier'] [AddCommGroup DualTarget']
    (input' : Input Source' Algebra' Combinatorial' Topological' Logical'
      Relation' Cochain' Carrier' DualTarget')
    (morphism : SourceMorphism input Source' Algebra' Combinatorial'
      Topological' Logical' Relation' Cochain' Carrier' DualTarget' input') :
    SourceGeneratedCanonicalPerfectPair.GeneratedDual
        (RootDualEvaluation input) →ₗ[ℤ]
      SourceGeneratedCanonicalPerfectPair.GeneratedDual
        (RootDualEvaluation input') :=
  SourceGeneratedCanonicalPerfectPair.inducedDualImageMap
    (RootDualEvaluation input) (RootDualEvaluation input')
    morphism.carrierMap morphism.dualMap morphism.naturality

theorem generatedDualImage_naturality
    (input : Input Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget)
    (Source' : Type s) (Algebra' : Type a) (Combinatorial' : Type c)
    (Topological' : Type t) (Logical' : Type l) (Relation' : Type r)
    (Cochain' : Type h) (Carrier' : Type v) (DualTarget' : Type d)
    [AddCommGroup Carrier'] [AddCommGroup DualTarget']
    (input' : Input Source' Algebra' Combinatorial' Topological' Logical'
      Relation' Cochain' Carrier' DualTarget')
    (morphism : SourceMorphism input Source' Algebra' Combinatorial'
      Topological' Logical' Relation' Cochain' Carrier' DualTarget' input') :
    (inducedGeneratedDualImageMap input Source' Algebra' Combinatorial'
      Topological' Logical' Relation' Cochain' Carrier' DualTarget' input'
      morphism).comp
      (SourceGeneratedCanonicalPerfectPair.generatedDualMap
        (RootDualEvaluation input)) =
      (SourceGeneratedCanonicalPerfectPair.generatedDualMap
        (RootDualEvaluation input')).comp
        (inducedPerfectificationMap input Source' Algebra' Combinatorial'
          Topological' Logical' Relation' Cochain' Carrier' DualTarget' input'
          morphism) :=
  SourceGeneratedCanonicalPerfectPair.generatedDualMap_naturality
    (RootDualEvaluation input) (RootDualEvaluation input')
    morphism.carrierMap morphism.dualMap morphism.naturality

end
end UnifiedFourFace
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
