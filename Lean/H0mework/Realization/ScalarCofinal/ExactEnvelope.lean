import H0mework.Realization.ScalarCofinal.RootOccurrence
import H0mework.Realization.Perfectification.ScalarEnvelope

/-!
# Scalar cofinal exact envelope

The canonical `ModuleCat R` inverse limit of one rooted evaluator history is
fed directly into the scalar exact-envelope producer.  The resulting source
map is the composite

`Generator → cofinal completion → completion / ker(e)`.

No finite, projective, perfect, determinant, kernel-separation, or coverage
premise enters this junction.  The dual evaluation is source material; the
coimage, generated dual image, coevaluation, zig-zags, and universal exact
target factorization are generated from it.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarCofinalExactEnvelope

open SourceGeneratedScalarCofinalKernelCompletion
open SourceGeneratedScalarCofinalRootOccurrence
open SourceGeneratedScalarPerfectification
open SourceGeneratedScalarExactEnvelope

noncomputable section

universe r u w d a b

variable {R : Type r} [CommRing R]
variable {Root : Type w}
variable {Generator : Type u} [AddCommGroup Generator] [Module R Generator]
variable {StageCarrier : Nat → Type u}
variable [∀ stage, AddCommGroup (StageCarrier stage)]
variable [∀ stage, Module R (StageCarrier stage)]
variable {rootOccurrence : RootedAccountedUnfolding
  (Root × Data (R := R) (Generator := Generator) (Carrier := StageCarrier))}
variable (face : Face rootOccurrence)
variable (calculation : Face.GeneratedCompatibilityCalculationAt face)
variable {DualTarget : Type d}
variable [AddCommGroup DualTarget] [Module R DualTarget]
variable (evaluation : face.completion calculation →ₗ[R]
  Module.Dual R DualTarget)

abbrev Carrier :=
  SourceGeneratedScalarPerfectification.PerfectificationCarrier evaluation

abbrev GeneratedDual :=
  SourceGeneratedScalarExactEnvelope.GeneratedDual evaluation

/-- The exact perfect envelope of the actual cofinal completion. -/
def envelope : UniversalPerfectEnvelope evaluation :=
  sourceGeneratedPerfectification evaluation

/-- The original source enters the exact envelope through the generated
cofinal completion map, never through a caller-selected lift. -/
def sourceMap : Generator →ₗ[R] Carrier face calculation evaluation :=
  (canonicalMap evaluation).comp (face.completionMap calculation).hom

theorem envelope_total :
    Nonempty (UniversalPerfectEnvelope evaluation) :=
  universalPerfectEnvelope_total evaluation

theorem preserves_root :
    face.root = rootOccurrence.map Prod.fst :=
  rfl

/-- The completed source evaluation is recovered literally from the exact
envelope's generated dual map and ambient inclusion. -/
theorem completion_evaluation_readback :
    ((dualInclusion evaluation).comp (generatedDualMap evaluation)).comp
        (canonicalMap evaluation) = evaluation :=
  source_evaluation_readback evaluation

/-- The same readback after precomposition with the original source map. -/
theorem source_evaluation_readback :
    ((dualInclusion evaluation).comp (generatedDualMap evaluation)).comp
        (sourceMap face calculation evaluation) =
      evaluation.comp (face.completionMap calculation).hom := by
  apply LinearMap.ext
  intro value
  rfl

/-- Source loss at the perfectification mouth is exactly evaluation-kernel
loss on the already generated cofinal completion. -/
theorem sourceMap_eq_zero_iff (value : Generator) :
    sourceMap face calculation evaluation value = 0 ↔
      evaluation (face.completionMap calculation value) = 0 := by
  change Submodule.mkQ (LinearMap.ker evaluation)
      (face.completionMap calculation value) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker]

/-- The existing universal property is now available on the actual completed
carrier; compatible targets are quantified downstream and are not producer
premises. -/
theorem completion_universal_property
    {TargetCarrier : Type a} {TargetDual : Type b}
    [AddCommGroup TargetCarrier] [Module R TargetCarrier]
    [AddCommGroup TargetDual] [Module R TargetDual]
    (target : CompatiblePerfectTarget evaluation TargetCarrier TargetDual) :
    ∃! morphism : EnvelopeMorphism evaluation target,
      morphism.carrierMap.comp (canonicalMap evaluation) = target.sourceMap :=
  universal_property evaluation target

end
end SourceGeneratedScalarCofinalExactEnvelope
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
