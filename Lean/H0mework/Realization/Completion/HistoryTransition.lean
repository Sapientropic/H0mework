import H0mework.Realization.Completion.HistorySettlement

/-!
# Root-generated cofinal-history transitions

Two actual cofinal relation histories on the same free generator language
either generate the canonical identity-on-generators map between their
presented completion carriers, or expose the first generator/relation
coordinate that the target representation has lost.

No carrier map, naturality square, finite model, branch, endpoint, ledger or
next current enters the constructor.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalHistoryTransition

open CofinalHistorySettlement

noncomputable section

universe u w₁ w₂

variable {Root₁ : Type w₁} {Root₂ : Type w₂} {Generator : Type u}
variable {rootOccurrence₁ : RootedAccountedUnfolding Root₁}
variable {rootOccurrence₂ : RootedAccountedUnfolding Root₂}
variable {seedOccurrence₁ seedOccurrence₂ :
  RootedAccountedUnfolding (PresentedRelationEventAt Generator)}
variable {continuationOccurrence₁ continuationOccurrence₂ :
  RootedAccountedUnfolding
    (PresentedRelationEventAt Generator →
      RootedAccountedUnfolding (PresentedRelationEventAt Generator))}

variable (source : RootGeneratedCofinalHistoryAt rootOccurrence₁
  seedOccurrence₁ continuationOccurrence₁)
variable (target : RootGeneratedCofinalHistoryAt rootOccurrence₂
  seedOccurrence₂ continuationOccurrence₂)

/-- The identity free-generator coordinate restricted to the two actual
closures. -/
def generatorInclusion
    (generatorCompatible : source.generatorClosure ≤ target.generatorClosure) :
    source.generatorClosure →ₗ[ℤ] target.generatorClosure :=
  Submodule.inclusion generatorCompatible

/-- Free transition followed by the target quotient projection. -/
def freeTransition
    (generatorCompatible : source.generatorClosure ≤ target.generatorClosure) :
    source.generatorClosure →ₗ[ℤ] target.CompletionCarrier :=
  target.completionProjection.comp
    (generatorInclusion source target generatorCompatible)

/-- Source relations remain zero after the canonical generator inclusion. -/
def RelationCompatible
    (generatorCompatible : source.generatorClosure ≤ target.generatorClosure) :
    Prop :=
  source.relationInGeneratorClosure ≤
    LinearMap.ker (freeTransition source target generatorCompatible)

/-- Positive transition evidence.  The completion map is generated from
these two exact inclusion laws and is not a field. -/
structure GeneratedTransition : Type (max u w₁ w₂) where
  private mk ::
  generatorCompatible : source.generatorClosure ≤ target.generatorClosure
  relationCompatible :
    RelationCompatible source target generatorCompatible

namespace GeneratedTransition

def create
    (generatorCompatible : source.generatorClosure ≤ target.generatorClosure)
    (relationCompatible :
      RelationCompatible source target generatorCompatible) :
    GeneratedTransition source target :=
  ⟨generatorCompatible, relationCompatible⟩

def generatorMap (generated : GeneratedTransition source target) :
    source.generatorClosure →ₗ[ℤ] target.generatorClosure :=
  generatorInclusion source target generated.generatorCompatible

/-- Canonical quotient transition. -/
def completionMap (generated : GeneratedTransition source target) :
    source.CompletionCarrier →ₗ[ℤ] target.CompletionCarrier :=
  source.relationInGeneratorClosure.liftQ
    (freeTransition source target generated.generatorCompatible)
    generated.relationCompatible

@[simp] theorem completionMap_projection
    (generated : GeneratedTransition source target)
    (value : source.generatorClosure) :
    completionMap source target generated (source.completionProjection value) =
      target.completionProjection (generatorMap source target generated value) := by
  exact Submodule.liftQ_apply _ _ _

theorem completionMap_comp_projection
    (generated : GeneratedTransition source target) :
    (completionMap source target generated).comp source.completionProjection =
      target.completionProjection.comp (generatorMap source target generated) := by
  apply LinearMap.ext
  intro value
  exact completionMap_projection source target generated value

/-- The transition is uniquely fixed by its free-generator readback. -/
theorem completionMap_unique
    (generated : GeneratedTransition source target)
    (other : source.CompletionCarrier →ₗ[ℤ] target.CompletionCarrier)
    (other_commutes : other.comp source.completionProjection =
      target.completionProjection.comp
        (generatorMap source target generated)) :
    other = completionMap source target generated := by
  apply LinearMap.ext
  intro value
  obtain ⟨representative, rfl⟩ :=
    Submodule.Quotient.mk_surjective source.relationInGeneratorClosure value
  change other (source.completionProjection representative) =
    completionMap source target generated
      (source.completionProjection representative)
  have readback := LinearMap.congr_fun other_commutes representative
  calc
    other (source.completionProjection representative) =
        target.completionProjection
          (generatorMap source target generated representative) := by
      simpa only [LinearMap.comp_apply] using readback
    _ = completionMap source target generated
          (source.completionProjection representative) := by
      exact (completionMap_projection source target generated
        representative).symm

@[simp] theorem completionMap_self_eq_id
    (generated : GeneratedTransition source source) :
    completionMap source source generated = LinearMap.id := by
  symm
  apply completionMap_unique source source generated
  apply LinearMap.ext
  intro coordinate
  rfl

end GeneratedTransition

/-- Exact generator coordinate present in the source history but absent from
the target history. -/
structure GeneratorResidual where
  coordinate : Generator →₀ ℤ
  source_mem : coordinate ∈ source.generatorClosure
  target_not_mem : coordinate ∉ target.generatorClosure

/-- Exact source relation whose identity transport is nonzero in the target
presented completion. -/
structure RelationResidual
    (generatorCompatible : source.generatorClosure ≤ target.generatorClosure) where
  coordinate : source.generatorClosure
  source_relation : coordinate ∈ source.relationInGeneratorClosure
  target_nonzero :
    freeTransition source target generatorCompatible coordinate ≠ 0

/-- Positive canonical transition or one of the two exact representation
residuals. -/
inductive TransitionDisposition : Type (max u w₁ w₂) where
  | generated (transition : GeneratedTransition source target)
  | generatorResidual (residual : GeneratorResidual source target)
  | relationResidual
      (generatorCompatible : source.generatorClosure ≤ target.generatorClosure)
      (residual : RelationResidual source target generatorCompatible)

/-- Total source-language transition disposition. -/
noncomputable def settle : TransitionDisposition source target := by
  classical
  by_cases generatorCompatible :
      source.generatorClosure ≤ target.generatorClosure
  · by_cases relationCompatible :
        RelationCompatible source target generatorCompatible
    · exact .generated
        (GeneratedTransition.create source target generatorCompatible
          relationCompatible)
    · have existsCoordinate : ∃ coordinate,
          ∃ (_ : coordinate ∈ source.relationInGeneratorClosure),
            freeTransition source target generatorCompatible coordinate ≠ 0 := by
        simpa only [RelationCompatible, SetLike.le_def, LinearMap.mem_ker,
          not_forall] using relationCompatible
      let coordinate := Classical.choose existsCoordinate
      have existsSourceRelation := Classical.choose_spec existsCoordinate
      let sourceRelation := Classical.choose existsSourceRelation
      have targetNonzero := Classical.choose_spec existsSourceRelation
      exact .relationResidual generatorCompatible
        ⟨coordinate, sourceRelation, targetNonzero⟩
  · have existsCoordinate : ∃ coordinate,
        ∃ (_ : coordinate ∈ source.generatorClosure),
          coordinate ∉ target.generatorClosure := by
      simpa only [SetLike.le_def, not_forall] using generatorCompatible
    let coordinate := Classical.choose existsCoordinate
    have existsSourceMem := Classical.choose_spec existsCoordinate
    let sourceMem := Classical.choose existsSourceMem
    have targetNotMem := Classical.choose_spec existsSourceMem
    exact .generatorResidual
      ⟨coordinate, sourceMem, targetNotMem⟩

theorem settle_eq_generated_of_compatible
    (generatorCompatible : source.generatorClosure ≤ target.generatorClosure)
    (relationCompatible :
      RelationCompatible source target generatorCompatible) :
    ∃ transition, settle source target = .generated transition := by
  simp only [settle, generatorCompatible, relationCompatible]
  exact ⟨GeneratedTransition.create source target generatorCompatible
    relationCompatible, rfl⟩

theorem settle_self_is_generated :
    ∃ transition, settle source source = .generated transition := by
  let generatorCompatible :
      source.generatorClosure ≤ source.generatorClosure := le_rfl
  let relationCompatible :
      RelationCompatible source source generatorCompatible := by
    intro coordinate coordinate_mem
    rw [LinearMap.mem_ker]
    apply (Submodule.Quotient.mk_eq_zero
      source.relationInGeneratorClosure).2
    exact coordinate_mem
  exact settle_eq_generated_of_compatible source source
    generatorCompatible relationCompatible

theorem settle_eq_generatorResidual_of_not_le
    (not_le : ¬ source.generatorClosure ≤ target.generatorClosure) :
    ∃ residual, settle source target = .generatorResidual residual := by
  simp only [settle, not_le]
  have existsCoordinate : ∃ coordinate,
      ∃ (_ : coordinate ∈ source.generatorClosure),
        coordinate ∉ target.generatorClosure := by
    simpa only [SetLike.le_def, not_forall] using not_le
  exact ⟨⟨Classical.choose existsCoordinate,
    Classical.choose (Classical.choose_spec existsCoordinate),
    Classical.choose_spec (Classical.choose_spec existsCoordinate)⟩, rfl⟩

end

end CofinalHistoryTransition
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
