import H0mework.Versions.R2.Realization.Operations.Context.Relations
import H0mework.Realization.Operations.Substitution.Source

/-! Actual native binding acts on complete contextual witnesses and the original literal-next receipts. -/

set_option autoImplicit false

universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Context

open SourceOperationEffects SourceOperationDerivations SourceOperationScalarRelations
open SourceOperationScalarPresentation

noncomputable section

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ sort, AddCommGroup (PhysicalValue sort)]

private def retarget {OriginalSorts : Type u} {OriginalValue OriginalVar : OriginalSorts → Type u}
    [∀ sort, AddCommGroup (OriginalValue sort)] {first second : Env OriginalValue OriginalVar}
    {s : OriginalSorts} (same : first = second) (generator : RelationIndex ℤ second s) :
    RelationIndex ℤ first s := same.symm ▸ generator

private theorem retarget_boundary {OriginalSorts : Type u} {OriginalValue OriginalVar : OriginalSorts → Type u}
    [∀ sort, AddCommGroup (OriginalValue sort)] {first second : Env OriginalValue OriginalVar}
    {s : OriginalSorts} (same : first = second) (generator : RelationIndex ℤ second s) :
    relation (R := ℤ) first (retarget same generator) = relation (R := ℤ) second generator := by
  cases same
  rfl

def actionIndex (runtime : LivingRuntimeState process) {s : ContextSort Sorts} :
    RelationIndex ℤ (environment (PhysicalValue := PhysicalValue) (point runtime.tick.next)) s →
      RelationIndex ℤ (environment (PhysicalValue := PhysicalValue) (point runtime)) s :=
  fun generator => SourceSubstitution.index binding (environment (point runtime))
    (retarget (show SourceSubstitution.sourceEnvironment binding (environment (point runtime)) =
      environment (PhysicalValue := PhysicalValue) (point runtime.tick.next) from binding_eval runtime) generator)

def actionRelationWords (runtime : LivingRuntimeState process) {s : ContextSort Sorts} :
    (RelationIndex ℤ (environment (PhysicalValue := PhysicalValue) (point runtime.tick.next)) s →₀ ℤ) →ₗ[ℤ]
      (RelationIndex ℤ (environment (PhysicalValue := PhysicalValue) (point runtime)) s →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (actionIndex runtime)

theorem action_index_boundary (runtime : LivingRuntimeState process) {s : ContextSort Sorts}
    (generator : RelationIndex ℤ (environment (PhysicalValue := PhysicalValue) (point runtime.tick.next)) s) :
    relation (R := ℤ) (environment (point runtime)) (actionIndex runtime generator) =
      substitution (R := ℤ) binding (relation (R := ℤ)
        (environment (PhysicalValue := PhysicalValue) (point runtime.tick.next)) generator) := by
  unfold actionIndex
  rw [SourceSubstitution.index_boundary, retarget_boundary]

theorem action_boundary_square (runtime : LivingRuntimeState process) {s : ContextSort Sorts} :
    (relationMap (R := ℤ) (environment (PhysicalValue := PhysicalValue) (point runtime))).comp
      (actionRelationWords (s := s) runtime) =
        (substitution (R := ℤ) binding).comp
          (relationMap (R := ℤ) (environment (PhysicalValue := PhysicalValue) (point runtime.tick.next))) := by
  apply Finsupp.lhom_ext
  intro generator coefficient
  simp only [LinearMap.comp_apply, actionRelationWords, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, relationMap, Finsupp.linearCombination_single, map_smul]
  exact congrArg (fun value => coefficient • value) (action_index_boundary runtime generator)

def nextDerivation (readEnv : process.State → Env PhysicalValue PhysicalVar)
    (runtime : LivingRuntimeState process) {s : Sorts} {left right : Expr PhysicalValue PhysicalVar s}
    (proof : Derivation (readEnv runtime.tick.next.state) left right) :
    Derivation (environment (point runtime))
      ((embed readEnv left).subst binding) ((embed readEnv right).subst binding) :=
  Derivation.subst binding (environment (point runtime)) (by
    rw [binding_eval runtime]
    exact embedDerivation readEnv runtime.tick.next proof)

def nextRelationWords (readEnv : process.State → Env PhysicalValue PhysicalVar)
    (runtime : LivingRuntimeState process) {s : Sorts} :
    (RelationIndex ℤ (readEnv runtime.tick.next.state) s →₀ ℤ) →ₗ[ℤ]
      (RelationIndex ℤ (environment (PhysicalValue := PhysicalValue) (point runtime)) (Sum.inl s) →₀ ℤ) :=
  (actionRelationWords runtime).comp (embedRelationWords readEnv runtime.tick.next)

theorem next_boundary_square (readEnv : process.State → Env PhysicalValue PhysicalVar)
    (runtime : LivingRuntimeState process) {s : Sorts} :
    (relationMap (R := ℤ) (environment (PhysicalValue := PhysicalValue) (point runtime))).comp
      (nextRelationWords (s := s) readEnv runtime) =
        ((substitution (R := ℤ) binding).comp (words readEnv)).comp
          (relationMap (R := ℤ) (s := s) (readEnv runtime.tick.next.state)) := by
  unfold nextRelationWords
  rw [← LinearMap.comp_assoc, action_boundary_square, LinearMap.comp_assoc,
    embed_boundary_square, ← LinearMap.comp_assoc]

end
end SourceOperationNative.Context
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
