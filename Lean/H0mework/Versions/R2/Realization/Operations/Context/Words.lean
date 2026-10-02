import H0mework.Versions.R2.Realization.Operations.Context.Expression
import H0mework.Realization.Operations.ScalarRelations

/-! All integral formal words retain the original values and full effects under actual context action. -/

set_option autoImplicit false

universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Context

open SourceOperationEffects SourceOperationScalarRelations

noncomputable section

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ sort, AddCommGroup (PhysicalValue sort)]

def words (readEnv : process.State → Env PhysicalValue PhysicalVar) {s : Sorts} :
    Formal ℤ PhysicalValue PhysicalVar s →ₗ[ℤ] Formal ℤ (Value process PhysicalValue) (Var Sorts) (.inl s) :=
  Finsupp.lmapDomain ℤ ℤ (embed readEnv)

theorem inventory_square (readEnv : process.State → Env PhysicalValue PhysicalVar) {s : Sorts}
    (runtime : LivingRuntimeState process) :
    (updateInventory (R := ℤ) (environment (point runtime))
      (environment (point runtime.tick.next - point runtime))).comp (words (s := s) readEnv) =
      updateInventory (R := ℤ) (readEnv runtime.state)
        (readEnv runtime.tick.next.state - readEnv runtime.state) := by
  apply Finsupp.lhom_ext
  intro expression coefficient
  simp only [LinearMap.comp_apply, words, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    updateInventory, LinearMap.prod_apply, Function.prod, evaluation, effectEvaluator,
    Finsupp.linearCombination_single]
  apply Prod.ext
  · exact congrArg (fun value => coefficient • value) (embed_eval readEnv expression runtime)
  · exact congrArg (fun value => coefficient • value) (embed_effect readEnv expression runtime)

theorem next_inventory_square (readEnv : process.State → Env PhysicalValue PhysicalVar) {s : Sorts}
    (runtime : LivingRuntimeState process) :
    (updateInventory (R := ℤ) (environment (point runtime))
      (environment (point runtime.tick.next - point runtime))).comp
        ((substitution (R := ℤ) binding).comp (words (s := s) readEnv)) =
      updateInventory (R := ℤ) (readEnv runtime.tick.next.state)
        (readEnv runtime.tick.next.tick.next.state - readEnv runtime.tick.next.state) := by
  apply Finsupp.lhom_ext
  intro expression coefficient
  simp only [LinearMap.comp_apply, words, substitution, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, updateInventory, LinearMap.prod_apply, Function.prod,
    evaluation, effectEvaluator, Finsupp.linearCombination_single]
  apply Prod.ext
  · exact congrArg (fun value => coefficient • value)
      (congrArg Prod.fst (literalnext_pair readEnv expression runtime))
  · exact congrArg (fun value => coefficient • value)
      (congrArg Prod.snd (literalnext_pair readEnv expression runtime))

end
end SourceOperationNative.Context
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
