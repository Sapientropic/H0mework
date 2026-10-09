import H0mework.Versions.R2.Realization.Operations.FieldInputs
import H0mework.Versions.R2.Realization.Operations.RuntimeRelations
import H0mework.Realization.Operations.DerivationReduction

/-! The original native action rebinds every variable. Existing substitution
semantics generate the complete old/effect pair at the literal next stage. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Substitution
open SourceOperationEffects SourceOperationScalarRelations SourceOperationRuntime
open SourceGeneratedScalarCofinalKernelCompletion SourceGeneratedScalarCofinalNaturality
open CategoryTheory
noncomputable section
universe u
variable {N : WorldRelationNetwork.{u}} (process : SourceNativeLivingRootProcess N)

abbrev Value := Field.Value process
abbrev Var := Field.Var process
abbrev Word := FormalCarrier ℤ (Value process) (Var process) PUnit.unit

def binding : ∀ sort, Var process sort → Expr (Value process) (Var process) sort :=
  fun sort name => .linear (s := sort) (t := sort) (sourceAction process).toAddMonoidHom
    (.var (s := sort) name)

def words : Word process →ₗ[ℤ] Word process :=
  substitution (R := ℤ) (s := PUnit.unit) (binding process)

variable {process}

def oldEnv (runtime : LivingRuntimeState process) := Field.environment process (point runtime)
def incrementEnv (runtime : LivingRuntimeState process) :=
  Field.environment process (point runtime.tick.next - point runtime)

theorem binding_eval_environment (runtime : LivingRuntimeState process) :
    (fun sort name => (binding process sort name).eval (oldEnv runtime)) = oldEnv runtime.tick.next := by
  funext sort name
  change sourceAction process (point runtime) = point runtime.tick.next
  exact sourceAction_point runtime

theorem binding_effect_environment (runtime : LivingRuntimeState process) :
    (fun sort name => (binding process sort name).effect (oldEnv runtime) (incrementEnv runtime)) =
      incrementEnv runtime.tick.next := by
  funext sort name
  change sourceAction process (point runtime.tick.next - point runtime) =
    point runtime.tick.next.tick.next - point runtime.tick.next
  exact (map_sub (sourceAction process) _ _).trans
    (congrArg₂ (· - ·) (sourceAction_point runtime.tick.next) (sourceAction_point runtime))

theorem expression_pair (runtime : LivingRuntimeState process) {sort : PUnit.{u + 1}}
    (expression : Expr (Value process) (Var process) sort) :
    ((expression.subst (binding process)).eval (oldEnv runtime),
      (expression.subst (binding process)).effect (oldEnv runtime) (incrementEnv runtime)) =
    (expression.eval (oldEnv runtime.tick.next), expression.effect (oldEnv runtime.tick.next) (incrementEnv runtime.tick.next)) := by
  rw [Expr.eval_subst, Expr.effect_subst, binding_eval_environment, binding_effect_environment]

theorem stage_pair (runtime : LivingRuntimeState process) (word : Word process) :
    stageInventory (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process)
      (SourceGeneratedRuntimeMaterialStageAt.generate runtime) (words process word) =
    stageInventory (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process)
      (SourceGeneratedRuntimeMaterialStageAt.generate runtime.tick.next) word := by
  have old := evaluation_substitution (R := ℤ) (s := PUnit.unit) (binding process) (oldEnv runtime)
  rw [binding_eval_environment] at old
  have effect := effectEvaluator_substitution (R := ℤ) (s := PUnit.unit) (binding process)
    (oldEnv runtime) (incrementEnv runtime)
  rw [binding_eval_environment, binding_effect_environment] at effect
  apply Prod.ext
  · exact LinearMap.congr_fun old word
  · exact LinearMap.congr_fun effect word

theorem prefix_square (runtime : LivingRuntimeState process) (bound : Nat) :
    (prefixEvaluator (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process) runtime bound).comp
      (words process) =
    prefixEvaluator (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process) runtime.tick.next bound := by
  apply LinearMap.ext
  intro word
  funext index
  have exactStage := stage_pair (runtime.advance index.val) word
  change stageInventory (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process)
    (SourceGeneratedRuntimeMaterialStageAt.generate (runtime.advance index.val)) (words process word) =
    stageInventory (R := ℤ) (s := PUnit.unit) (statePoint process) (Field.environment process)
      (SourceGeneratedRuntimeMaterialStageAt.generate (runtime.tick.next.advance index.val)) word
  rw [runtime_tail]
  exact exactStage

end
end SourceOperationNative.Substitution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
