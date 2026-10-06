import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Faces.Fibre
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Consumer
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! A retained source word generates executable pair syntax from each
original operation and coefficient. No representative is chosen from its
residual quotient and no computed pair is inserted as a constant answer. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarInventoryLift
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
end O

variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}

def coefficient (integer : ℤ) : PhysicalValue sort →+ PhysicalValue sort where
  toFun value := integer • value
  map_zero' := smul_zero integer
  map_add' := smul_add integer

def terms (items : List (Expr PhysicalValue PhysicalVar sort × ℤ)) : Expr PhysicalValue PhysicalVar sort :=
  match items with
  | [] => .const 0
  | (expression, integer) :: rest => .add (.linear (coefficient integer) expression) (terms rest)

theorem terms_eval (items : List (Expr PhysicalValue PhysicalVar sort × ℤ)) (environment : Env PhysicalValue PhysicalVar) :
    (terms items).eval environment = (items.map (fun item => item.2 • item.1.eval environment)).sum := by
  induction items with
  | nil => rfl
  | cons item rest prior =>
      cases item
      simp only [terms, Expr.eval, prior, coefficient, List.map_cons, List.sum_cons]
      rfl

def expression (word : Word (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort)) :
    Expr PhysicalValue PhysicalVar sort :=
  terms (word.support.toList.map (fun term => (term, word term)))

theorem expression_eval (word : Word (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))
    (environment : Env PhysicalValue PhysicalVar) :
    (expression word).eval environment = evaluation (R := ℤ) environment word := by
  classical
  rw [expression, terms_eval, evaluation, Finsupp.linearCombination_apply]
  simp only [List.map_map, Finsupp.sum]
  exact Finset.sum_map_toList _ _

variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)
variable (source : RawSource (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) runtime)

def pairRaw (state : runtime.State) (word : Word (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort)) :
    O.Raw (Value := PairValue PhysicalValue) (Var := PhysicalVar) (sort := sort) :=
  ⟨pairEnvironmentAt runtime source state, liftExpr (expression word)⟩

theorem pair_raw_eval (state : runtime.State)
    (word : Word (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort)) :
    (pairRaw runtime source state word).expression.eval (pairRaw runtime source state word).environment =
      pairInventory runtime source state word := by
  change (liftExpr (expression word)).eval (pairEnvironment (readEnv runtime source state)
    (increment runtime source state)) = _
  rw [eval_liftExpr, expression_eval]
  apply Prod.ext
  · rfl
  · apply add_left_cancel (a := evaluation (R := ℤ) (readEnv runtime source state) word)
    change evaluation (R := ℤ) (readEnv runtime source state) word +
      (expression word).effect (readEnv runtime source state) (increment runtime source state) =
      evaluation (R := ℤ) (readEnv runtime source state) word +
        effectEvaluator (R := ℤ) (readEnv runtime source state) (increment runtime source state) word
    rw [← expression_eval word (readEnv runtime source state), ← Expr.eval_update, expression_eval]
    simpa only [expression_eval, LinearMap.add_apply] using LinearMap.congr_fun (evaluation_update (R := ℤ)
      (readEnv runtime source state) (increment runtime source state)) word

end SourceOperationInquiry.Context.Faces.Execution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
