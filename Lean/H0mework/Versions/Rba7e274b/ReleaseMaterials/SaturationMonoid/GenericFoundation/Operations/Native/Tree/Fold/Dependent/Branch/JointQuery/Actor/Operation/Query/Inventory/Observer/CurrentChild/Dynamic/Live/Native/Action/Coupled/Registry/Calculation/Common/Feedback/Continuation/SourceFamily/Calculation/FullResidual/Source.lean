import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullResidualCalculation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace AI
export Lower.SourceFamily.ActualInputCalculation
  (withActualInput actual_value actual_trace actual_base_value updated_base_total cofinal_actual_input cofinal_actual_value successor_born_base successor_feedback_base)
end AI
namespace CF
export Lower.SourceFamily.CalculationFactory (codeAt collapseValue)
end CF
namespace SF
export Lower.SourceFamily (Factory Seed Packet cfg defaultFactory)
end SF
namespace L
export Lower (Value groups)
end L
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence next)
end S
namespace R
export SourceGeneratedInquiryReceiptAction (actionReader actionResultAt actualMaterial)
end R
namespace SS
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor
  (oldPair nativeValue born actual_whole actual_next)
end SS
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input)
end N
variable {Sorts : Type u} {V X : Sorts → Type u} [∀ target, AddCommGroup (V target)] {s : Sorts}

-- The complete actual pair feeds the physical branch and its residual branch separately.
def regroup (target : Sorts) : PairValue (PairValue V) target →+ PairValue (PairValue V) target where
  toFun row := ((row.1.1 + row.2.1, 0), (row.1.2 + row.2.2, 0))
  map_zero' := by simp
  map_add' left right := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, add_zero] <;> abel

def binding (target : Sorts) (name : X target) : Expr (PairValue (PairValue V)) X target :=
  .linear (regroup target) (.var name)

def jointCode (sourceCode : Expr (PairValue V) X s) : Expr (PairValue (PairValue V)) X s :=
  (liftExpr sourceCode).subst binding

def physicalInput (complete : Env (PairValue V) X) : Env (PairValue V) X :=
  fun target name => ((complete target name).1, 0)
def residualInput (complete : Env (PairValue V) X) : Env (PairValue V) X :=
  fun target name => ((complete target name).2, 0)

def completeInput (environment : Env (PairValue (PairValue V)) X) : Env (PairValue V) X :=
  fun target name => (environment target name).1 + (environment target name).2

theorem joint_eval (sourceCode : Expr (PairValue V) X s) (environment : Env (PairValue (PairValue V)) X) :
    (jointCode sourceCode).eval environment =
      (sourceCode.eval (physicalInput (completeInput environment)),
        sourceCode.effect (physicalInput (completeInput environment)) (residualInput (completeInput environment))) := by
  unfold jointCode
  rw [Expr.eval_subst]
  have actual : (fun target name => (binding target name).eval environment) =
      pairEnvironment (physicalInput (completeInput environment)) (residualInput (completeInput environment)) := by
    funext target name
    rfl
  rw [actual]
  exact eval_liftExpr _ _ _

theorem joint_complete (sourceCode : Expr (PairValue V) X s) (environment : Env (PairValue (PairValue V)) X) :
    ((jointCode sourceCode).eval environment).1 +
      ((jointCode sourceCode).eval environment).2 =
        sourceCode.eval (physicalInput (completeInput environment) + residualInput (completeInput environment)) :=
  (congrArg (fun pair : PairValue (PairValue V) s => pair.1 + pair.2)
    (joint_eval sourceCode environment)).trans (Expr.eval_update _ _ _).symm

def factory (sourceCode : Expr (PairValue V) X s) (baseFactory : SF.Factory (PairValue V) X s) :
    SF.Factory (PairValue V) X s := AI.withActualInput (jointCode sourceCode) baseFactory

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullResidualCalculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
