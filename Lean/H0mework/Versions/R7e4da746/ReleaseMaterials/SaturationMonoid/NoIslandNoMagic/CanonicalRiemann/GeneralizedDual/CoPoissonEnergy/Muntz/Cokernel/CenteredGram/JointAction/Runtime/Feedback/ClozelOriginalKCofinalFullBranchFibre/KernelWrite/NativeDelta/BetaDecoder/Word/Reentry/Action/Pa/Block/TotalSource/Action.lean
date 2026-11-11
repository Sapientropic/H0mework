import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNativeSourceReturn.Kernel
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Action
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState
namespace Two
export CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalTwoDirection
 (actionCode action_code_directions directions sourceShift totalBranches pairTotal)
end Two
namespace Ret
export CenteredGram.IntegralGraphJointAction.OriginalKNativeSourceReturn
 (returnDirectionRead pairedPacking)
end Ret
namespace P
export CenteredGram.IntegralGraphJointAction.OriginalKCombPhysicalAction (R)
end P
namespace F
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction
 (BaseValue sourceRaw sourceEnvironment pairEnvironmentAt)
namespace C
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.C (Value Var)
end C
end F
namespace Operand
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa (CodeValue bodyAt)
end Operand
namespace DR
export CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialResidualAction
 (completeRSourceRead sourceCollapseHom source_collapse_actual)
namespace L
export CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialResidualAction.L (Value groups)
end L
end DR
namespace CF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory
 (codeAt code_base_value collapseValue)
end CF
abbrev Branches := PairValue (PairValue F.C.Value) ()
namespace Split
abbrev totalTwo : Branches →+ BurnolL2 :=
 Two.pairTotal.toLinearMap.toAddMonoidHom.comp ((AddMonoidHom.fst _ _)+(AddMonoidHom.snd _ _))
end Split

theorem total_actual (value : Branches) : Split.totalTwo value = Two.totalBranches value := by
 change (value.1.1+value.2.1)+(value.1.2+value.2.2)=(value.1.1+value.1.2)+(value.2.1+value.2.2)
 abel

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)

def sourceAction : Branches →+ Branches :=
 Ret.pairedPacking.toLinearMap.toAddMonoidHom.comp
  ((P.R observation nontrivial half).toLinearMap.toAddMonoidHom.comp Split.totalTwo)

/-- This existing actor reads both original source directions before their inverse unitary return. -/
def sourceCode : Expr (PairValue (PairValue F.C.Value)) F.C.Var () :=
 .linear Ret.returnDirectionRead.toLinearMap.toAddMonoidHom (Two.actionCode observation nontrivial half)

theorem source_code_read (environment : Env (PairValue (PairValue F.C.Value)) F.C.Var) :
 (sourceCode observation nontrivial half).eval environment = sourceAction observation nontrivial half (environment () ()) := by
 change ((burnolMultiplicativeDilation (-Two.sourceShift)
   (Two.directions ((Two.actionCode observation nontrivial half).eval environment)).1,
  fourierL2 (burnolMultiplicativeDilation Two.sourceShift
   (Two.directions ((Two.actionCode observation nontrivial half).eval environment)).2)),0)=_
 rw [Two.action_code_directions]
 simp only [burnolMultiplicativeDilation_add,neg_add_cancel,add_neg_cancel,burnolMultiplicativeDilation_zero]
 change Ret.pairedPacking (P.R observation nontrivial half (Two.totalBranches (environment () ()))) =
  Ret.pairedPacking (P.R observation nontrivial half (Split.totalTwo (environment () ())))
 rw [total_actual]

local instance baseGroups (n : Nat) : ∀ t,AddCommGroup (F.BaseValue n t) := DR.L.groups (PairValue F.C.Value) n
local instance originGroups (n : Nat) : ∀ t,AddCommGroup (DR.L.Value (F.BaseValue n) 2 t) := DR.L.groups (F.BaseValue n) 2
local instance runtimeGroups (n : Nat) : ∀ t,AddCommGroup
 (DR.L.Value (DR.L.Value (F.BaseValue n) 2) 0 t) := DR.L.groups (DR.L.Value (F.BaseValue n) 2) 0
local instance codeGroups (n : Nat) : ∀ t,AddCommGroup (Operand.CodeValue n t) := DR.L.groups (F.BaseValue n) 3
variable (initial : Nat)

def gradedCode : Expr (Operand.CodeValue initial) F.C.Var () :=
 CF.codeAt (CF.codeAt (sourceCode observation nontrivial half) initial) 2

theorem graded_read (environment : Env (Operand.CodeValue initial) F.C.Var) :
 DR.completeRSourceRead initial 2 0 ((gradedCode observation nontrivial half initial).eval environment) =
 sourceAction observation nontrivial half (DR.completeRSourceRead initial 2 0 (environment () ())) := by
 change DR.sourceCollapseHom initial (DR.sourceCollapseHom 2 ((gradedCode observation nontrivial half initial).eval environment)) =
  sourceAction observation nontrivial half (DR.sourceCollapseHom initial (DR.sourceCollapseHom 2 (environment () ())))
 rw [DR.source_collapse_actual,DR.source_collapse_actual,DR.source_collapse_actual,DR.source_collapse_actual]
 unfold gradedCode
 rw [CF.code_base_value,CF.code_base_value,source_code_read]

variable (raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value := PairValue (PairValue (F.BaseValue initial))) (Var := F.C.Var) (sort := ()))

def binding (target : Unit) (_name : F.C.Var target) : Expr (Operand.CodeValue initial) F.C.Var target := by
 cases target
 exact Operand.bodyAt initial raw

def code : Expr (Operand.CodeValue initial) F.C.Var () :=
 (gradedCode observation nontrivial half initial).subst (binding initial raw)

theorem code_read (environment : Env (Operand.CodeValue initial) F.C.Var) :
 DR.completeRSourceRead initial 2 0 ((code observation nontrivial half initial raw).eval environment) =
 sourceAction observation nontrivial half (DR.completeRSourceRead initial 2 0 ((Operand.bodyAt initial raw).eval environment)) := by
 unfold code
 rw [Expr.eval_subst]
 exact graded_read observation nontrivial half initial _

theorem code_effect (environment increment : Env (Operand.CodeValue initial) F.C.Var) :
 DR.completeRSourceRead initial 2 0 ((code observation nontrivial half initial raw).effect environment increment) =
 sourceAction observation nontrivial half (DR.completeRSourceRead initial 2 0 ((Operand.bodyAt initial raw).effect environment increment)) := by
 have update := congrArg (DR.completeRSourceRead initial 2 0)
  (Expr.eval_update (code observation nontrivial half initial raw) environment increment)
 rw [map_add,code_read,code_read,Expr.eval_update,map_add,map_add] at update
 exact add_left_cancel update.symm

theorem body_updated (nextEnvironment : Env (PairValue (PairValue (F.BaseValue initial))) F.C.Var) :
 (Operand.bodyAt initial raw).eval (pairEnvironment raw.environment (nextEnvironment-raw.environment)) =
 (raw.expression.eval nextEnvironment,0) := by
 change (((liftExpr raw.expression).eval (pairEnvironment raw.environment (nextEnvironment-raw.environment))).1+
  ((liftExpr raw.expression).eval (pairEnvironment raw.environment (nextEnvironment-raw.environment))).2,0)=_
 rw [eval_liftExpr]
 have actual := (Expr.eval_update raw.expression raw.environment (nextEnvironment-raw.environment)).symm
 rw [add_sub_cancel] at actual
 exact congrArg (fun value => (value,0)) actual

/-- Full four-branch physical addition is upstream of the original R actor. -/
theorem full_source_action (nextEnvironment : Env (PairValue (PairValue (F.BaseValue initial))) F.C.Var) :
 DR.completeRSourceRead initial 2 0 ((code observation nontrivial half initial raw).eval
  (pairEnvironment raw.environment (nextEnvironment-raw.environment))) =
 Ret.pairedPacking (P.R observation nontrivial half (Two.totalBranches
  (DR.completeRSourceRead initial 2 0 (raw.expression.eval nextEnvironment,0)))) := by
 rw [code_read,body_updated]
 change Ret.pairedPacking (P.R observation nontrivial half (Split.totalTwo _)) = _
 rw [total_actual]

end SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
