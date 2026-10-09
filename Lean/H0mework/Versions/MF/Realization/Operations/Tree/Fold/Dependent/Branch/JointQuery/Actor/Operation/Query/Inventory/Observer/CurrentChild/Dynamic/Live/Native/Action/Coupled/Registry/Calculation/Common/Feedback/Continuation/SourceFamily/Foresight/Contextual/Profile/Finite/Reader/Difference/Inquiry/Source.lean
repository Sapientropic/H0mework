import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Finite.Reader.Difference.Source
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Installation.Inquiry

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.PaidDifference.Inquiry
namespace A
export Lower.SourceFamily.Foresight.Contextual.Profile.Assembly (nextPacket)
end A
namespace T
export Lower.SourceFamily.Foresight.Contextual.Profile.Affine (afterq head head_source head_constant after_environment afterEnv)
end T
namespace E
export Lower.SourceFamily.Foresight.Contextual.Effect (actualEnvironment source_environment)
end E
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (baseRoot query datum actualOccurrence query_generated)
end Q
namespace Owned
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (resultAt source_value source_history sourceMaterialAt)
end Owned
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat)
variable (prior:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
abbrev grandPacket:=A.nextPacket binding (n+1) (packet binding n prior)
abbrev currentCfg:=R.cfg binding (n+1+1) (grandPacket binding n prior)
abbrev currentFrame:=(grandPacket binding n prior).1
abbrev sourceRoot:=(Q.baseRoot (currentFrame binding n prior) (currentCfg binding n prior)).toAuthoritativeRoot

def reader {current:RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current
 (currentFrame binding n prior).registered}
 (supplied:SourceOperationInquiry.Context.Installation.Occurrence (currentFrame binding n prior) (current:=current)):
 Owned.Raw (Value:=PairValue (Lower.Value W (n+1+1))) (Var:=X) (sort:=s):=
 ⟨((Q.datum (currentFrame binding n prior) (currentCfg binding n prior)).reader supplied).environment,
  Coefficients.expression (difference binding n prior)⟩

def result:=Owned.resultAt (sourceRoot binding n prior) (reader binding n prior)
 (Q.actualOccurrence (currentFrame binding n prior))

theorem original_query_source:
 (result binding n prior).1.environment=(Q.query (currentFrame binding n prior) (currentCfg binding n prior)).raw.environment:=
 (congrArg (fun germ=>germ.raw.environment) (Q.query_generated (currentFrame binding n prior) (currentCfg binding n prior))).symm

theorem generated_value:(result binding n prior).2.2.1=
 evaluation (R:=ℤ) (result binding n prior).1.environment (difference binding n prior):=
 (Owned.source_value (sourceRoot binding n prior) (reader binding n prior)
  (Q.actualOccurrence (currentFrame binding n prior))).trans (Coefficients.expression_eval _ _)

theorem own_fee:(result binding n prior).2.1.2.length=Coefficients.cost (difference binding n prior):=
 (Owned.source_history (sourceRoot binding n prior) (reader binding n prior)
  (Q.actualOccurrence (currentFrame binding n prior))).trans (Coefficients.expression_remaining _)
theorem source_environment:(result binding n prior).1.environment=
 T.afterEnv binding (n+1) (packet binding n prior):=
 (original_query_source binding n prior).trans
  ((E.source_environment binding (n+1) (packet binding n prior)).symm.trans
   (T.after_environment binding (n+1) (packet binding n prior)).symm)

theorem actual_value:(result binding n prior).2.2.1=(0,sigmaEffect binding n prior):=by
 have full:T.afterq binding (n+1) (packet binding n prior) (difference binding n prior)=
  T.constant binding (n+1) (packet binding n prior) (0,sigmaEffect binding n prior):=
  (scope_constant_difference binding n prior).trans
   (congrArg (T.constant binding (n+1) (packet binding n prior)) (correction_generated binding n prior))
 have source:evaluation (R:=ℤ) (T.afterEnv binding (n+1) (packet binding n prior)) (difference binding n prior)=
  (0,sigmaEffect binding n prior):=
  (T.head_source binding (n+1) (packet binding n prior) (difference binding n prior)).symm.trans
   ((congrArg (T.head binding (n+1) (packet binding n prior)) full).trans
    (T.head_constant binding (n+1) (packet binding n prior) _))
 exact (generated_value binding n prior).trans
  ((congrArg (fun environment=>evaluation (R:=ℤ) environment (difference binding n prior))
    (source_environment binding n prior)).trans source)

namespace C
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry
 (state query resultFace compiles originalCompilationFace original_compilation_preserved authority)
end C
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (answeredState entryAt actualVisit next query_unique)
end Q
namespace Req
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest
 (MaterialAt input expression budget updated_value residual_value relation_boundary action_is_paid)
end Req
end Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.PaidDifference.Inquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
