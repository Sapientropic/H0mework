import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Finite.Reader.Scope
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Phase.Scope.Source

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
namespace Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.Next
namespace R
export Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual
 (event beta)
end R
namespace Sc
export Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.Scope
 (requestWord generated_actor_equation generated_rebase_equation)
end Sc
namespace T
export Lower.SourceFamily.Foresight.Contextual.Profile.Affine
 (beforeq afterq actor rebase constant writerValue writerBoundary)
end T
namespace C
export Lower.SourceFamily.Foresight.Contextual (factory factory_raw reader_source_present)
end C
namespace Wr
export Lower.SourceFamily.Foresight.Contextual.Written
 (jointHistory jointStock receiver paid_in_joint)
end Wr
namespace M
export Lower.SourceFamily.Foresight.Paid (paidTrace sourceEnv)
end M
namespace A
export Lower.SourceFamily.Foresight.Contextual.Profile.Assembly
 (nextPacket afterFrame afterIndex afterSource)
end A
namespace K
export Lower.SourceFamily.Foresight.Contextual.Profile.Kernel (afterFace afterDisposition before_actual_index)
end K
namespace P
export Lower.SourceFamily.Foresight.Contextual.Profile.Producer (query raw)
end P
namespace D
export Lower.SourceFamily.Foresight.Contextual.Forecast.Dispatch (free_evaluation queryRaw)
end D
namespace J
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint (history)
end J
namespace Projection
export Lower.SourceFamily.Foresight.Contextual.Phase.Scope.ClosureProjection (evaluation)
end Projection
namespace Disposition
export Lower.SourceFamily.Foresight.Contextual.Psi.Closure.DispositionProjection (At read)
end Disposition
namespace DispositionEffect
export Lower.SourceFamily.Foresight.Contextual.Psi.EffectConsumption.DispositionProjection (At read)
end DispositionEffect
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat)
variable (data:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)

def boundary:=T.writerBoundary binding n data (Sc.requestWord binding n data)

theorem boundary_in_next:boundary binding n data∈(Wr.jointHistory binding n data).relationClosure:=by
 let origin:=RootedAccountedUnfolding.zero PUnit.unit
 have seen:=SourceOperationPaidRelations.boundary_in_inventory origin
  (M.paidTrace binding n data s (Sc.requestWord binding n data))
 exact SourceOperationPaidRelations.relations_next origin
  (SourceOperationPaidRelations.exposure (M.paidTrace binding n data s (Sc.requestWord binding n data)))
  (RootedAccountedUnfolding.zero (Q.actualOccurrence (Wr.receiver binding n data))) (Wr.jointStock binding n data)
  (fun entry paid=>Wr.paid_in_joint binding n data (R.event binding n data)
   (C.reader_source_present binding n data) entry paid) seen

abbrev nextHistory:=J.history (A.nextPacket binding n data).2 (A.afterFrame binding n data) (A.afterIndex binding n data).2

theorem actual_relation:boundary binding n data∈(nextHistory binding n data).relationClosure:=by
 have index:=K.before_actual_index (n+1) (A.nextPacket binding n data) rfl
 have same:=congrArg (fun index=>(J.history (A.nextPacket binding n data).2
  (A.afterFrame binding n data) index.2).relationClosure) index
 exact Eq.mp (congrArg (fun closure=>boundary binding n data∈closure) same) (boundary_in_next binding n data)

def vector:(nextHistory binding n data).generatorClosure:=
 ⟨boundary binding n data,(nextHistory binding n data).relationClosure_le_generatorClosure
  (actual_relation binding n data)⟩
theorem vector_val:(vector binding n data).val=boundary binding n data:=rfl
theorem vector_relation:vector binding n data∈(nextHistory binding n data).relationInGeneratorClosure:=
 actual_relation binding n data

variable (native:data.1.depth=0)
include native in
theorem actual_actor_value:(K.afterFace binding n data).closureEvaluation (vector binding n data)=
 T.actor binding n data native (T.beforeq binding n data (R.beta binding n data))-
 T.constant binding n data (T.writerValue binding n data (Sc.requestWord binding n data)):=
 (Projection.evaluation (K.afterFace binding n data) (vector binding n data)).trans
 ((congrArg (K.afterFace binding n data).freeEvaluation (vector_val binding n data)).trans
  ((D.free_evaluation (A.nextPacket binding n data).2 (A.afterFrame binding n data)
    (A.afterIndex binding n data).2 (A.afterSource binding n data) (boundary binding n data)).trans
   (Sc.generated_actor_equation binding n data native)))
include native in
theorem actual_rebase_value:(K.afterFace binding n data).closureEvaluation (vector binding n data)=
 T.rebase binding n data (T.actor binding n data native (T.beforeq binding n data (R.beta binding n data))):=
 (Projection.evaluation (K.afterFace binding n data) (vector binding n data)).trans
 ((congrArg (K.afterFace binding n data).freeEvaluation (vector_val binding n data)).trans
  ((D.free_evaluation (A.nextPacket binding n data).2 (A.afterFrame binding n data)
    (A.afterIndex binding n data).2 (A.afterSource binding n data) (boundary binding n data)).trans
   (Sc.generated_rebase_equation binding n data native)))

def dispositionRead:Prop:=Disposition.At (K.afterFace binding n data) (boundary binding n data)
 (K.afterDisposition binding n data)
theorem actual_disposition:dispositionRead binding n data:=
 Disposition.read (K.afterFace binding n data) (boundary binding n data)
  (actual_relation binding n data) (K.afterDisposition binding n data)

def effect:=T.rebase binding n data
 (T.actor binding n data native (T.beforeq binding n data (R.beta binding n data)))
def effectRead:Prop:=DispositionEffect.At (K.afterFace binding n data)
 (effect binding n data native=0) (K.afterDisposition binding n data)
include native in
private theorem sound_effect_zero (sound:GeneratedRelationSoundnessAt (K.afterFace binding n data)):
 effect binding n data native=0:=
 ((D.free_evaluation (A.nextPacket binding n data).2 (A.afterFrame binding n data)
   (A.afterIndex binding n data).2 (A.afterSource binding n data) (boundary binding n data)).trans
  (Sc.generated_rebase_equation binding n data native)).symm.trans
 (LinearMap.mem_ker.mp (sound.sound (actual_relation binding n data)))
include native in
theorem actual_disposition_effect:effectRead binding n data native:=
 DispositionEffect.read (K.afterFace binding n data) (effect binding n data native=0)
  (sound_effect_zero binding n data native) (K.afterDisposition binding n data)

theorem actual_next_reader:
 (Q.query (A.nextPacket binding n data).1
  (Lower.SourceFamily.cfg (C.factory (s:=s) binding) (n+1) (A.nextPacket binding n data).2)).raw=
 P.raw binding (n+1) (A.nextPacket binding n data).2 (A.afterFrame binding n data) (A.afterIndex binding n data):=
 (C.factory_raw binding (n+1) (A.nextPacket binding n data).2 (A.nextPacket binding n data).1).trans
 (congrArg (P.raw binding (n+1) (A.nextPacket binding n data).2 (A.afterFrame binding n data))
  (Lower.SourceFamily.Foresight.Installed.native_actual_index (n+1) (A.nextPacket binding n data).1 rfl))

theorem actual_next_inner_query:
 P.query binding (n+1) (A.nextPacket binding n data).2 (A.afterFrame binding n data) (A.afterIndex binding n data)=
 D.queryRaw (A.nextPacket binding n data).2 (A.afterFrame binding n data) (A.afterIndex binding n data).2
  (Lower.SourceFamily.Foresight.Contextual.Reader.Core.raw binding (n+1) (A.nextPacket binding n data).2
   (A.afterFrame binding n data) (A.afterIndex binding n data))
  (A.afterSource binding n data) (K.afterDisposition binding n data):=rfl
end Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.Next
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
