import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Affine.Source
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Phase.Closure
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Psi.Action.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
namespace Lower.SourceFamily.Foresight.Contextual.Phase.Scope
namespace A
export Lower.SourceFamily.Foresight.Contextual.Profile.Assembly
 (BeforeTarget AfterTarget beforeJointModule afterJointModule nextPacket beforeFrame afterFrame beforeIndex afterIndex afterSource)
end A
namespace Af
export Lower.SourceFamily.Foresight.Contextual.Profile.Affine
 (beforeq afterq currentBeta currentr currentTrace writerBoundary writer_rebase actor rebase)
end Af
namespace K
export Lower.SourceFamily.Foresight.Contextual.Profile.Kernel (before_actual_index afterFace afterDisposition)
end K
namespace P
export Lower.SourceFamily.Foresight.Contextual.Profile.Producer (residual joint_scope_semantic)
end P
namespace Ph
export Lower.SourceFamily.Foresight.Contextual.Phase
 (requestWord requestTrace requestWritten complete_paid_in_history full_source_charge all_step_relations)
export Lower.SourceFamily.Foresight.Contextual.Phase.Closed (boundary boundary_closure)
end Ph
namespace Wr
export Lower.SourceFamily.Foresight.Contextual.Written (jointHistory)
end Wr
namespace D
export Lower.SourceFamily.Foresight.Contextual.Forecast.Dispatch (free_evaluation)
end D
namespace J
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint (history)
end J
namespace Psi
export Lower.SourceFamily.Foresight.Contextual.Psi.Closure (next_query_consumes)
namespace Disposition
export Lower.SourceFamily.Foresight.Contextual.Psi.Closure.DispositionProjection (At read)
end Disposition
end Psi
namespace DispositionEffect
export Lower.SourceFamily.Foresight.Contextual.Psi.EffectConsumption.DispositionProjection (At read)
end DispositionEffect
namespace ClosureProjection
variable {Root Generator Carrier:Type u} [AddCommGroup Carrier]
variable {root:RootedAccountedUnfolding Root}
variable {seed:RootedAccountedUnfolding (PresentedRelationEventAt Generator)}
variable {continuation:RootedAccountedUnfolding
 (PresentedRelationEventAt Generator→RootedAccountedUnfolding (PresentedRelationEventAt Generator))}
variable {history:RootGeneratedCofinalHistoryAt root seed continuation}
variable {evaluator:RootedAccountedUnfolding (Generator→Carrier)}
theorem evaluation (face:CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt history evaluator)
 (vector:history.generatorClosure):face.closureEvaluation vector=face.freeEvaluation vector.val :=rfl
end ClosureProjection
section TraceSyntax
variable {T:Type u} {U Y:T→Type u} [∀t,AddCommGroup (U t)] {t:T}
private theorem trace_residual_semantic {environment:Env U Y} {before after:Expr U Y t}
 (trace:Trace environment before after):
 Lower.SourceFamily.Foresight.Contextual.Forecast.Rendering.SemanticEq
  (Finsupp.single (Lower.SourceFamily.Foresight.Contextual.Mixed.residualExpression before after) 1)
  (relationMap (R:=ℤ) environment trace.relationWords) :=by
 intro env
 rw [trace.relation_boundary,map_sub]
 simp only [evaluation,Finsupp.linearCombination_single,one_smul,
  Lower.SourceFamily.Foresight.Contextual.Mixed.residualExpression,Expr.eval,
  AddMonoidHom.neg_apply,AddMonoidHom.id_apply,sub_eq_add_neg]
end TraceSyntax
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat)
variable (packet:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
local instance beforeModule:Module ℤ (A.BeforeTarget binding n packet):=A.beforeJointModule binding n packet
local instance afterModule:Module ℤ (A.AfterTarget binding n packet):=A.afterJointModule binding n packet
abbrev boundary:=Ph.boundary binding n packet
abbrev nextFace:=K.afterFace binding n packet
abbrev nextDisposition:=K.afterDisposition binding n packet
abbrev nextHistory:=J.history (A.nextPacket binding n packet).2 (A.afterFrame binding n packet) (A.afterIndex binding n packet).2
variable (native:packet.1.depth=0)
include native in
theorem phase_word : Ph.requestWord binding n packet=Finsupp.single (Af.currentr binding n packet) (1:ℤ) :=by
 have index:=K.before_actual_index n packet native
 exact congrArg (fun index=>Finsupp.single
  (P.residual binding n packet.2 (A.beforeFrame n packet) index) (1:ℤ)) index
include native in
theorem phase_scope : Af.beforeq binding n packet (Ph.requestWord binding n packet)=
 Af.beforeq binding n packet (Af.currentBeta binding n packet) :=
 (congrArg (Af.beforeq binding n packet) (phase_word binding n packet native)).trans
 (P.joint_scope_semantic binding n packet.2 (A.beforeFrame n packet) (A.beforeIndex n packet) _ _
  (trace_residual_semantic (Af.currentTrace binding n packet)))
theorem same_writer : boundary binding n packet=Af.writerBoundary binding n packet (Ph.requestWord binding n packet) :=rfl
def residualEffect := Af.rebase binding n packet
 (Af.actor binding n packet native (Af.beforeq binding n packet (Af.currentBeta binding n packet)))
include native in
theorem scope_equation : Af.afterq binding n packet (boundary binding n packet)=residualEffect binding n packet native :=
 (congrArg (Af.afterq binding n packet) (same_writer binding n packet)).trans
 ((Af.writer_rebase binding n packet native (Ph.requestWord binding n packet)).trans
  (congrArg (fun point=>Af.rebase binding n packet (Af.actor binding n packet native point))
   (phase_scope binding n packet native)))
theorem actual_relation : boundary binding n packet∈(nextHistory binding n packet).relationClosure :=by
 have index:=K.before_actual_index (n+1) (A.nextPacket binding n packet) rfl
 have same:=congrArg (fun index=>(J.history (A.nextPacket binding n packet).2
  (A.afterFrame binding n packet) index.2).relationClosure) index
 exact Eq.mp (congrArg (fun closure=>boundary binding n packet∈closure) same) (Ph.boundary_closure binding n packet)
def relationVector : (nextHistory binding n packet).generatorClosure :=
 ⟨boundary binding n packet,(nextHistory binding n packet).relationClosure_le_generatorClosure (actual_relation binding n packet)⟩
theorem relationVector_val : (relationVector binding n packet).val=boundary binding n packet :=rfl
include native in
theorem next_relation_value : (nextFace binding n packet).closureEvaluation (relationVector binding n packet)=
 residualEffect binding n packet native :=
 (ClosureProjection.evaluation (nextFace binding n packet) (relationVector binding n packet)).trans
 ((congrArg (nextFace binding n packet).freeEvaluation (relationVector_val binding n packet)).trans
  ((D.free_evaluation (A.nextPacket binding n packet).2 (A.afterFrame binding n packet)
    (A.afterIndex binding n packet).2 (A.afterSource binding n packet) _).trans
   (scope_equation binding n packet native)))
def dispositionRead : Prop:=Psi.Disposition.At (nextFace binding n packet) (boundary binding n packet) (nextDisposition binding n packet)
theorem actual_disposition : dispositionRead binding n packet :=
 Psi.Disposition.read (nextFace binding n packet) (boundary binding n packet)
  (actual_relation binding n packet) (nextDisposition binding n packet)
def effectRead : Prop:=DispositionEffect.At (nextFace binding n packet)
 (residualEffect binding n packet native=0) (nextDisposition binding n packet)
include native in
private theorem sound_effect (sound:GeneratedRelationSoundnessAt (nextFace binding n packet)):
 residualEffect binding n packet native=0 :=
 ((D.free_evaluation (A.nextPacket binding n packet).2 (A.afterFrame binding n packet)
   (A.afterIndex binding n packet).2 (A.afterSource binding n packet) _).trans
  (scope_equation binding n packet native)).symm.trans
 (LinearMap.mem_ker.mp (sound.sound (actual_relation binding n packet)))
include native in
theorem actual_effect_disposition : effectRead binding n packet native :=
 DispositionEffect.read (nextFace binding n packet) (residualEffect binding n packet native=0)
  (sound_effect binding n packet native) (nextDisposition binding n packet)
end Lower.SourceFamily.Foresight.Contextual.Phase.Scope
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
