import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Kernel
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Phase.Written
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Effect
import H0mework.Realization.Operations.Execution.Relations.History.Monotone
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Profile.Affine
namespace A
export Lower.SourceFamily.Foresight.Contextual.Profile.Assembly
 (nextPacket beforeFrame afterFrame beforeIndex afterIndex beforeState afterState BeforeTarget AfterTarget beforeSource afterSource)
end A
namespace G
export Lower.SourceFamily.Foresight.Contextual.Profile.Generated (sourceMorphism source_scope_action)
end G
namespace P
export Lower.SourceFamily.Foresight.Contextual.Profile.Producer
 (nativeCursor sigma pair source_fibre profile_head jointSource joint_scope_renderer query queryResult queryTrace residual beta feedback raw actionBinding sourceTarget sourceRestriction rawOldSource joint_semantic joint_scope_semantic raw_scope scopeOperator)
end P
namespace R
export Lower.SourceFamily.Foresight.Contextual.Forecast.Rendering (SemanticEq semantic_advance)
end R
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (query actualOccurrence base)
end Q
namespace C
export Lower.SourceFamily.Foresight.Contextual
 (factory baseFactory factory_raw sourceTree priorSourceTree prior_source_preserved)
end C
namespace Wr
export Lower.SourceFamily.Foresight.Contextual.Written
 (stock receiver jointStock jointHistory stock_in_joint paid_in_joint action_written_in_stock)
end Wr
namespace M
export Lower.SourceFamily.Foresight.Paid (expression result paidTrace sourceEnv)
end M
section Syntax
variable {S:Type u} {U X:S→Type u} [∀t,AddCommGroup (U t)] {s:S}
variable {old:Env U X} {before after:Expr U X s}
private theorem trace_residual_semantic (trace:Trace old before after):
 R.SemanticEq (Finsupp.single (Lower.SourceFamily.Foresight.Contextual.Mixed.residualExpression before after) 1)
  (relationMap (R:=ℤ) old (trace.relationWords (R:=ℤ))) :=by
 intro env
 rw [trace.relation_boundary,map_sub]
 simp only [evaluation,Finsupp.linearCombination_single,one_smul,
  Lower.SourceFamily.Foresight.Contextual.Mixed.residualExpression,Expr.eval,
  AddMonoidHom.neg_apply,AddMonoidHom.id_apply,sub_eq_add_neg]
private theorem trace_raw_semantic (trace:Trace old before after) (binding:∀t,X t→Expr U X t):
 R.SemanticEq
 (Finsupp.single (Expr.add (Lower.SourceFamily.Foresight.Contextual.Mixed.residualExpression before after)
  ((Lower.SourceFamily.Foresight.Contextual.Mixed.residualExpression before after).subst binding)) 1)
 (relationMap (R:=ℤ) old (trace.relationWords (R:=ℤ))+
  substitution (R:=ℤ) binding (relationMap (R:=ℤ) old (trace.relationWords (R:=ℤ)))) :=by
 intro env
 have left:=trace_residual_semantic trace env
 have right:=trace_residual_semantic trace (SourceSubstitution.sourceEnvironment binding env)
 simp only [evaluation,Finsupp.linearCombination_single,one_smul] at left right
 simp only [evaluation,Finsupp.linearCombination_single,one_smul,Expr.eval]
 rw [map_add,Expr.eval_subst]
 exact congrArg₂ (·+·) left (right.trans
  (LinearMap.congr_fun (evaluation_substitution (R:=ℤ) binding env)
   (relationMap (R:=ℤ) old (trace.relationWords (R:=ℤ)))).symm)
end Syntax
section Generic
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat)
local instance nativeModule (seed:Lower.SourceFamily.Seed W X s n) (frame:M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s)) :
 Module ℤ (Lower.SourceFamily.Foresight.Model binding (Lower.SourceFamily.Foresight.Installed.nativeState n seed frame) s 0) :=
 (SourceGeneratedScalarCharacterExact.Carrier ℤ (Lower.SourceFamily.Foresight.completion binding
  (Lower.SourceFamily.Foresight.Installed.nativeState n seed frame) s 0)).module
variable (seed:Lower.SourceFamily.Seed W X s n) (frame:M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s))
variable (index:Lower.SourceFamily.Foresight.Installed.OccurrenceIndex n frame)
local instance jointModule:Module ℤ (P.sourceTarget binding n seed frame index):=Submodule.Quotient.module _
 private theorem joint_semantic (left right:Formal ℤ (PairValue (Lower.Value W n)) X s) (same:R.SemanticEq left right):
 P.jointSource binding n seed frame index left=P.jointSource binding n seed frame index right :=
 P.joint_semantic binding n seed frame index left right same
private theorem joint_scope_semantic (left right:Formal ℤ (PairValue (Lower.Value W n)) X s) (same:R.SemanticEq left right):
 SourceOperationLogic.q (P.jointSource binding n seed frame index) left=
 SourceOperationLogic.q (P.jointSource binding n seed frame index) right :=by
 apply (SourceOperationLogic.q_eq_iff _ _ _).mpr
 rw [LinearMap.mem_ker,map_sub]
 exact sub_eq_zero.mpr (joint_semantic binding n seed frame index left right same)
private theorem source_const_add (left right:PairValue (Lower.Value W n) s):
 SourceOperationLogic.q (P.jointSource binding n seed frame index) (Finsupp.single (.const (left+right)) 1)=
 SourceOperationLogic.q (P.jointSource binding n seed frame index) (Finsupp.single (.const left) 1)+
 SourceOperationLogic.q (P.jointSource binding n seed frame index) (Finsupp.single (.const right) 1) :=by
 rw [←map_add]
 exact joint_scope_semantic binding n seed frame index _ _
  (fun env=>by simp only [map_add,evaluation,Finsupp.linearCombination_single,one_smul,Expr.eval])
private theorem source_const_smul (scalar:ℤ) (value:PairValue (Lower.Value W n) s):
 SourceOperationLogic.q (P.jointSource binding n seed frame index) (Finsupp.single (.const (scalar • value)) 1)=
 scalar • SourceOperationLogic.q (P.jointSource binding n seed frame index) (Finsupp.single (.const value) 1) :=by
 rw [←map_smul]
 exact joint_scope_semantic binding n seed frame index _ _
  (fun env=>by simp only [map_smul,evaluation,Finsupp.linearCombination_single,one_smul,Expr.eval])
end Generic
section ActualPacket
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat) (packet:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
local instance beforeNativeModule : Module ℤ (Lower.SourceFamily.Foresight.Model binding (A.beforeState n packet) s 0) :=
 (SourceGeneratedScalarCharacterExact.Carrier ℤ (Lower.SourceFamily.Foresight.completion binding (A.beforeState n packet) s 0)).module
local instance afterNativeModule : Module ℤ (Lower.SourceFamily.Foresight.Model binding (A.afterState binding n packet) s 0) :=
 (SourceGeneratedScalarCharacterExact.Carrier ℤ (Lower.SourceFamily.Foresight.completion binding (A.afterState binding n packet) s 0)).module
local instance beforeJointModule :Module ℤ (A.BeforeTarget binding n packet):=
 Lower.SourceFamily.Foresight.Contextual.Profile.Assembly.beforeJointModule binding n packet
local instance afterJointModule :Module ℤ (A.AfterTarget binding n packet):=
 Lower.SourceFamily.Foresight.Contextual.Profile.Assembly.afterJointModule binding n packet
abbrev BeforeScope:=SourceOperationLogic.Scope (A.beforeSource binding n packet)
abbrev AfterScope:=SourceOperationLogic.Scope (A.afterSource binding n packet)
abbrev beforeq:=SourceOperationLogic.q (A.beforeSource binding n packet)
abbrev afterq:=SourceOperationLogic.q (A.afterSource binding n packet)
abbrev currentQuery:=P.query binding n packet.2 (A.beforeFrame n packet) (A.beforeIndex n packet)
abbrev currentResult:=P.queryResult binding n packet.2 (A.beforeFrame n packet) (A.beforeIndex n packet)
abbrev currentTrace:=P.queryTrace binding n packet.2 (A.beforeFrame n packet) (A.beforeIndex n packet)
abbrev currentBeta:=P.beta binding n packet.2 (A.beforeFrame n packet) (A.beforeIndex n packet)
abbrev currentr:=P.residual binding n packet.2 (A.beforeFrame n packet) (A.beforeIndex n packet)
def queryWord:=Finsupp.single (currentQuery binding n packet).expression (1:ℤ)
def endpointWord:=Finsupp.single (currentResult binding n packet).2.1.1 (1:ℤ)
abbrev substitutedBeta:=substitution (R:=ℤ) (P.actionBinding binding n) (currentBeta binding n packet)
theorem boundary_words:currentBeta binding n packet=queryWord binding n packet-endpointWord binding n packet :=
 (currentTrace binding n packet).relation_boundary (R:=ℤ)
theorem query_affine:beforeq binding n packet (currentBeta binding n packet)=
 beforeq binding n packet (queryWord binding n packet)-beforeq binding n packet (endpointWord binding n packet) :=
 (congrArg (beforeq binding n packet) (boundary_words binding n packet)).trans (map_sub _ _ _)
private theorem residual_semantic:R.SemanticEq (Finsupp.single (currentr binding n packet) 1) (currentBeta binding n packet) :=by
 intro env
 rw [boundary_words,map_sub]
 simp only [queryWord,endpointWord,currentr,P.residual,evaluation,Finsupp.linearCombination_single,one_smul,
  Expr.eval,AddMonoidHom.neg_apply,AddMonoidHom.id_apply,sub_eq_add_neg]
private theorem raw_semantic :R.SemanticEq
 (Finsupp.single (P.raw binding n packet.2 (A.beforeFrame n packet) (A.beforeIndex n packet)).expression 1)
 (currentBeta binding n packet+substitutedBeta binding n packet) :=
 trace_raw_semantic (currentTrace binding n packet) (P.actionBinding binding n)

variable (native:packet.1.depth=0)
def actor:=inducedResidualMap (G.sourceMorphism binding n packet native)
include native in
theorem boundary_action : afterq binding n packet (liftMap (currentBeta binding n packet))=
 actor binding n packet native (beforeq binding n packet (queryWord binding n packet))-
 actor binding n packet native (beforeq binding n packet (endpointWord binding n packet)) :=by
 exact (G.source_scope_action binding n packet native _).symm.trans
  ((congrArg (actor binding n packet native) (query_affine binding n packet)).trans (map_sub _ _ _))

def rawWord:=Finsupp.single (Q.query packet.1
 (Lower.SourceFamily.cfg (C.factory (s:=s) binding) n packet.2)).raw.expression (1:ℤ)
def rootEvent:Lower.SourceFamily.Foresight.Paid.Ledger.SourceEvent (W:=W) (X:=X) (s:=s) n:=
 .generator (Q.query packet.1 (Lower.SourceFamily.cfg (C.factory (s:=s) binding) n packet.2)).raw.expression
include native in
private theorem raw_owned:
 (Q.query packet.1 (Lower.SourceFamily.cfg (C.factory (s:=s) binding) n packet.2)).raw=
 P.raw binding n packet.2 (A.beforeFrame n packet) (A.beforeIndex n packet) :=
 (C.factory_raw binding n packet.2 packet.1).trans
 (congrArg (P.raw binding n packet.2 (A.beforeFrame n packet))
  (Lower.SourceFamily.Foresight.Contextual.Profile.Kernel.before_actual_index n packet native))
include native in
theorem raw_scope:
 beforeq binding n packet (rawWord binding n packet)=beforeq binding n packet (currentBeta binding n packet)+
 beforeq binding n packet (substitutedBeta binding n packet) :=by
 have own:=congrArg (fun raw=>Finsupp.single raw.expression (1:ℤ)) (raw_owned binding n packet native)
 apply (congrArg (beforeq binding n packet) own).trans
 have generated:=P.raw_scope binding n packet.2 (A.beforeFrame n packet) (A.beforeIndex n packet)
 have acted:=Lower.SourceFamily.Foresight.Contextual.Profile.BindingSource.scope_source binding n packet.2
  (A.beforeFrame n packet) (A.beforeIndex n packet) (currentBeta binding n packet)
 exact generated.trans (congrArg (fun value=>beforeq binding n packet (currentBeta binding n packet)+value) acted)

theorem root_present :rootEvent binding n packet∈(C.sourceTree binding n packet).trace :=
 C.prior_source_preserved binding n packet _ (Lower.SourceFamily.Foresight.Paid.Ledger.source_at_root n packet _)

def afterEnv:=P.pair (P.sigma binding (n+1))
 (P.nativeCursor (n+1) (A.afterFrame binding n packet) (A.afterIndex binding n packet))
private theorem head_kernel : LinearMap.ker (A.afterSource binding n packet) ≤
 LinearMap.ker (evaluation (R:=ℤ) (s:=s) (afterEnv binding n packet)) :=by
 intro word present
 have joint: A.afterSource binding n packet word=A.afterSource binding n packet 0 :=
  (LinearMap.mem_ker.mp present).trans (map_zero _).symm
 have restricted:=congrArg
  (P.sourceRestriction binding (n+1) (A.nextPacket binding n packet).2
   (A.afterFrame binding n packet) (A.afterIndex binding n packet)) joint
 have original:=
  (Lower.SourceFamily.Foresight.Contextual.Profile.BindingSource.empty_restriction binding (n+1)
   (A.nextPacket binding n packet).2 (A.afterFrame binding n packet) (A.afterIndex binding n packet) word).symm.trans
   (restricted.trans
    (Lower.SourceFamily.Foresight.Contextual.Profile.BindingSource.empty_restriction binding (n+1)
     (A.nextPacket binding n packet).2 (A.afterFrame binding n packet) (A.afterIndex binding n packet) 0))
 have profile:=congrArg Prod.fst original
 have all:=(P.source_fibre (P.sigma binding (n+1))
  (P.nativeCursor (n+1) (A.afterFrame binding n packet) (A.afterIndex binding n packet)) word 0).mp profile
 exact (all 0).trans (map_zero _)
def head:AfterScope binding n packet→ₗ[ℤ]PairValue (Lower.Value W (n+1)) s:=
 (LinearMap.ker (A.afterSource binding n packet)).liftQ
 (evaluation (R:=ℤ) (afterEnv binding n packet)) (head_kernel binding n packet)
theorem head_source (word:Formal ℤ (PairValue (Lower.Value W (n+1))) X s):
 head binding n packet (afterq binding n packet word)=evaluation (R:=ℤ) (afterEnv binding n packet) word:=rfl

def constant:PairValue (Lower.Value W (n+1)) s→ₗ[ℤ]AfterScope binding n packet where
 toFun value:=afterq binding n packet (Finsupp.single (.const value) 1)
 map_add' left right:=source_const_add binding (n+1) (A.nextPacket binding n packet).2
  (A.afterFrame binding n packet) (A.afterIndex binding n packet) left right
 map_smul' scalar value:=source_const_smul binding (n+1) (A.nextPacket binding n packet).2
  (A.afterFrame binding n packet) (A.afterIndex binding n packet) scalar value
theorem head_constant (value:PairValue (Lower.Value W (n+1)) s):
 head binding n packet (constant binding n packet value)=value :=by
 change head binding n packet (afterq binding n packet (Finsupp.single (.const value) 1))=value
 rw [head_source]
 simp only [evaluation,Finsupp.linearCombination_single,one_smul,Expr.eval]
def rebase:AfterScope binding n packet→ₗ[ℤ]AfterScope binding n packet:=
 LinearMap.id-(constant binding n packet).comp (head binding n packet)

def writerEndpoint (word:Formal ℤ (PairValue (Lower.Value W n)) X s):=
 (M.result binding n packet s word).2.1.1
def writerValue (word:Formal ℤ (PairValue (Lower.Value W n)) X s):=(M.result binding n packet s word).2.2.1
def writerBoundary (word:Formal ℤ (PairValue (Lower.Value W n)) X s):=
 relationMap (R:=ℤ) (M.sourceEnv binding n packet) ((M.paidTrace binding n packet s word).relationWords (R:=ℤ))
theorem writer_endpoint (word:Formal ℤ (PairValue (Lower.Value W n)) X s):
 writerEndpoint binding n packet word=.const (writerValue binding n packet word) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.target_expression _ _ _

theorem after_environment : afterEnv binding n packet=M.sourceEnv binding n packet :=by
 have actual:=Lower.SourceFamily.Foresight.Installed.native_actual_index (n+1) (A.nextPacket binding n packet).1 rfl
 have current:=(P.profile_head binding (n+1) (A.nextPacket binding n packet).2
  (A.afterFrame binding n packet) (A.afterIndex binding n packet))
 have source:=C.factory_raw binding (n+1) (A.nextPacket binding n packet).2 (A.nextPacket binding n packet).1
 have full:=congrArg (fun raw=>raw.environment) source
 exact current.trans
  ((congrArg (fun idx=>(P.raw binding (n+1) (A.nextPacket binding n packet).2
   (A.afterFrame binding n packet) idx).environment) actual.symm).trans
   (full.symm.trans (Lower.SourceFamily.Foresight.Contextual.Effect.source_environment binding n packet).symm))

include native in
theorem writer_affine (word:Formal ℤ (PairValue (Lower.Value W n)) X s):
 afterq binding n packet (writerBoundary binding n packet word)=
 actor binding n packet native (beforeq binding n packet word)-
 constant binding n packet (writerValue binding n packet word) :=by
 have source:=(M.paidTrace binding n packet s word).relation_boundary (R:=ℤ)
 change writerBoundary binding n packet word=
  Finsupp.single (M.result binding n packet s word).1.expression 1-
  Finsupp.single (writerEndpoint binding n packet word) 1 at source
 have boundary:afterq binding n packet (writerBoundary binding n packet word)=
  afterq binding n packet (Finsupp.single (M.result binding n packet s word).1.expression 1)-
  afterq binding n packet (Finsupp.single (writerEndpoint binding n packet word) 1) :=
  (congrArg (afterq binding n packet) source).trans (map_sub _ _ _)
 apply boundary.trans
 apply congrArg₂ (·-·)
 · have rendered:=P.joint_scope_renderer binding (n+1) (A.nextPacket binding n packet).2
    (A.afterFrame binding n packet) (A.afterIndex binding n packet) (liftMap word)
   exact rendered.trans (G.source_scope_action binding n packet native word).symm
 · exact congrArg (fun endpoint:Expr (PairValue (Lower.Value W (n+1))) X s=>
    afterq binding n packet (Finsupp.single endpoint 1)) (writer_endpoint binding n packet word)

theorem writer_head (word:Formal ℤ (PairValue (Lower.Value W n)) X s):
 head binding n packet (afterq binding n packet (liftMap word))=writerValue binding n packet word :=by
 rw [head_source]
 have environment:afterEnv binding n packet=Lower.SourceFamily.Foresight.Contextual.Effect.actualEnvironment binding n packet:=
  (after_environment binding n packet).trans (Lower.SourceFamily.Foresight.Contextual.Effect.source_environment binding n packet)
 exact (congrArg (fun env=>evaluation (R:=ℤ) env (liftMap word)) environment).trans
  (Lower.SourceFamily.Foresight.Contextual.Effect.actual_paid_value binding n packet s word).symm
include native in
theorem writer_rebase (word:Formal ℤ (PairValue (Lower.Value W n)) X s):
 afterq binding n packet (writerBoundary binding n packet word)=
 rebase binding n packet (actor binding n packet native (beforeq binding n packet word)) :=by
 apply (writer_affine binding n packet native word).trans
 change _=_-(constant binding n packet) (head binding n packet (actor binding n packet native (beforeq binding n packet word)))
 have value:head binding n packet (actor binding n packet native (beforeq binding n packet word))=writerValue binding n packet word:=
  (congrArg (head binding n packet) (G.source_scope_action binding n packet native word)).trans (writer_head binding n packet word)
 exact congrArg (fun value=>actor binding n packet native (beforeq binding n packet word)-(constant binding n packet) value) value.symm

include native in
theorem raw_writer_action:
 afterq binding n packet (writerBoundary binding n packet (rawWord binding n packet))=
 rebase binding n packet (actor binding n packet native (beforeq binding n packet (currentBeta binding n packet)+
  beforeq binding n packet (substitutedBeta binding n packet))) :=
 (writer_rebase binding n packet native _).trans
 (congrArg (fun point=>rebase binding n packet (actor binding n packet native point)) (raw_scope binding n packet native))

theorem all_writer_steps_in_stock (event)
 (paid:event∈(SourceOperationPaidRelations.exposure (M.paidTrace binding n packet s (rawWord binding n packet))).trace):
 event∈(Wr.stock binding n packet).trace :=
 Lower.SourceFamily.Foresight.Contextual.Written.paid_in_stock binding n packet
  (rootEvent binding n packet) (root_present binding n packet) event paid

theorem raw_boundary_in_next:
 writerBoundary binding n packet (rawWord binding n packet)∈(Wr.jointHistory binding n packet).relationClosure :=by
 let origin:=RootedAccountedUnfolding.zero PUnit.unit
 have seen:=SourceOperationPaidRelations.boundary_in_inventory origin
  (M.paidTrace binding n packet s (rawWord binding n packet))
 exact SourceOperationPaidRelations.relations_next origin
  (SourceOperationPaidRelations.exposure (M.paidTrace binding n packet s (rawWord binding n packet)))
  (RootedAccountedUnfolding.zero (Q.actualOccurrence (Wr.receiver binding n packet))) (Wr.jointStock binding n packet)
   (fun event paid=>Wr.paid_in_joint binding n packet (rootEvent binding n packet)
   (root_present binding n packet) event paid) seen

theorem boundary_in_next_of_stock (word : Formal ℤ (PairValue (Lower.Value W n)) X s)
 (written : ∀ event ∈ (SourceOperationPaidRelations.exposure
   (M.paidTrace binding n packet s word)).trace,
   event ∈ (Wr.stock binding n packet).trace) :
 writerBoundary binding n packet word ∈ (Wr.jointHistory binding n packet).relationClosure := by
 let origin:=RootedAccountedUnfolding.zero PUnit.unit
 have seen:=SourceOperationPaidRelations.boundary_in_inventory origin
  (M.paidTrace binding n packet s word)
 exact SourceOperationPaidRelations.relations_next origin
  (SourceOperationPaidRelations.exposure (M.paidTrace binding n packet s word))
  (RootedAccountedUnfolding.zero (Q.actualOccurrence (Wr.receiver binding n packet))) (Wr.jointStock binding n packet)
  (fun event paid=>Wr.stock_in_joint binding n packet event (written event paid)) seen
def rawBoundaryVector:(Wr.jointHistory binding n packet).generatorClosure:=
 ⟨writerBoundary binding n packet (rawWord binding n packet),
  (Wr.jointHistory binding n packet).relationClosure_le_generatorClosure (raw_boundary_in_next binding n packet)⟩
theorem raw_boundary_relation:rawBoundaryVector binding n packet∈(Wr.jointHistory binding n packet).relationInGeneratorClosure:=
 raw_boundary_in_next binding n packet
include native in
theorem actual_next_relation_value:
 (Lower.SourceFamily.Foresight.Contextual.Profile.Kernel.afterFace binding n packet).closureEvaluation
  (rawBoundaryVector binding n packet)=
 rebase binding n packet (actor binding n packet native (beforeq binding n packet (currentBeta binding n packet)+
  beforeq binding n packet (substitutedBeta binding n packet))) :=
 (Lower.SourceFamily.Foresight.Contextual.Forecast.Dispatch.free_evaluation
  (A.nextPacket binding n packet).2 (A.afterFrame binding n packet) (A.afterIndex binding n packet).2
  (A.afterSource binding n packet) _).trans (raw_writer_action binding n packet native)
end ActualPacket
end Lower.SourceFamily.Foresight.Contextual.Profile.Affine
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
