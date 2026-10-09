import H0mework.Versions.PR.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Boundary
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Psi.Closure
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Environment
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Psi.Equation
namespace Ps
export Lower.SourceFamily.Foresight.Contextual.Psi (receipt installedFace endpointFrame source_clock installed_full_state)
end Ps
namespace Cl
export Lower.SourceFamily.Foresight.Contextual.Psi.Closure (sourceTrace boundary boundary_relation)
end Cl
namespace Claim
export Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim
 (cfg material activeExpression activeEnv activeWord actionWord readerValue endpointCorrection input_expression reader_endpoint raw_source actual_claim_equation)
end Claim
namespace Env
export Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Environment (activeIncrement actual_environment)
end Env
namespace Af
export Lower.SourceFamily.Foresight.Contextual.Profile.Affine
 (AfterScope afterq constant rawWord writerBoundary writerValue writer_head head_source afterEnv after_environment)
end Af
namespace A
export Lower.SourceFamily.Foresight.Contextual.Profile.Assembly (AfterTarget afterJointModule)
end A
namespace Wr
export Lower.SourceFamily.Foresight.Contextual.Written
 (jointHistory stock stock_in_joint action_written_in_stock)
end Wr
namespace C
export Lower.SourceFamily.Foresight.Contextual (actionWord actionWritten)
end C
namespace E
export Lower.SourceFamily.Foresight.Contextual.Effect (actualEnvironment source_environment)
end E
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (query)
end Q
namespace C
export RootGeneratedDebtActivationJointSource.Successor.Restructuring.Completion (completed completed_value)
end C
namespace Req
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (expression)
end Req
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat)
variable (packet:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
local instance afterModule:Module ℤ (A.AfterTarget binding n packet):=A.afterJointModule binding n packet
abbrev terminalValue : Lower.Value W (n+1) s :=(Ps.installedFace binding n packet.2 packet.1).rootRead.value
abbrev readerValue : Lower.Value W (n+1) s :=Claim.readerValue binding n packet
abbrev gamma : Expr (Lower.Value W (n+1)) X s :=
 (SourceGeneratedInquiryReceiptAction.actionReader packet.1 (Claim.cfg binding n packet)
  (SourceGeneratedInquiryReceiptAction.occurrence packet.1 (Claim.cfg binding n packet))).expression
abbrev beta : Formal ℤ (Lower.Value W (n+1)) X s :=Cl.boundary binding n packet
abbrev activeWord : Formal ℤ (Lower.Value W (n+1)) X s :=Claim.activeWord binding n packet

theorem terminal_value : terminalValue binding n packet=
 (Claim.activeExpression binding n packet).eval (Claim.activeEnv binding n packet) :=
 (SourceRegisteredClaimCompletion.value (Ps.endpointFrame binding n packet.2 packet.1)).trans
  (congrArg₂ (fun expression:Expr (Lower.Value W (n+1)) X s=>fun environment:Env (Lower.Value W (n+1)) X=>expression.eval environment)
   (Lower.SourceFamily.Foresight.Contextual.Psi.TerminalTransport.same_expression binding n packet)
   (Lower.SourceFamily.Foresight.Contextual.Psi.TerminalTransport.same_environment binding n packet))

theorem boundary_words : beta binding n packet=
 activeWord binding n packet-Finsupp.single (Expr.const (terminalValue binding n packet)) (1:ℤ) :=
 (SourceRegisteredClaimBoundary.boundary (Ps.endpointFrame binding n packet.2 packet.1)
  (Ps.source_clock binding n packet.2 packet.1)).trans
  (congrArg (fun expression:Expr (Lower.Value W (n+1)) X s=>
   (Finsupp.single expression (1:ℤ):Formal ℤ (Lower.Value W (n+1)) X s)-
   (Finsupp.single (show Expr (Lower.Value W (n+1)) X s from Expr.const (terminalValue binding n packet)) (1:ℤ):
    Formal ℤ (Lower.Value W (n+1)) X s))
   (Lower.SourceFamily.Foresight.Contextual.Psi.TerminalTransport.same_expression binding n packet))

theorem boundary_affine : Af.afterq binding n packet (liftMap (beta binding n packet))=
 Af.afterq binding n packet (liftMap (activeWord binding n packet))-
 Af.constant binding n packet (terminalValue binding n packet,0) :=by
 have constantLift:liftMap (R:=ℤ) (Finsupp.single (Expr.const (terminalValue binding n packet)) (1:ℤ))=
  Finsupp.single (show Expr (PairValue (Lower.Value W (n+1))) X s from
   .const (terminalValue binding n packet,(0 : Lower.Value W (n+1) s))) (1:ℤ) :=by
  simp only [liftMap,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,liftExpr]
 have lifted:liftMap (beta binding n packet)=liftMap (activeWord binding n packet)-
  liftMap (Finsupp.single (Expr.const (terminalValue binding n packet)) (1:ℤ)) :=
  (congrArg (liftMap (R:=ℤ)) (boundary_words binding n packet)).trans
   ((liftMap (R:=ℤ)).map_sub _ _)
 have evaluated:Af.afterq binding n packet (liftMap (beta binding n packet))=
  Af.afterq binding n packet (liftMap (activeWord binding n packet))-
  Af.afterq binding n packet (liftMap (Finsupp.single (Expr.const (terminalValue binding n packet)) (1:ℤ))) :=
  (congrArg (Af.afterq binding n packet) lifted).trans ((Af.afterq binding n packet).map_sub _ _)
 exact evaluated.trans (congrArg
  (fun word:Formal ℤ (PairValue (Lower.Value W (n+1))) X s=>
   Af.afterq binding n packet (liftMap (activeWord binding n packet))-Af.afterq binding n packet word) constantLift)

def correction : PairValue (Lower.Value W (n+1)) s :=
 Af.writerValue binding n packet (Claim.actionWord binding n packet)-
 (readerValue binding n packet+terminalValue binding n packet,(0 : Lower.Value W (n+1) s))

variable (native:packet.1.depth=0)
include native in
theorem boundary_equation : Af.afterq binding n packet (liftMap (beta binding n packet))=
 Af.afterq binding n packet (Af.writerBoundary binding n packet (Claim.actionWord binding n packet))+
 Af.constant binding n packet (correction binding n packet) :=by
 let terminalPoint:Af.AfterScope binding n packet:=Af.constant binding n packet
  (terminalValue binding n packet,(0:Lower.Value W (n+1) s))
 let boundaryPoint:Af.AfterScope binding n packet:=Af.afterq binding n packet
  (Af.writerBoundary binding n packet (Claim.actionWord binding n packet))
 let correctionPoint:Af.AfterScope binding n packet:=Af.constant binding n packet (Claim.endpointCorrection binding n packet)
 have generated:Af.afterq binding n packet (liftMap (beta binding n packet))=
  (boundaryPoint+correctionPoint)-terminalPoint :=
  (boundary_affine binding n packet).trans
   (congrArg (fun point:Af.AfterScope binding n packet=>point-terminalPoint)
    (Claim.actual_claim_equation binding n packet native))
 have split:Claim.endpointCorrection binding n packet-
  (show PairValue (Lower.Value W (n+1)) s from (terminalValue binding n packet,(0 : Lower.Value W (n+1) s)))=
  correction binding n packet :=by
  apply Prod.ext
  · change ((Af.writerValue binding n packet (Claim.actionWord binding n packet)).1-readerValue binding n packet)-
     terminalValue binding n packet=(Af.writerValue binding n packet (Claim.actionWord binding n packet)).1-
     (readerValue binding n packet+terminalValue binding n packet)
    abel
  · change ((Af.writerValue binding n packet (Claim.actionWord binding n packet)).2-0)-0=
     (Af.writerValue binding n packet (Claim.actionWord binding n packet)).2-0
    abel
 have linear:correctionPoint-terminalPoint=Af.constant binding n packet (correction binding n packet) :=
  ((Af.constant binding n packet).map_sub (Claim.endpointCorrection binding n packet)
   (show PairValue (Lower.Value W (n+1)) s from
    (terminalValue binding n packet,(0:Lower.Value W (n+1) s)))).symm.trans
   (congrArg (Af.constant binding n packet) split)
 exact generated.trans ((add_sub_assoc boundaryPoint correctionPoint terminalPoint).trans
  (congrArg (fun point:Af.AfterScope binding n packet=>boundaryPoint+point) linear))

def difference : Formal ℤ (PairValue (Lower.Value W (n+1))) X s := liftMap (beta binding n packet)-
 Af.writerBoundary binding n packet (Claim.actionWord binding n packet)

theorem difference_member : difference binding n packet∈(Wr.jointHistory binding n packet).relationClosure :=
 Submodule.sub_mem _ (Cl.boundary_relation binding n packet)
 (Lower.SourceFamily.Foresight.Contextual.Profile.Affine.boundary_in_next_of_stock
  binding n packet (Claim.actionWord binding n packet) (by
   intro event paid
   apply Wr.action_written_in_stock binding n packet event
   exact paid))

abbrev afterHistory := Lower.SourceFamily.Foresight.Contextual.Psi.Closure.afterHistory binding n packet
theorem difference_after : difference binding n packet∈(afterHistory binding n packet).relationClosure :=by
 have index:=Lower.SourceFamily.Foresight.Contextual.Profile.Kernel.before_actual_index (n+1)
  (Lower.SourceFamily.Foresight.Contextual.Profile.Assembly.nextPacket binding n packet) rfl
 have same:=congrArg (fun index=>(Lower.SourceFamily.Foresight.Contextual.Psi.Closure.J.history
  (Lower.SourceFamily.Foresight.Contextual.Profile.Assembly.nextPacket binding n packet).2
  (Lower.SourceFamily.Foresight.Contextual.Profile.Assembly.afterFrame binding n packet) index.2).relationClosure) index
 exact Eq.mp (congrArg (fun closure=>difference binding n packet∈closure) same)
  (difference_member binding n packet)

def differenceRelation : (Wr.jointHistory binding n packet).relationClosure :=
 ⟨difference binding n packet,difference_member binding n packet⟩

include native in
theorem difference_scope : Af.afterq binding n packet (difference binding n packet)=
 Af.constant binding n packet (correction binding n packet) :=by
 have evaluated:Af.afterq binding n packet (difference binding n packet)=
  Af.afterq binding n packet (liftMap (beta binding n packet))-
  Af.afterq binding n packet (Af.writerBoundary binding n packet (Claim.actionWord binding n packet)) :=
  (Af.afterq binding n packet).map_sub _ _
 exact evaluated.trans ((congrArg (fun point:Af.AfterScope binding n packet=>
  point-Af.afterq binding n packet (Af.writerBoundary binding n packet (Claim.actionWord binding n packet)))
  (boundary_equation binding n packet native)).trans (add_sub_cancel_left _ _))

theorem value_affine : terminalValue binding n packet=
 (gamma binding n packet).eval (Claim.activeEnv binding n packet)-readerValue binding n packet :=by
 rw [terminal_value,Claim.input_expression]
 unfold Req.expression
 rw [Claim.reader_endpoint,Claim.raw_source]
 simp only [gamma,readerValue,Expr.eval,AddMonoidHom.neg_apply,AddMonoidHom.id_apply]
 exact (sub_eq_add_neg ((gamma binding n packet).eval (Claim.activeEnv binding n packet))
  (readerValue binding n packet)).symm

variable (paid:Lower.SourceFamily.Effect.PaidSource.Paid packet.1)
include paid in
theorem writer_channels : Af.writerValue binding n packet (Claim.actionWord binding n packet)=
 ((gamma binding n packet).eval (Claim.activeEnv binding n packet),
  (gamma binding n packet).effect (Claim.activeEnv binding n packet) (Env.activeIncrement binding n packet)) :=by
 have environment:Af.afterEnv binding n packet=pairEnvironment (Claim.activeEnv binding n packet)
  (Env.activeIncrement binding n packet):=
  ((Af.after_environment binding n packet).trans (E.source_environment binding n packet)).trans
   (Env.actual_environment binding n packet paid)
 apply (Af.writer_head binding n packet (Claim.actionWord binding n packet)).symm.trans
 apply (Af.head_source binding n packet (liftMap (Claim.actionWord binding n packet))).trans
 apply (congrArg (fun env=>evaluation (R:=ℤ) env (liftMap (Claim.actionWord binding n packet))) environment).trans
 apply (LinearMap.congr_fun (evaluation_liftMap (R:=ℤ) (s:=s)
  (Claim.activeEnv binding n packet) (Env.activeIncrement binding n packet)) (Claim.actionWord binding n packet)).trans
 simp only [gamma,Claim.actionWord,updateInventory,
  LinearMap.prod_apply,Function.prod,evaluation,effectEvaluator,Finsupp.linearCombination_single,one_smul]
 rfl

include paid in
theorem correction_channels : correction binding n packet=
 (0,(gamma binding n packet).effect (Claim.activeEnv binding n packet) (Env.activeIncrement binding n packet)) :=by
 apply (congrArg (fun value:PairValue (Lower.Value W (n+1)) s=>value-
  (readerValue binding n packet+terminalValue binding n packet,(0 : Lower.Value W (n+1) s)))
  (writer_channels binding n packet paid)).trans
 apply (congrArg (fun value:Lower.Value W (n+1) s=>
  ((gamma binding n packet).eval (Claim.activeEnv binding n packet),
   (gamma binding n packet).effect (Claim.activeEnv binding n packet) (Env.activeIncrement binding n packet))-
  (readerValue binding n packet+value,(0 : Lower.Value W (n+1) s)))
  (value_affine binding n packet)).trans
 apply Prod.ext
 · change (gamma binding n packet).eval (Claim.activeEnv binding n packet)-
    (readerValue binding n packet+((gamma binding n packet).eval (Claim.activeEnv binding n packet)-readerValue binding n packet))=0
   abel
 · exact sub_zero _

include native paid in
theorem difference_effect : Af.afterq binding n packet (difference binding n packet)=
 Af.constant binding n packet (0,(gamma binding n packet).effect (Claim.activeEnv binding n packet)
  (Env.activeIncrement binding n packet)) :=
 (difference_scope binding n packet native).trans
 (congrArg (Af.constant binding n packet) (correction_channels binding n packet paid))

namespace Actual
open RootLawDependentJointStateController
namespace Run
export Lower.SourceFamily.Foresight.Contextual.Profile.Kernel.Actual.Run (binding data actual_depth)
end Run
variable {N:WorldRelationNetwork.{u}} {V:Vocabulary.{u}}
variable {H:Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root:SourceNativeLivingRootClosure N V)
variable (visit:SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec:RecognitionAt H root)
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.Profile.Kernel.Actual.physicalGroups
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.Profile.Kernel.Actual.currentGroups
variable (U7:U7ProducerCalculus N) (calculus:U7ObstructionEvolutionCalculus N U7)
variable (anchor sourceStage stage count:Nat)

theorem source_equation (k:Nat):type_of% (boundary_equation (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)
 (Run.actual_depth root visit rec U7 calculus anchor sourceStage stage count k)):=
 boundary_equation _ _ _ (Run.actual_depth root visit rec U7 calculus anchor sourceStage stage count k)

theorem source_relation (k:Nat):type_of% (difference_member (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)):=difference_member _ _ _

theorem source_effect (k:Nat):type_of% (difference_effect (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)
 (Run.actual_depth root visit rec U7 calculus anchor sourceStage stage count k)
 (Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Environment.Actual.source_paid
  root visit rec U7 calculus anchor sourceStage stage count k)):=
 difference_effect _ _ _ (Run.actual_depth root visit rec U7 calculus anchor sourceStage stage count k)
 (Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Environment.Actual.source_paid
  root visit rec U7 calculus anchor sourceStage stage count k)
end Actual
end Lower.SourceFamily.Foresight.Contextual.Psi.Equation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
