import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Feedback.Consumer
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Engine
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Future.Replay
namespace Move
namespace Faces
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower
 (configuration actual_faces actual_dual_readback)
end Faces
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
variable (binding : ∀ t,X t → Expr W X t)
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr W X s)))
variable (frame : M.Frame (Value:=W) (Var:=X) (sort:=s))
def cfg := Faces.configuration (Installed.programme binding seed)
theorem language : (cfg binding seed).LowVar=X := rfl
def scalar := Stock.preserve
 (some ((Installed.scalarStock binding seed frame).map (T.liftEvent (W:=W) (X:=X) (s:=s))))
 (Lower.Stock.scalar frame (cfg binding seed) rfl)
def pair := Stock.preserve
 (some ((Installed.pairStock binding seed frame).map (T.liftEvent (W:=PairValue W) (X:=X) (s:=s))))
 (Lower.Stock.pair frame (cfg binding seed) rfl)
def receiver := B.initial frame (cfg binding seed) (scalar binding seed frame) (pair binding seed frame)
def nextSeed := SourceHistoryCommon.seed (scalar binding seed frame)
 (RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator (receiver binding seed frame).registered.input.expression))
def nextBinding (target : S) (name : X target) := liftExpr (binding target name)
def nextCfg := Faces.configuration (Installed.programme (nextBinding binding) (nextSeed binding seed frame))
def generated := Admission.generatedAction frame (cfg binding seed)
 (scalar binding seed frame) (pair binding seed frame) (nextCfg binding seed frame)
abbrev presentation := Admission.presentation frame (cfg binding seed)
 (scalar binding seed frame) (pair binding seed frame) (nextCfg binding seed frame)
abbrev event := Admission.sourceEvent frame (cfg binding seed)

theorem actual_raw : (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame (cfg binding seed)).raw=
 Source.raw binding seed (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame)
  (Installed.Q.actualOccurrence frame) := congrArg (fun query => query.raw) (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query_generated frame (cfg binding seed))

theorem target_root : type_of% (Admission.target_root frame (cfg binding seed)
 (scalar binding seed frame) (pair binding seed frame) (nextCfg binding seed frame) (event binding seed frame)) :=
 Admission.target_root _ _ _ _ _ _

theorem whole_first : type_of% (generated binding seed frame).target.firstDestination_heq :=
 (generated binding seed frame).target.firstDestination_heq

theorem old_projection (projection : (Admission.sourceRoot frame (cfg binding seed)).toAuthoritativeRoot.source.projectionLaw.Projection) :
 type_of% ((generated binding seed frame).target.oldOutcome_heq projection) :=
 (generated binding seed frame).target.oldOutcome_heq projection

theorem canonical_next : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockAdmission.target_erasure
 frame (cfg binding seed) (scalar binding seed frame) (pair binding seed frame) (nextCfg binding seed frame)) :=
 SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockAdmission.target_erasure _ _ _ _ _

theorem source_valid (candidate : (presentation binding seed frame).Query) : type_of%
 (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockAdmission.successor_valid
 frame (cfg binding seed) (scalar binding seed frame) (pair binding seed frame) (nextCfg binding seed frame) candidate) :=
 SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockAdmission.successor_valid _ _ _ _ _ _

theorem next_reader : (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query
 (receiver binding seed frame) (nextCfg binding seed frame)).raw=
 Source.raw (nextBinding binding) (nextSeed binding seed frame)
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (receiver binding seed frame))
 (Installed.Q.actualOccurrence (receiver binding seed frame)) := congrArg (fun query => query.raw) (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query_generated (receiver binding seed frame) (nextCfg binding seed frame))

def sourceFaces := Faces.actual_faces frame (Installed.programme binding seed)
def nextFaces := Faces.actual_faces (receiver binding seed frame)
 (Installed.programme (nextBinding binding) (nextSeed binding seed frame))
end Move
end Future.Replay
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
