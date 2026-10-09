import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Psi.TerminalTransport
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Psi.Source
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Written
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.TerminalConsumption
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.History.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
namespace Lower.SourceFamily.Foresight.Contextual.Psi.Closure
namespace P
export Lower.SourceFamily.Foresight.Contextual.Psi (cfg0 receipt endpointFrame installedFace written bootstrap_written)
end P
namespace T
export Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Terminal (written)
end T
namespace Wr
export Lower.SourceFamily.Foresight.Contextual.Written
 (receiver nextSeed stock jointStock jointHistory jointRaw jointDisposition jointQuery jointWritten
  psi_written_in_stock stock_in_joint query_consumes_disposition)
end Wr
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence)
end Q
namespace Lift
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (liftEvent)
end Lift
namespace K
export Lower.SourceFamily.Foresight.Contextual.Profile.Kernel (afterFace afterDisposition before_actual_index)
end K
namespace A
export Lower.SourceFamily.Foresight.Contextual.Profile.Assembly
 (nextPacket afterFrame afterIndex afterSource AfterTarget afterJointModule)
end A
namespace NextReader
export Lower.SourceFamily.Foresight.Contextual.Profile.Producer (query)
end NextReader
namespace Dispatch
export Lower.SourceFamily.Foresight.Contextual.Forecast.Dispatch (queryRaw)
end Dispatch
namespace J
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint (history)
end J
namespace ClosureProjection
variable {R G : Type u} {root : RootedAccountedUnfolding R}
variable {seed : RootedAccountedUnfolding (PresentedRelationEventAt G)}
variable {continuation : RootedAccountedUnfolding (PresentedRelationEventAt G → RootedAccountedUnfolding (PresentedRelationEventAt G))}
variable (history : RootGeneratedCofinalHistoryAt root seed continuation)
variable (relation : history.relationClosure)
def generator : history.generatorClosure := ⟨relation.val,history.relationClosure_le_generatorClosure relation.property⟩
theorem included : generator history relation∈history.relationInGeneratorClosure := relation.property
theorem zero : history.completionProjection (generator history relation)=0 :=
 (Submodule.Quotient.mk_eq_zero _).mpr (included history relation)
end ClosureProjection
namespace DispositionProjection
variable {Root Generator Carrier:Type u} [AddCommGroup Carrier]
variable {root:RootedAccountedUnfolding Root}
variable {seed:RootedAccountedUnfolding (PresentedRelationEventAt Generator)}
variable {continuation:RootedAccountedUnfolding
 (PresentedRelationEventAt Generator→RootedAccountedUnfolding (PresentedRelationEventAt Generator))}
variable {history:RootGeneratedCofinalHistoryAt root seed continuation}
variable {evaluator:RootedAccountedUnfolding (Generator→Carrier)}
variable (face:CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt history evaluator) (word:Generator→₀ℤ)
def At (outcome:ResidualDispositionOutcome face):Prop:=
 match outcome with
 | .faithful _ _ _ =>face.freeEvaluation word=0
 | .unsound _ coordinate =>face.freeEvaluation coordinate.relation≠0
 | .kernelResidual _ _ _ =>face.freeEvaluation word=0
 | .coverageResidual _ _ _ =>face.freeEvaluation word=0
theorem read (present:word∈history.relationClosure) (outcome:ResidualDispositionOutcome face):
 At face word outcome:=by
 cases outcome with
 | faithful sound _ _ =>exact LinearMap.mem_ker.mp (sound.sound present)
 | unsound _ coordinate =>exact fun zero=>coordinate.coordinate_ne_zero (coordinate.coordinate_eq.trans zero)
 | kernelResidual sound _ _ =>exact LinearMap.mem_ker.mp (sound.sound present)
 | coverageResidual sound _ _ =>exact LinearMap.mem_ker.mp (sound.sound present)
end DispositionProjection
variable {S : Type u} {W X : S → Type u} [∀t,AddCommGroup (W t)] {s : S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding : ∀t,X t→Expr W X t) (n : Nat)
variable (packet : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
local instance afterModule : Module ℤ (A.AfterTarget binding n packet) := A.afterJointModule binding n packet

theorem terminal_written : P.written binding n packet.2 packet.1=T.written binding n packet :=
 Lower.SourceFamily.Foresight.Contextual.Psi.TerminalTransport.terminal_written binding n packet

theorem terminal_in_stock (event) (present : event∈(T.written binding n packet).trace) :
 Lift.liftEvent event∈(Wr.stock binding n packet).trace :=
 Wr.psi_written_in_stock binding n packet event
  (Eq.mpr (congrArg (fun inventory=>event∈inventory.trace) (terminal_written binding n packet)) present)

theorem terminal_in_history (event) (present : event∈(T.written binding n packet).trace) :
 Lift.liftEvent event∈((Wr.jointHistory binding n packet).observation 0).trace :=
 Wr.stock_in_joint binding n packet _ (terminal_in_stock binding n packet event present)

abbrev sourceTrace := (P.installedFace binding n packet.2 packet.1).rootRead.state.2
abbrev sourceRoot := RootedAccountedUnfolding.zero
 ((P.endpointFrame binding n packet.2 packet.1).currentState.root.emitted
  (P.endpointFrame binding n packet.2 packet.1).currentState.visit.current)
abbrev nextRoot := RootedAccountedUnfolding.zero (Q.actualOccurrence (Wr.receiver binding n packet))
abbrev sourceHistory := SourceOperationPaidRelations.history (sourceRoot binding n packet) (sourceTrace binding n packet)

theorem psi_event (event) (present : event∈(P.written binding n packet.2 packet.1).trace) :
 Lift.liftEvent event∈(Wr.jointStock binding n packet).trace :=
 Wr.stock_in_joint binding n packet _ (Wr.psi_written_in_stock binding n packet event present)

theorem all_relations : (sourceHistory binding n packet).relationClosure≤
 (Wr.jointHistory binding n packet).relationClosure.comap (liftMap (R:=ℤ)) :=
 Lower.SourceFamily.Foresight.Contextual.Profile.History.Generic.relations
  (sourceRoot binding n packet) (nextRoot binding n packet)
  (P.written binding n packet.2 packet.1) (Wr.jointStock binding n packet) (psi_event binding n packet)

theorem all_generators : (sourceHistory binding n packet).generatorClosure≤
 (Wr.jointHistory binding n packet).generatorClosure.comap (liftMap (R:=ℤ)) :=
 Lower.SourceFamily.Foresight.Contextual.Profile.History.Generic.generators
  (sourceRoot binding n packet) (nextRoot binding n packet)
  (P.written binding n packet.2 packet.1) (Wr.jointStock binding n packet) (psi_event binding n packet)

abbrev boundary := relationMap (R:=ℤ)
 (P.receipt binding n packet.2 packet.1).registered.input.environment (sourceTrace binding n packet).relationWords

theorem boundary_relation : liftMap (boundary binding n packet)∈(Wr.jointHistory binding n packet).relationClosure :=
 all_relations binding n packet
  (SourceOperationPaidRelations.boundary_in_inventory (sourceRoot binding n packet) (sourceTrace binding n packet))

def boundaryRelation : (Wr.jointHistory binding n packet).relationClosure :=
 ⟨liftMap (boundary binding n packet),boundary_relation binding n packet⟩
def boundaryGenerator := ClosureProjection.generator (Wr.jointHistory binding n packet) (boundaryRelation binding n packet)

theorem boundary_in_relations : type_of% (ClosureProjection.included (Wr.jointHistory binding n packet) (boundaryRelation binding n packet)) :=
 ClosureProjection.included _ _

theorem presented_boundary_zero : type_of% (ClosureProjection.zero (Wr.jointHistory binding n packet) (boundaryRelation binding n packet)) :=
 ClosureProjection.zero _ _

abbrev afterHistory := J.history (A.nextPacket binding n packet).2 (A.afterFrame binding n packet) (A.afterIndex binding n packet).2

theorem actual_after_boundary : liftMap (boundary binding n packet)∈(afterHistory binding n packet).relationClosure := by
 have index:=K.before_actual_index (n+1) (A.nextPacket binding n packet) rfl
 have same:=congrArg (fun index=>(J.history (A.nextPacket binding n packet).2 (A.afterFrame binding n packet) index.2).relationClosure) index
 exact Eq.mp (congrArg (fun closure=>liftMap (boundary binding n packet)∈closure) same)
  (boundary_relation binding n packet)

abbrev nextFace := K.afterFace binding n packet
abbrev nextDisposition := K.afterDisposition binding n packet

private theorem boundary_sound (sound : GeneratedRelationSoundnessAt (nextFace binding n packet)) :
 (nextFace binding n packet).freeEvaluation (liftMap (boundary binding n packet))=0 :=
 LinearMap.mem_ker.mp (sound.sound (actual_after_boundary binding n packet))

def dispositionRead : Prop :=
 DispositionProjection.At (nextFace binding n packet) (liftMap (boundary binding n packet))
  (nextDisposition binding n packet)

theorem actual_disposition_read : dispositionRead binding n packet :=
 DispositionProjection.read (nextFace binding n packet) (liftMap (boundary binding n packet))
  (actual_after_boundary binding n packet) (nextDisposition binding n packet)

theorem next_query_consumes :
 NextReader.query binding (n+1) (A.nextPacket binding n packet).2 (A.afterFrame binding n packet) (A.afterIndex binding n packet)=
 Dispatch.queryRaw (A.nextPacket binding n packet).2 (A.afterFrame binding n packet) (A.afterIndex binding n packet).2
 (Lower.SourceFamily.Foresight.Contextual.Reader.Core.raw binding (n+1)
  (A.nextPacket binding n packet).2 (A.afterFrame binding n packet) (A.afterIndex binding n packet))
 (A.afterSource binding n packet) (nextDisposition binding n packet) := rfl
end Lower.SourceFamily.Foresight.Contextual.Psi.Closure
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
