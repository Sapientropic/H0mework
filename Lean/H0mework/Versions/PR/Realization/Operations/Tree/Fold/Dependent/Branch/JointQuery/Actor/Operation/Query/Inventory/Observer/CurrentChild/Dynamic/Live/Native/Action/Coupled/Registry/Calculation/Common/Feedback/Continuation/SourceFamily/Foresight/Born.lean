import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Installation
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Target
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace Lower.SourceFamily.Foresight.Born
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (datum root visit nextBorn actualOccurrence)
end Q
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
end E
namespace I
export Lower.SourceFamily.Foresight.Installed
  (binding baseCfg nativeState modelValues component combined configuration face sourceHigh sourceDecoder actualHighRead OccurrenceIndex)
end I
variable {S : Type u} {W X : S → Type u} [∀ t, AddCommGroup (W t)] {s : S}
local instance stageGroups (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
variable (binding : ∀ t, X t → Expr W X t) (n : Nat)
variable (seed : Lower.SourceFamily.Seed W X s n)
local notation "FrameAt" => M.Frame (Value := Lower.Value W n) (Var := X) (sort := s)
abbrev EnvironmentIndex (frame : FrameAt) := Sigma fun current : frame.V.Current =>
  frame.old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current

theorem pre_emitter_final_face_same (frame : FrameAt) :
    I.sourceHigh binding n seed frame =
      I.actualHighRead binding n seed (E.epoch frame) rfl := rfl

theorem next_environment_read (frame : FrameAt)
    (index : EnvironmentIndex n (Q.nextBorn frame (I.configuration binding n seed))) :
    (Q.nextBorn frame (I.configuration binding n seed)).environment index.2 =
      I.sourceDecoder binding n seed frame := rfl

theorem next_environment_uses_face (frame : FrameAt)
    (index : EnvironmentIndex n (Q.nextBorn frame (I.configuration binding n seed))) :
    (Q.nextBorn frame (I.configuration binding n seed)).environment index.2 =
      fun t name =>
        ((I.actualHighRead binding n seed (E.epoch frame) rfl).2.1 t name).1 +
          ((I.actualHighRead binding n seed (E.epoch frame) rfl).2.1 t name).2 := rfl

theorem next_environment_source (frame : FrameAt)
    (index : EnvironmentIndex n (Q.nextBorn frame (I.configuration binding n seed))) :
    (Q.nextBorn frame (I.configuration binding n seed)).environment index.2 =
      Future.Replay.Source.physicalNext (I.binding binding n)
        (E.epoch frame) (Q.actualOccurrence (E.epoch frame)) := by
  rw [next_environment_read]
  rw [Lower.SourceFamily.Foresight.Installed.source_decoder_original]

end Lower.SourceFamily.Foresight.Born
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation

end
