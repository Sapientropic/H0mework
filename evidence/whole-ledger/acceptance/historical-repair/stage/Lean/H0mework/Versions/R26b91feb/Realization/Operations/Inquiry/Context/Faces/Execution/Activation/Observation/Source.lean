import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Runtime
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Installation.Runtime

/-! The activated calculation query and the original physical raw are
separate restrictions of the same source occurrence. This reader follows
the inherited physical raw family through every calculation coface. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.Observation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation
  (root visit presentation base queryRoot resultRoot consumerRoot epoch queryLaw resultLaw consumerLaw compilationLaw
    runtime process frames actual_node next)
end A
namespace I
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Assembly (rawInstallation)
end I
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

def rawInstallation := (I.rawInstallation frame.old frame.registered frame.packetAt).trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface frame.currentState.root.source.base
    (SourceOperationInquiry.Context.Installation.component (A.epoch frame))) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (A.base frame).root.source.base (A.queryLaw frame)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (A.queryRoot frame).source.base (A.resultLaw frame)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (A.resultRoot frame).source.base (A.consumerLaw frame)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (A.consumerRoot frame).source.base (A.compilationLaw frame))

def rawFace : SourceNativeRootSemanticFaceAt (A.root frame) (A.visit frame) where
  projection := (rawInstallation frame).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem raw_face : (rawFace frame).rootRead = frame.rawRead := rfl

private def frameRaw : RawRestrictionAt (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort)
    (A.presentation frame).erase where
  projection := (rawInstallation frame).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl
  payload_eq := rfl

variable (initial : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

def rawSource (state : (A.runtime initial).State) :
    RawAt (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) (A.runtime initial) state := by
  rcases state with ⟨⟨count⟩, activation⟩
  exact frameRaw (A.frames initial count.down)

private def index (engine : Engine (A.process initial)) : Nat := by
  rcases engine with ⟨count⟩
  exact count.down

private theorem raw_state (state : (A.runtime initial).State) :
    Context.raw (A.runtime initial) (rawSource initial) state =
      (A.frames initial (index initial state.engine)).rawRead := by
  rcases state with ⟨⟨count⟩, activation⟩
  rfl

theorem raw_actual (count : Nat) :
    Context.raw (A.runtime initial) (rawSource initial) ((A.runtime initial).stateAt count) =
      (A.frames initial count).rawRead := by
  have indexEq : index initial ((A.runtime initial).stateAt count).engine = count := by
    have same := A.actual_node initial count
    generalize engineEq : ((A.runtime initial).stateAt count).engine = engine at same ⊢
    rcases engine with ⟨hidden⟩
    have hiddenEq : hidden = ULift.up count := (A.process initial).erase_injective rfl rfl
      (congrArg RootInquiryProcessNode.erase same)
    subst hidden
    rfl
  exact (raw_state initial _).trans (congrArg (fun n => (A.frames initial n).rawRead) indexEq)

theorem next_raw (frame : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)) :
    SourceOperationInquiry.Context.Installation.nextRawAt (A.epoch frame)
      ((A.root frame).emitted (A.visit frame).current) = (A.next frame).rawRead := by
  have readerSource : ∀ {current}
      (occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current := current)),
      SourceOperationInquiry.Context.Installation.nextRawAt (A.epoch frame) occurrence =
        SourceOperationInquiry.Context.Installation.nextRawAt frame occurrence := by
    intro current occurrence
    dsimp only [SourceOperationInquiry.Context.Faces.Execution.Activation.epoch]
    rcases occurrence with ⟨support, event⟩
    cases event
    unfold SourceOperationInquiry.Context.Installation.nextRawAt
      SourceOperationInquiry.Context.Installation.rawAt SourceOperationInquiry.Context.Installation.residualAt
    cases RootGeneratedDebtActivationJointSource.mathAction current.2 <;> rfl
  have sameSource := readerSource ((A.root frame).emitted (A.visit frame).current)
  apply sameSource.trans
  apply (SourceOperationInquiry.Context.Installation.next_raw_source frame).trans
  unfold RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.next
    RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.nextFrom
    SourceOperationInquiry.Context.Faces.Execution.Activation.next
    SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
  cases frame.action <;> rfl

end SourceOperationInquiry.Context.Faces.Execution.Activation.Observation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
