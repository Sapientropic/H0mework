import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Installation.Source

/-! The actual macro reads its original installed raw family. The source
component's branch-generated next raw is identified with the same tick's
successor; a residual birth keeps its full new expression and environment. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Installation
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion
namespace M
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation
  (Frame frames runtime inquiryProcess)
end M
namespace I
export RootGeneratedDebtActivationJointSource.Successor.Inquiry (mathCurrent rawFace)
namespace Assembly
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Assembly (rawInstallation)
end Assembly
end I
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (initial : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

private def readRestriction (actual : AnyAuthoritativeRootCurrent.{u})
    (restriction : RawRestrictionAt (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) actual) :
    Raw (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) :=
  Eq.mp restriction.payload_eq (actual.current.root.source.projectionLaw.project
    restriction.projection (actual.current.root.emitted actual.current.visit.current) restriction.active)

private theorem readRestriction_transport {first second : AnyAuthoritativeRootCurrent.{u}}
    (same : first = second)
    (restriction : RawRestrictionAt (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) second) :
    readRestriction first (same.symm ▸ restriction) = readRestriction second restriction := by
  cases same
  rfl

private def frameRaw (frame : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)) :
    RawRestrictionAt (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort)
      frame.currentPresentation.erase :=
  { projection := (I.Assembly.rawInstallation frame.old frame.registered frame.packetAt).embed PUnit.unit
    active := PUnit.unit
    classifier_eq := rfl
    payload_eq := rfl }

def rawSource (state : (M.runtime initial).State) :
    RawAt (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) (M.runtime initial) state := by
  rcases state with ⟨⟨count⟩, activation⟩
  let frame := M.frames initial count.down
  change RawRestrictionAt (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) frame.presentation.erase
  exact frame.presentation_erase.symm ▸ frameRaw frame

private def index (engine : Engine (M.inquiryProcess initial)) : Nat := by
  rcases engine with ⟨count⟩
  exact count.down

private theorem raw_state (state : (M.runtime initial).State) :
    Context.raw (M.runtime initial) (rawSource initial) state =
      (M.frames initial (index initial state.engine)).rawRead := by
  rcases state with ⟨⟨count⟩, activation⟩
  change readRestriction (M.frames initial count.down).presentation.erase
    ((M.frames initial count.down).presentation_erase.symm ▸ frameRaw (M.frames initial count.down)) = _
  exact (readRestriction_transport (M.frames initial count.down).presentation_erase
    (frameRaw (M.frames initial count.down))).trans (by rfl)

theorem raw_actual (count : Nat) :
    Context.raw (M.runtime initial) (rawSource initial) ((M.runtime initial).stateAt count) =
      (M.frames initial count).rawRead := by
  have indexEq : index initial ((M.runtime initial).stateAt count).engine = count := by
    have same := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.actual_node initial count
    generalize engineEq : ((M.runtime initial).stateAt count).engine = engine at same ⊢
    rcases engine with ⟨hidden⟩
    have hiddenEq : hidden = ULift.up count :=
      (M.inquiryProcess initial).erase_injective rfl rfl
        (congrArg RootInquiryProcessNode.erase same)
    subst hidden
    rfl
  exact (raw_state initial _).trans (congrArg (fun n => (M.frames initial n).rawRead)
    indexEq)

theorem next_raw_source (frame : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)) :
    nextRawAt frame (frame.currentState.root.emitted frame.currentState.visit.current) = frame.next.rawRead := by
  unfold nextRawAt RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.next
    RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.nextFrom
  dsimp only [RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.currentState,
    RootGeneratedDebtActivationJointSource.Successor.Inquiry.Source.currentState,
    RootGeneratedDebtActivationJointSource.Successor.Inquiry.mathState,
    RootGeneratedDebtActivationJointSource.Successor.Inquiry.mathVisit,
    RootGeneratedDebtActivationJointSource.Successor.Inquiry.temporalVisit,
    SourceNativeTemporalVisitAt.finite,
    RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.event]
  dsimp only [RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.action,
    RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.event,
    RootGeneratedDebtActivationJointSource.Successor.Inquiry.mathCurrent]
  cases selected : RootGeneratedDebtActivationJointSource.mathAction
    (RootGeneratedDebtActivationJointSource.Successor.Inquiry.finiteVisit frame.old
      frame.registered frame.packetAt (frame.depth + 1)).current.2 with
  | inr paid => rfl
  | inl settled => rfl

theorem increment_birth (frame : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)) :
    (nextRawAt frame (frame.currentState.root.emitted frame.currentState.visit.current)).environment =
      match frame.action with
      | .inr _ => frame.rawRead.environment
      | .inl _ => frame.activeEnvironment := by
  rw [next_raw_source]
  unfold RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.next
    RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.nextFrom
  cases selected : frame.action with
  | inr paid => rfl
  | inl settled =>
      exact RootGeneratedDebtActivationJointSource.Successor.Inquiry.Source.request_environment
        frame.old frame.registered frame.packetAt frame.environment frame.depth

end SourceOperationInquiry.Context.Installation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
