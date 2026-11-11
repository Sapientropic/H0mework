import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierNative.NextFace
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativeCayleyNextAction

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalConstantFourierRetainedFace
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution BurnolPhysicalState
namespace MS
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
  (frame endpointState residualRegistered packet endpointCount)
end MS
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
end O
namespace M
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end M
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (root visit base baseRoot datum queryLaw queryRoot resultLaw resultRoot consumerLaw consumerRoot compilationLaw
   baseInstallation frames next nextBorn originalTarget targetAt)
end S
namespace Activation
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch epoch_math)
end Activation
namespace Completion
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion (atReceipt)
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix (receipt_read)
end Completion
open private retainedFace from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativeCayleyNextAction

open private optionalFace extendFace optionalFace_read extendFace_read from
  H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Source

namespace Transport
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
variable (cfg : Activation.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))

noncomputable def sharedFace (face : SourceNativeRootSemanticFaceAt frame.currentState.root frame.currentState.visit) :
    SourceNativeRootSemanticFaceAt (S.root frame cfg) (S.visit frame cfg) :=
  optionalFace (S.base frame).root (S.datum frame cfg).component
    (extendFace (SourceOperationInquiry.Context.Installation.component (Activation.epoch frame)) face)
  |> extendFace (root := S.baseRoot frame cfg) (S.queryLaw (Activation.epoch frame) cfg)
  |> extendFace (root := S.queryRoot frame cfg) (S.resultLaw (Activation.epoch frame) cfg)
  |> extendFace (root := S.resultRoot frame cfg) (S.consumerLaw (Activation.epoch frame) cfg)
  |> extendFace (root := S.consumerRoot frame cfg) (S.compilationLaw (Activation.epoch frame) cfg)

theorem shared_payload (face : SourceNativeRootSemanticFaceAt frame.currentState.root frame.currentState.visit) :
    HEq (sharedFace frame cfg face).rootRead face.rootRead := by
  unfold sharedFace
  exact (extendFace_read _ _).trans ((extendFace_read _ _).trans
    ((extendFace_read _ _).trans ((extendFace_read _ _).trans
      ((optionalFace_read _ _ _).trans (extendFace_read _ _)))))

private theorem completed_epoch :
    Activation.epoch (Completion.atReceipt cfg frame 0) = Activation.epoch frame := by
  apply Completion.receipt_read cfg frame (fun stage => Activation.epoch (S.frames frame cfg stage))
  intro stage paid actual
  change Activation.epoch (S.next (S.frames frame cfg stage) cfg) = _
  unfold S.next
  rw [actual]
  rfl

theorem completed_frame : Completion.atReceipt cfg frame 0 =
    {frame with depth := (Completion.atReceipt cfg frame 0).depth} := by
  have restore (f : M.Frame (Value := Value) (Var := Var) (sort := sort)) :
      {Activation.epoch f with depth := f.depth} = f := rfl
  calc
    _ = {Activation.epoch (Completion.atReceipt cfg frame 0) with
        depth := (Completion.atReceipt cfg frame 0).depth} := (restore _).symm
    _ = _ := congrArg (fun f : M.Frame (Value := Value) (Var := Var) (sort := sort) =>
      {f with depth := (Completion.atReceipt cfg frame 0).depth}) (completed_epoch frame cfg)

noncomputable def faceCast {left right : M.Frame (Value := Value) (Var := Var) (sort := sort)}
    (same : left = right)
    (face : SourceNativeRootSemanticFaceAt (S.root left cfg) (S.visit left cfg)) :
    SourceNativeRootSemanticFaceAt (S.root right cfg) (S.visit right cfg) := same ▸ face

theorem faceCast_payload {left right : M.Frame (Value := Value) (Var := Var) (sort := sort)}
    (same : left = right)
    (face : SourceNativeRootSemanticFaceAt (S.root left cfg) (S.visit left cfg)) :
    HEq (faceCast cfg same face).rootRead face.rootRead := by
  cases same
  rfl

noncomputable def bornFace
    (event : ExactTemporalCausalRootEventAt (S.root frame cfg).toAuthoritativeRoot.toLedgerRoot (S.visit frame cfg))
    (face : SourceNativeRootSemanticFaceAt (S.root frame cfg) (S.visit frame.mathNext cfg)) :
    SourceNativeRootSemanticFaceAt (S.targetAt frame cfg event).targetRoot (S.targetAt frame cfg event).targetVisit :=
  optionalFace (S.base (S.nextBorn frame cfg)).root (S.datum (S.nextBorn frame cfg) cfg).component
    (extendFace (SourceOperationInquiry.Context.Installation.component (Activation.epoch (S.nextBorn frame cfg)))
      (ConstantFourierNextFace.fromNext frame cfg event face))
  |> extendFace (root := S.baseRoot (S.nextBorn frame cfg) cfg) (S.queryLaw (Activation.epoch (S.nextBorn frame cfg)) cfg)
  |> extendFace (root := S.queryRoot (S.nextBorn frame cfg) cfg) (S.resultLaw (Activation.epoch (S.nextBorn frame cfg)) cfg)
  |> extendFace (root := S.resultRoot (S.nextBorn frame cfg) cfg) (S.consumerLaw (Activation.epoch (S.nextBorn frame cfg)) cfg)
  |> extendFace (root := S.consumerRoot (S.nextBorn frame cfg) cfg) (S.compilationLaw (Activation.epoch (S.nextBorn frame cfg)) cfg)

theorem born_payload
    (event : ExactTemporalCausalRootEventAt (S.root frame cfg).toAuthoritativeRoot.toLedgerRoot (S.visit frame cfg))
    (face : SourceNativeRootSemanticFaceAt (S.root frame cfg) (S.visit frame.mathNext cfg)) :
    HEq (bornFace frame cfg event face).rootRead face.rootRead := by
  unfold bornFace
  exact (extendFace_read _ _).trans ((extendFace_read _ _).trans
    ((extendFace_read _ _).trans ((extendFace_read _ _).trans
      ((optionalFace_read _ _ _).trans ((extendFace_read _ _).trans
        (ConstantFourierNextFace.fromNext_read frame cfg event face))))))

end Transport

namespace Retained
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (u7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N u7)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt visit.current →
  O.Raw (Value := Value) (Var := Var) (sort := sort))
variable (face : SourceNativeRootSemanticFaceAt root visit)
local notation "initial" => MS.frame root visit u7 calculus reader

def frameAt (n : Nat) : M.Frame (Value := Value) (Var := Var) (sort := sort) := {initial with depth := n}

noncomputable def sourceFace (n : Nat) :
    SourceNativeRootSemanticFaceAt (frameAt root visit u7 calculus reader n).currentState.root
      (frameAt root visit u7 calculus reader n).currentState.visit where
  projection := (RootGeneratedDebtActivationJointSource.Successor.Inquiry.Assembly.oldInstallation
    (MS.endpointState root visit u7 calculus reader) (MS.residualRegistered root visit u7 calculus reader)
      (MS.packet root visit u7 calculus reader)).embed
        (.inl (retainedFace root visit u7 calculus reader face (MS.endpointCount root visit reader)).projection)
  active := face.active
  classifier_eq := face.classifier_eq

theorem source_payload (n : Nat) :
    HEq (sourceFace root visit u7 calculus reader face n).rootRead face.rootRead := HEq.rfl

variable (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
variable (cfg : Activation.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))

private theorem next_frame (same : frame = {initial with depth := frame.depth}) : frame.mathNext = frameAt root visit u7 calculus reader (frame.depth+1) :=
  congrArg (fun f : M.Frame (Value := Value) (Var := Var) (sort := sort) => f.mathNext) same

noncomputable def afterFace
    (face : SourceNativeRootSemanticFaceAt root visit)
    (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
    (same : frame = {initial with depth := frame.depth})
    (cfg : Activation.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort)) :
    SourceNativeRootSemanticFaceAt (S.root frame cfg) (S.visit frame.mathNext cfg) :=
  Transport.faceCast cfg
    (left := frameAt root visit u7 calculus reader (frame.depth+1)) (right := frame.mathNext)
    (next_frame root visit u7 calculus reader frame same).symm
    (Transport.sharedFace (frameAt root visit u7 calculus reader (frame.depth+1)) cfg
      (sourceFace root visit u7 calculus reader face (frame.depth+1)))

theorem after_payload
    (face : SourceNativeRootSemanticFaceAt root visit)
    (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
    (same : frame = {initial with depth := frame.depth})
    (cfg : Activation.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort)) :
    HEq (afterFace root visit u7 calculus reader face frame same cfg).rootRead face.rootRead :=
  (Transport.faceCast_payload cfg
    (left := frameAt root visit u7 calculus reader (frame.depth+1)) (right := frame.mathNext)
    (next_frame root visit u7 calculus reader frame same).symm _).trans
      ((Transport.shared_payload _ cfg _).trans (source_payload root visit u7 calculus reader face (frame.depth+1)))

variable (event : ExactTemporalCausalRootEventAt (S.root frame cfg).toAuthoritativeRoot.toLedgerRoot (S.visit frame cfg))
noncomputable def targetFace
    (face : SourceNativeRootSemanticFaceAt root visit)
    (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
    (same : frame = {initial with depth := frame.depth})
    (cfg : Activation.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
    (event : ExactTemporalCausalRootEventAt (S.root frame cfg).toAuthoritativeRoot.toLedgerRoot (S.visit frame cfg)) :=
  Transport.bornFace frame cfg event (afterFace root visit u7 calculus reader face frame same cfg)

theorem target_payload
    (face : SourceNativeRootSemanticFaceAt root visit)
    (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
    (same : frame = {initial with depth := frame.depth})
    (cfg : Activation.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
    (event : ExactTemporalCausalRootEventAt (S.root frame cfg).toAuthoritativeRoot.toLedgerRoot (S.visit frame cfg)) :
    type_of% ((Transport.born_payload frame cfg event
    (afterFace root visit u7 calculus reader face frame same cfg)).trans
      (after_payload root visit u7 calculus reader face frame same cfg)) :=
  (Transport.born_payload frame cfg event (afterFace root visit u7 calculus reader face frame same cfg)).trans
    (after_payload root visit u7 calculus reader face frame same cfg)

end Retained

end OriginalConstantFourierRetainedFace
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
