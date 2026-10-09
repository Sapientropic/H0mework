import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRegisteredSourceFeed
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombConfiguredPairWriteback
open SourceGeneratedInquiryReceiptAction.Configured.Writeback
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift RootInquiryCompletion
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace F
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombRegisteredSourceFeed
  (recoveredBorn configuration projected next_action_source next_registered_value registered_environment next_paid_trace next_paid_R_state next_complete_raw)
end F
namespace P
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombPhysicalAction
  (R code physicalProjection physicalRemainder)
end P
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (depth : Nat)
variable (half : NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)
attribute [local irreducible] P.code

def sourceFrame := F.recoveredBorn observation nontrivial depth half
def sourceConfiguration := F.configuration observation nontrivial half
namespace C
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombReceiptFeedback (Value Var)
end C

def writePair (value : BurnolL2 × BurnolL2) : Env (PairValue C.Value)
    (F.configuration observation nontrivial half).LowVar := fun _ _ => value

def sourceBorn := born (sourceFrame observation nontrivial depth half) (sourceConfiguration observation nontrivial half)
  (writePair observation nontrivial half)

theorem native_zero : nativeValue (sourceFrame observation nontrivial depth half)
    (sourceConfiguration observation nontrivial half) (writePair observation nontrivial half) = (0 : BurnolL2 × BurnolL2) := by
  let source := sourceFrame observation nontrivial depth half
  let configuration := sourceConfiguration observation nontrivial half
  have before : (material source configuration).environment =
      (fun _ _ => (F.projected observation nontrivial depth half, (0 : BurnolL2))) :=
    congrArg (fun raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
      (Value := PairValue C.Value) (Var := C.Var) (sort := ()) => raw.environment)
      (F.next_action_source observation nontrivial depth half)
  have same : (N.input (material source configuration)).environment = (material source configuration).environment :=
    (F.registered_environment observation nontrivial depth half).trans before.symm
  exact (native_value source configuration (writePair observation nontrivial half)).trans
    ((congrArg (fun environment => (N.expression (material source configuration)).eval environment) same).trans
      (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.old_value (material source configuration)))

theorem written_pair : oldPaid (sourceFrame observation nontrivial depth half)
      (sourceConfiguration observation nontrivial half) +
    nativeValue (sourceFrame observation nontrivial depth half) (sourceConfiguration observation nontrivial half)
      (writePair observation nontrivial half) =
      (P.physicalProjection ((P.R observation nontrivial half) (F.projected observation nontrivial depth half)),
       P.physicalRemainder ((P.R observation nontrivial half) (F.projected observation nontrivial depth half))) := by
  have literal := congrArg (fun raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value := PairValue C.Value) (Var := C.Var) (sort := ()) => raw.expression.eval raw.environment)
      (F.next_action_source observation nontrivial depth half)
  have arithmetic : (P.code observation nontrivial half).eval
      (fun _ _ => (F.projected observation nontrivial depth half, (0 : BurnolL2))) =
        (P.physicalProjection ((P.R observation nontrivial half) (F.projected observation nontrivial depth half)),
         P.physicalRemainder ((P.R observation nontrivial half) (F.projected observation nontrivial depth half))) := by
    unfold P.code
    rfl
  have original := ((old_paid_value (sourceFrame observation nontrivial depth half)
    (sourceConfiguration observation nontrivial half)).trans literal).trans arithmetic

  exact (congrArg (fun value : BurnolL2 × BurnolL2 =>
    oldPaid (sourceFrame observation nontrivial depth half) (sourceConfiguration observation nontrivial half) + value)
      (native_zero observation nontrivial depth half)).trans ((add_zero _).trans original)

theorem actual_born_pair :
    SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.At
      (sourceBorn observation nontrivial depth half)
      (fun _ _ =>
        (P.physicalProjection ((P.R observation nontrivial half) (F.projected observation nontrivial depth half)),
         P.physicalRemainder ((P.R observation nontrivial half) (F.projected observation nontrivial depth half)))) := by
  intro current occurrence
  exact ((born_environment (sourceFrame observation nontrivial depth half)
    (sourceConfiguration observation nontrivial half) (writePair observation nontrivial half)) occurrence).trans
    (congrArg (fun value : BurnolL2 × BurnolL2 => fun _target _coordinate => value)
      (written_pair observation nontrivial depth half))
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombConfiguredPairWriteback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
