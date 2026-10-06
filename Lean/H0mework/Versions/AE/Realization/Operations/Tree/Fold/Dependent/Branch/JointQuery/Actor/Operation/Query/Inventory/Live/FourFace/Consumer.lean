import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.FourFace.Source
import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Payment.Consumer
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Reverse.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.FourFace
open CategoryTheory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationInquiry SourceOperationInquiry.Context
open RootLawDependentJointStateController
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
theorem dual_readback (stage : Nat) : (faces root visit recognition U7 calculus stage).embedding.comp
    (faces root visit recognition U7 calculus stage).canonical=pairing root visit recognition U7 calculus :=
  UnifiedFourFace.generated_dual_readback (faceInput root visit recognition U7 calculus stage)
theorem same_occurrence (stage : Nat) : (faceInput root visit recognition U7 calculus stage).occurrence.root.1=
    occurrence root visit recognition U7 calculus stage := rfl
theorem raw_actual (stage : Nat) : type_of%
    (SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation.raw_actual
      (initial root visit recognition U7 calculus) (programme root visit recognition U7 calculus) stage) :=
  SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation.raw_actual _ _ stage
theorem source_equation (stage : Nat) : (frameAt root visit recognition U7 calculus stage).rawRead.expression.eval
    (frameAt root visit recognition U7 calculus (stage+1)).rawRead.environment=
    (Context.pairValue (runtime root visit recognition U7 calculus) (source root visit recognition U7 calculus)
      ((runtime root visit recognition U7 calculus).stateAt stage)).1+
    (Context.pairValue (runtime root visit recognition U7 calculus) (source root visit recognition U7 calculus)
      ((runtime root visit recognition U7 calculus).stateAt stage)).2 := by
  have value := Context.next_value (runtime root visit recognition U7 calculus) (source root visit recognition U7 calculus)
    ((runtime root visit recognition U7 calculus).stateAt stage)
  rw [raw_actual] at value
  exact (congrArg (fun environment => (frameAt root visit recognition U7 calculus stage).rawRead.expression.eval environment)
    (SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation.environment_actual
      (initial root visit recognition U7 calculus) (programme root visit recognition U7 calculus) (stage+1))).symm.trans value
theorem actual_operation (stage : Nat) : type_of% (Context.actual_operation_receipt
    (runtime root visit recognition U7 calculus) (source root visit recognition U7 calculus)
    ((runtime root visit recognition U7 calculus).stateAt stage)) := Context.actual_operation_receipt _ _ _
theorem actual_relation (stage : Nat) : type_of% (Context.Faces.actual_relation_transport
    (runtime root visit recognition U7 calculus) (source root visit recognition U7 calculus)
    ((runtime root visit recognition U7 calculus).stateAt stage)) := Context.Faces.actual_relation_transport _ _ _
theorem actual_field (stage : Nat) : type_of% (SourceOperationInquiry.actual_factorizes
    (runtime root visit recognition U7 calculus) ((runtime root visit recognition U7 calculus).stateAt stage)) :=
  SourceOperationInquiry.actual_factorizes _ _
theorem typed_receipt (stage : Nat) : type_of% (SourceOperationInquiry.actual_next_receipt
    (runtime root visit recognition U7 calculus) stage) := SourceOperationInquiry.actual_next_receipt _ stage
theorem cochain_zero (stage : Nat) : (cochain root visit recognition U7 calculus stage).d 0 1 ≫
    (cochain root visit recognition U7 calculus stage).d 1 2=0 := (cochain root visit recognition U7 calculus stage).d_comp_d 0 1 2
theorem inverse_read (stage : Nat) : type_of% (Context.Faces.Reverse.reverse_pair
    (runtime root visit recognition U7 calculus) (source root visit recognition U7 calculus)
    ((runtime root visit recognition U7 calculus).stateAt stage)) := Context.Faces.Reverse.reverse_pair _ _ _
theorem inverse_whole (stage : Nat) : type_of% (Context.Faces.Reverse.source_write
    (runtime root visit recognition U7 calculus) (source root visit recognition U7 calculus)
    ((runtime root visit recognition U7 calculus).stateAt stage)) := Context.Faces.Reverse.source_write _ _ _
theorem inverse_next (stage : Nat) : type_of% (Context.Faces.Reverse.source_next
    (runtime root visit recognition U7 calculus) (source root visit recognition U7 calculus)
    ((runtime root visit recognition U7 calculus).stateAt stage)) := Context.Faces.Reverse.source_next _ _ _
theorem macro_payment (stage : Nat) : type_of%
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.macro_current
      (programme root visit recognition U7 calculus) (initial root visit recognition U7 calculus) stage) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.macro_current _ _ stage
theorem no_refill (stage : Nat) : type_of%
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.no_refill
      (programme root visit recognition U7 calculus) (frameAt root visit recognition U7 calculus stage)) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.no_refill _ _
theorem noetherian (stage : Nat) : type_of%
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.wellFounded
      (programme root visit recognition U7 calculus) (frameAt root visit recognition U7 calculus stage)) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.wellFounded _ _

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.FourFace
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
