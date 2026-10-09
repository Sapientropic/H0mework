import H0mework.Versions.C62.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Acted.FourFace.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.FourFace
open CategoryTheory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationInquiry SourceOperationInquiry.Context
variable {T : Type u} {V Z : T → Type u} [∀ t,AddCommGroup (V t)] {t : T}
variable (seed : RootedAccountedUnfolding (CofinalHistorySettlement.PresentedRelationEventAt (Expr V Z t)))
variable (initial : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=V) (Var:=Z) (sort:=t))

theorem raw_actual (count : Nat) : type_of%
 (SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation.raw_actual initial (configuration seed) count) :=
 SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation.raw_actual _ _ count
theorem dual_readback (count : Nat) : (faces seed initial count).embedding.comp (faces seed initial count).canonical=pairing seed initial :=
 UnifiedFourFace.generated_dual_readback (faceInput seed initial count)
theorem same_occurrence (count : Nat) : (faceInput seed initial count).occurrence.root.1=occurrence seed initial count := rfl
theorem full_word (count : Nat) (word : words (V:=V) (Z:=Z) (t:=t)) :
 (logic seed initial count).symm (logic seed initial count word)=word :=
 (logic seed initial count).symm_apply_apply word
theorem cochain_zero (count : Nat) : (cochain seed initial count).d 0 1 ≫ (cochain seed initial count).d 1 2=0 :=
 (cochain seed initial count).d_comp_d 0 1 2
theorem actual_operation (count : Nat) : type_of% (Context.actual_operation_receipt
 (actualRuntime seed initial) (actualSource seed initial) ((actualRuntime seed initial).stateAt count)) :=
 Context.actual_operation_receipt _ _ _
theorem actual_relation (count : Nat) : type_of% (Context.Faces.actual_relation_transport
 (actualRuntime seed initial) (actualSource seed initial) ((actualRuntime seed initial).stateAt count)) :=
 Context.Faces.actual_relation_transport _ _ _
theorem complete_fibre (offset : Nat) (left right : words (V:=V) (Z:=Z) (t:=t)) : type_of% (Context.Faces.Cofinal.source_fibre
 (actualRuntime seed initial) (actualSource seed initial) offset left right) :=
 Context.Faces.Cofinal.source_fibre _ _ offset left right
theorem cofinal_next (offset : Nat) (word : words (V:=V) (Z:=Z) (t:=t)) : type_of% (Context.Faces.Cofinal.next_source
 (actualRuntime seed initial) (actualSource seed initial) offset word) :=
 Context.Faces.Cofinal.next_source _ _ offset word
theorem recover_source (word : carrier seed initial) :
 recover seed initial (SourceGeneratedPerfectification.canonicalMap (pairing seed initial) word)=word :=
 SourceGeneratedCompleteWordDual.recovery_source word
theorem action_source (word : carrier seed initial) :
 coimageAction seed initial (SourceGeneratedPerfectification.canonicalMap (pairing seed initial) word)=
 SourceGeneratedPerfectification.canonicalMap (pairing seed initial)
  (SourceOperationInquiry.sourceAction (actualRuntime seed initial) word) :=
 congrArg (fun value => SourceGeneratedPerfectification.canonicalMap (pairing seed initial)
  (SourceOperationInquiry.sourceAction (actualRuntime seed initial) value)) (recover_source seed initial word)
theorem actual_field (count : Nat) : type_of% (SourceOperationInquiry.actual_factorizes (actualRuntime seed initial)
 ((actualRuntime seed initial).stateAt count)) := SourceOperationInquiry.actual_factorizes _ _
theorem typed_receipt (count : Nat) : type_of% (SourceOperationInquiry.actual_next_receipt (actualRuntime seed initial) count) :=
 SourceOperationInquiry.actual_next_receipt _ count
theorem original_inverse_next (count : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Inverse.next_raw_actual
 seed (A.frames initial (configuration seed) count) (configuration seed) rfl rfl) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Inverse.next_raw_actual _ _ _ rfl rfl
theorem macro_payment (count : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.macro_current
  (configuration seed) initial count) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.macro_current _ _ count
theorem no_refill (count : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.no_refill
  (configuration seed) (A.frames initial (configuration seed) count)) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.no_refill _ _
theorem noetherian (count : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.wellFounded
  (configuration seed) (A.frames initial (configuration seed) count)) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.wellFounded _ _
theorem installed_request (count : Nat) :
 (A.query (A.frames initial (configuration seed) count) (configuration seed)).raw=(queryPacket seed initial count).rootRead.2.1 := rfl
theorem complete_query_trace (count : Nat) : SourceOperationPaidRelations.exposure
 (A.resultFace (A.frames initial (configuration seed) count) (configuration seed)).rootRead.2.1.2=
 SourceOperationPaidRelations.exposure (queryPacket seed initial count).rootRead.2.2.1.2.1.2 :=
 RootGeneratedDebtActivationJointSource.OwnerFree.common_raw_exposure
 (A.baseRoot (A.frames initial (configuration seed) count) (configuration seed)).toAuthoritativeRoot
 (A.actualVisit (A.frames initial (configuration seed) count)).current
 (SourceOperationInquiry.Context.Faces.Execution.Mother.baseState (X.epoch (A.frames initial (configuration seed) count))).root.toAuthoritativeRoot
 (A.actualVisit (A.frames initial (configuration seed) count)).current
 ((queryPacket seed initial count).rootRead.2.1)
theorem source_equation (count : Nat) :
 (A.frames initial (configuration seed) count).rawRead.expression.eval
 (A.frames initial (configuration seed) (count+1)).rawRead.environment=
 (Context.pairValue (actualRuntime seed initial) (actualSource seed initial) ((actualRuntime seed initial).stateAt count)).1+
 (Context.pairValue (actualRuntime seed initial) (actualSource seed initial) ((actualRuntime seed initial).stateAt count)).2 := by
 have value := Context.next_value (actualRuntime seed initial) (actualSource seed initial) ((actualRuntime seed initial).stateAt count)
 rw [raw_actual] at value
 exact (congrArg (fun environment => (A.frames initial (configuration seed) count).rawRead.expression.eval environment)
  (SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation.environment_actual initial (configuration seed) (count+1))).symm.trans value
end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.FourFace
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
