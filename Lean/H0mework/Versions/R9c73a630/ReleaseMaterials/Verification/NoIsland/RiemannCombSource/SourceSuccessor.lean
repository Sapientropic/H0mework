import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceSuccessor

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift RootInquiryCompletion CofinalHistorySettlement
namespace SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor
attribute [local instance] levelGroups
section Direct
variable {W X : Unit → Type} [∀ t, AddCommGroup (W t)]
variable (factory : SF.Factory W X ()) (n : Nat)
variable (data : SF.Packet (W := W) (X := X) (s := ()) n)
variable (sourceCfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := ()))
variable (language : sourceCfg.LowVar = X)
example : type_of% (actual_compiles factory n data sourceCfg language) := actual_compiles _ _ _ _ _
example : type_of% (actual_whole factory n data sourceCfg language) := actual_whole _ _ _ _ _
example : type_of% (actual_next factory n data sourceCfg language) := actual_next _ _ _ _ _
example : type_of% (actual_target_root factory n data sourceCfg language) := actual_target_root _ _ _ _ _
example : type_of% (calculation_target_root factory n data sourceCfg language) := calculation_target_root _ _ _ _ _
example (event : SourceGeneratedInquiryReceiptAction.Configured.Event data.1 sourceCfg) :
    type_of% (target_first_source factory n data sourceCfg language event) := target_first_source _ _ _ _ _ event
example : type_of% (installed_decoder factory n data sourceCfg language) := installed_decoder _ _ _ _ _
example : type_of% (receiver_inventories factory n data sourceCfg language) := receiver_inventories _ _ _ _ _
example : type_of% (updated_total factory n data sourceCfg language) := updated_total _ _ _ _ _
example : type_of% (full_frame factory n data sourceCfg language) := full_frame _ _ _ _ _
example : type_of% (born_inventories factory n data sourceCfg language) := born_inventories _ _ _ _ _
example : type_of% (successor_registered_present factory n data sourceCfg language) := successor_registered_present _ _ _ _ _
example : type_of% (second_decoder factory n data sourceCfg language) := second_decoder _ _ _ _ _
example : type_of% (@second_writeback _ _ _ factory n data sourceCfg language) := @second_writeback _ _ _ factory n data sourceCfg language
example (bound : Nat) : type_of% (cofinal factory n data sourceCfg language bound) := cofinal _ _ _ _ _ bound
example (word : SourceOperationInquiry.Carrier (S.runtime (receiver factory n data sourceCfg language)
    (nextCfg factory n data sourceCfg language))) : type_of% (complete_word factory n data sourceCfg language word) :=
  complete_word _ _ _ _ _ word
end Direct
namespace Controls
abbrev ScalarValue := fun _ : Unit => ℤ
abbrev ScalarVar := fun _ : Unit => Unit
abbrev ScalarFrame := A.M.Frame (Value := ScalarValue) (Var := ScalarVar) (sort := ())
namespace Family
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily
  (defaultFactory)
end Family
def factory : SF.Factory ScalarValue ScalarVar () := { Family.defaultFactory ScalarValue ScalarVar () with
  datum := fun _ _ frame => { component := none, reader := fun {_current} _supplied =>
    ⟨(fun _ slot => (frame.activeEnvironment () slot, 0)), .var ()⟩ } }
def sourceCfg : A.Programme (PhysicalValue := ScalarValue) (PhysicalVar := ScalarVar) (sort := ()) where
  LowVar := ScalarVar
  datum _ := { component := none, reader := fun {_current} _supplied => ⟨0, .const ((1 : ℤ), (0 : ℤ))⟩ }
variable (frame : ScalarFrame)
def data : SF.Packet (W := ScalarValue) (X := ScalarVar) (s := ()) 0 :=
  ⟨frame, RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator frame.registered.input.expression)⟩
theorem first_old_paid : oldPair 0 (data frame) sourceCfg = ((1 : ℤ), (0 : ℤ)) :=
  (SourceGeneratedInquiryReceiptAction.Configured.Writeback.old_paid_value frame sourceCfg).trans rfl
theorem first_native_zero : nativeValue factory 0 (data frame) sourceCfg rfl = 0 := by
  have same : (N.input (sourceMaterial 0 (data frame) sourceCfg)).environment =
      (sourceMaterial 0 (data frame) sourceCfg).environment := by
    change (0 : Env (fun _ : Unit => ℤ × ℤ) ScalarVar) + (0 - 0) = 0
    abel
  exact (native_value factory 0 (data frame) sourceCfg rfl).trans
    ((congrArg (fun environment => (N.expression (sourceMaterial 0 (data frame) sourceCfg)).eval environment) same).trans
      (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.old_value (sourceMaterial 0 (data frame) sourceCfg)))
theorem first_written : (born factory 0 (data frame) sourceCfg rfl).activeEnvironment () () = ((1 : ℤ), (0 : ℤ)) := by
  have active := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.active
    (born_environment factory 0 (data frame) sourceCfg rfl)
  have point := congrArg (fun environment : Env (fun _ : Unit => ℤ × ℤ) ScalarVar => environment () ()) active
  exact point.trans ((congrArg (fun value : ℤ × ℤ => (show ℤ × ℤ from oldPair 0 (data frame) sourceCfg) + value)
    (first_native_zero frame)).trans ((add_zero _).trans (first_old_paid frame)))
theorem second_old_paid : successorOldPaid factory 0 (data frame) sourceCfg rfl =
    (((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (0 : ℤ))) :=
  (SourceGeneratedInquiryReceiptAction.Configured.Writeback.old_paid_value
    (successorPacket factory 0 (data frame) sourceCfg rfl).1
    (nextCfg factory 0 (data frame) sourceCfg rfl)).trans
      (congrArg (fun value : ℤ × ℤ => (value, (0 : ℤ × ℤ))) (first_written frame))
example : successorOldPaid factory 0 (data frame) sourceCfg rfl ≠ (0 : (ℤ × ℤ) × (ℤ × ℤ)) := by
  rw [second_old_paid]
  change (((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (0 : ℤ))) ≠ (((0 : ℤ), (0 : ℤ)), ((0 : ℤ), (0 : ℤ)))
  intro same
  have impossible := congrArg (fun value : (ℤ × ℤ) × (ℤ × ℤ) => value.1.1) same
  norm_num at impossible
example : type_of% (second_decoder factory 0 (data frame) sourceCfg rfl) := second_decoder _ _ _ _ _
example : type_of% (@second_writeback _ _ _ factory 0 (data frame) sourceCfg rfl) := @second_writeback _ _ _ factory 0 (data frame) sourceCfg rfl
#print axioms first_written
#print axioms second_old_paid
end Controls
#print axioms decoder_source
#print axioms reader_preserved
#print axioms calculation_reader_preserved
#print axioms inventories_preserved
#print axioms actual_compiles
#print axioms actual_whole
#print axioms actual_next
#print axioms actual_target_root
#print axioms calculation_target_root
#print axioms target_first_source
#print axioms installed_decoder
#print axioms receiver_inventories
#print axioms native_value
#print axioms updated_total
#print axioms actual_writeback
#print axioms frames_born
#print axioms full_frame
#print axioms born_inventories
#print axioms successor_registered_present
#print axioms second_decoder
#print axioms second_writeback
#print axioms cofinal
#print axioms complete_word
end SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombSourceSuccessor
open NoIslandNoMagic.CanonicalRiemann
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (depth : Nat)
variable (half : NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)
example : type_of% (source_compiles observation nontrivial depth half) := source_compiles _ _ _ _
example : type_of% (source_whole observation nontrivial depth half) := source_whole _ _ _ _
example : type_of% (source_next observation nontrivial depth half) := source_next _ _ _ _
example : type_of% (actual_full_frame observation nontrivial depth half) := actual_full_frame _ _ _ _
example : type_of% (@actual_born_pair observation nontrivial depth half) := @actual_born_pair observation nontrivial depth half
example : type_of% (next_source_decoder observation nontrivial depth half) := next_source_decoder _ _ _ _
example : type_of% (@next_source_writeback observation nontrivial depth half) := @next_source_writeback observation nontrivial depth half
example (bound : Nat) : type_of% (sourceCofinal observation nontrivial depth half bound) := sourceCofinal _ _ _ _ bound
#print axioms actual_born_pair
#print axioms next_source_writeback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombSourceSuccessor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
