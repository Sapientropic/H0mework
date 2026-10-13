import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullSourceRAction.Writeback
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullSourceRAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace SF
export OriginalKFiniteWard.SF (Factory)
end SF
namespace AN
export ActualNativeRelationTransport (new_relation_in_born new_relation_face new_cochain_face new_differential new_completion_zero new_full_trace)
end AN
namespace Native
export ActualCofinalSourceAction (born_inventory born_pair_inventory source_word_action_inventory source_word_action_substitution
  bornStock bornPairStock old_event_in_born old_pair_event_in_born sourceLiftEvent sourceLiftPairEvent selected nativePacket)
end Native
local instance inventoryGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target

private theorem boundary_at
    (producer : SF.Factory (PairValue C.Value) C.Var ())
    (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) : type_of%
    (AN.new_relation_in_born (Native.selected producer packet) (Native.nativePacket producer packet).2.2.1) :=
  AN.new_relation_in_born (Native.selected producer packet) (Native.nativePacket producer packet).2.2.1

private theorem faces_at
    (producer : SF.Factory (PairValue C.Value) C.Var ())
    (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) : type_of%
    (AN.new_relation_face (Native.selected producer packet)) ∧ type_of%
    (AN.new_cochain_face (Native.selected producer packet)) ∧ type_of%
    (AN.new_differential (Native.selected producer packet)) ∧ type_of%
    (AN.new_completion_zero (Native.selected producer packet)) :=
  ⟨AN.new_relation_face _,AN.new_cochain_face _,AN.new_differential _,AN.new_completion_zero _⟩

private theorem trace_at
    (producer : SF.Factory (PairValue C.Value) C.Var ())
    (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) : type_of%
    (AN.new_full_trace (Native.selected producer packet)) :=
  AN.new_full_trace (Native.selected producer packet)

variable (observation : NoIslandNoMagic.CanonicalRiemann.GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

theorem actual_R_boundary_in_born (ordinal : Nat) : type_of%
    (boundary_at (factory observation nontrivial half) (actionPacket observation nontrivial half depth ordinal)) :=
  boundary_at _ _

theorem actual_R_four_faces (ordinal : Nat) : type_of%
    (faces_at (factory observation nontrivial half) (actionPacket observation nontrivial half depth ordinal)) :=
  faces_at _ _

theorem actual_R_full_trace (ordinal : Nat) : type_of%
    (trace_at (factory observation nontrivial half) (actionPacket observation nontrivial half depth ordinal)) :=
  trace_at _ _

theorem actual_R_born_inventory (ordinal : Nat) : type_of%
    (Native.born_inventory (factory observation nontrivial half) (actionPacket observation nontrivial half depth ordinal)) :=
  Native.born_inventory _ _

theorem actual_R_word_inventory (ordinal : Nat) : type_of%
    (Native.source_word_action_inventory (factory observation nontrivial half) (actionPacket observation nontrivial half depth ordinal)) :=
  Native.source_word_action_inventory _ _

theorem actual_R_joint_inventory (ordinal : Nat) : type_of%
    (Native.born_pair_inventory (factory observation nontrivial half) (actionPacket observation nontrivial half depth ordinal)) :=
  Native.born_pair_inventory _ _

theorem actual_R_keeps_previous_inventory (ordinal : Nat)
    (prior : RootedAccountedUnfolding (PresentedRelationEventAt
      (Expr (L.Value (PairValue C.Value) (actionPacket observation nontrivial half depth ordinal).1) C.Var ())))
    (present : (actionPacket observation nontrivial half depth ordinal).2.1.1.inventory=some prior)
    (event) (belongs : event∈prior.trace) : type_of%
    (Native.old_event_in_born (factory observation nontrivial half)
      (actionPacket observation nontrivial half depth ordinal) prior present event belongs) :=
  Native.old_event_in_born _ _ prior present event belongs

theorem actual_R_keeps_previous_joint_inventory (ordinal : Nat)
    (prior : RootedAccountedUnfolding (PresentedRelationEventAt
      (Expr (PairValue (L.Value (PairValue C.Value) (actionPacket observation nontrivial half depth ordinal).1)) C.Var ())))
    (present : (actionPacket observation nontrivial half depth ordinal).2.1.1.pairInventory=some prior)
    (event) (belongs : event∈prior.trace) : type_of%
    (Native.old_pair_event_in_born (factory observation nontrivial half)
      (actionPacket observation nontrivial half depth ordinal) prior present event belongs) :=
  Native.old_pair_event_in_born _ _ prior present event belongs

theorem actual_input_boundary_in_born (ordinal : Nat) : type_of%
    (boundary_at (factory observation nontrivial half) (parentPacket observation nontrivial half depth ordinal)) :=
  boundary_at _ _

theorem actual_input_four_faces (ordinal : Nat) : type_of%
    (faces_at (factory observation nontrivial half) (parentPacket observation nontrivial half depth ordinal)) :=
  faces_at _ _

theorem actual_input_full_trace (ordinal : Nat) : type_of%
    (trace_at (factory observation nontrivial half) (parentPacket observation nontrivial half depth ordinal)) :=
  trace_at _ _

theorem actual_input_word_inventory (ordinal : Nat) : type_of%
    (Native.source_word_action_inventory (factory observation nontrivial half) (parentPacket observation nontrivial half depth ordinal)) :=
  Native.source_word_action_inventory _ _

theorem actual_R_word_substitution (ordinal : Nat)
    (binding : ∀ target, C.Var target → Expr (L.Value (PairValue C.Value)
      (actionPacket observation nontrivial half depth ordinal).1) C.Var target) : type_of%
    (Native.source_word_action_substitution (actionPacket observation nontrivial half depth ordinal) binding) :=
  Native.source_word_action_substitution _ binding

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullSourceRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

