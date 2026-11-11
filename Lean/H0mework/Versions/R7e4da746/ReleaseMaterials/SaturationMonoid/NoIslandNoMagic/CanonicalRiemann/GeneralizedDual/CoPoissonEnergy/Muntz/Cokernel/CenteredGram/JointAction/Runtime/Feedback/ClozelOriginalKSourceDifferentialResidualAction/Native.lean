import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceDifferentialResidualAction.Action
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialResidualAction
open Complex BurnolPhysicalState
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Whole
export OriginalKSourceDifferentialAction.Prior
 (sourcePacketWhole sourcePacketWholeTotal source_packet_whole_total source_actual_native_total source_actual_born_write)
end Whole
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local instance completeNativeBaseGroups (initial : Nat) : ∀ target,AddCommGroup (L.Value (PairValue OriginalR.C.Value) initial target) :=
 L.groups (PairValue OriginalR.C.Value) initial
local instance completeNativeOriginGroups (initial origin : Nat) : ∀ target,AddCommGroup
 (L.Value (L.Value (PairValue OriginalR.C.Value) initial) origin target) :=
 L.groups (L.Value (PairValue OriginalR.C.Value) initial) origin
local instance completeNativeRuntimeGroups (initial origin grade : Nat) : ∀ target,AddCommGroup
 (L.Value (L.Value (L.Value (PairValue OriginalR.C.Value) initial) origin) grade target) :=
 L.groups (L.Value (L.Value (PairValue OriginalR.C.Value) initial) origin) grade
variable (initial origin : Nat)
variable (mother : SF.Factory (L.Value (L.Value (PairValue OriginalR.C.Value) initial) origin) OriginalR.C.Var ())

/-- The original R acts on the same actual registered source residual; old residual words and complete inherited callbacks remain. -/
def completeResidualRFactory : SF.Factory (L.Value (L.Value (PairValue OriginalR.C.Value) initial) origin) OriginalR.C.Var () :=
 let stocked:=sourceResidualStockFactory mother
 {stocked with datum:=fun grade seed frame=>
  {stocked.datum grade seed frame with calculationReader:=some (fun {_current} supplied=>
   ⟨sourceResidualEnvironment frame supplied,
    completeResidualRCode observation nontrivial half initial origin grade frame supplied⟩)}}

variable (packet : AS.AdmissionPacket (W:=L.Value (L.Value (PairValue OriginalR.C.Value) initial) origin) (X:=OriginalR.C.Var) (s:=()))

def completeResidualRPacket : AS.AdmissionPacket (W:=L.Value (L.Value (PairValue OriginalR.C.Value) initial) origin) (X:=OriginalR.C.Var) (s:=()) :=
 ⟨packet.1,packet.2.1,SF.cfg (completeResidualRFactory observation nontrivial half initial origin mother) packet.1 packet.2.1.2,⟨rfl⟩⟩

def completeResidualRMaterial := R.actualMaterial packet.2.1.1
 (SF.cfg (completeResidualRFactory observation nontrivial half initial origin mother) packet.1 packet.2.1.2)

def completeResidualRWhole := Whole.sourcePacketWhole
 (completeResidualRFactory observation nontrivial half initial origin mother) (completeResidualRPacket observation nontrivial half initial origin mother packet)

def completeResidualRWholeTotal : PairValue (L.Value (L.Value (L.Value (PairValue OriginalR.C.Value) initial) origin) packet.1) () := Whole.sourcePacketWholeTotal
 (completeResidualRFactory observation nontrivial half initial origin mother) (completeResidualRPacket observation nontrivial half initial origin mother packet)

def completeResidualRInherited := (completeResidualRMaterial observation nontrivial half initial origin mother packet).raw.effect
 (completeResidualRMaterial observation nontrivial half initial origin mother packet).environment
 (completeResidualRMaterial observation nontrivial half initial origin mother packet).increment

def completeResidualRReceived := completeResidualRWholeTotal observation nontrivial half initial origin mother packet-
 completeResidualRInherited observation nontrivial half initial origin mother packet

/-- The real whole source environment/expression and received endpoint restore every R source fee before its physical read. -/
theorem complete_R_whole_complete :
 completeResidualRWholeTotal observation nontrivial half initial origin mother packet=
 (completeResidualRMaterial observation nontrivial half initial origin mother packet).raw.eval
  (completeResidualRMaterial observation nontrivial half initial origin mother packet).environment+
 completeResidualRInherited observation nontrivial half initial origin mother packet :=
 (Whole.source_packet_whole_total _ _).trans ((Whole.source_actual_native_total _ _).trans (Expr.eval_update _ _ _))

/-- The actual inherited source increment is acted on by the same original R, with no field erased. -/
theorem complete_R_inherited_action :
 completeResidualRInherited observation nontrivial half initial origin mother packet=
 completeRSourceAction observation nontrivial half initial origin packet.1
 (completeResidualTotalRole initial origin packet.1
  ((sourceResidualCode (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)).effect
   (completeResidualRMaterial observation nontrivial half initial origin mother packet).environment
   (completeResidualRMaterial observation nontrivial half initial origin mother packet).increment)) :=
 complete_R_code_effect observation nontrivial half initial origin packet.1 _ _ _ _

/-- Both source relation roles are generated before their complete residual is acted on by R. -/
theorem complete_R_received_actual_relation :
 completeRSourceRead initial origin packet.1 (completeResidualRReceived observation nontrivial half initial origin mother packet)=
 OriginalR.variableAction observation nontrivial half
  (completeRSourceRead initial origin packet.1
   (completeResidualTotalRole initial origin packet.1
    ((sourceResidualCode (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)).eval
     (sourceResidualEnvironment (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1))))) := by
 have restored : completeResidualRReceived observation nontrivial half initial origin mother packet=
  (completeResidualRMaterial observation nontrivial half initial origin mother packet).raw.eval
   (completeResidualRMaterial observation nontrivial half initial origin mother packet).environment :=
  (congrArg (fun value=>value-completeResidualRInherited observation nontrivial half initial origin mother packet)
   (complete_R_whole_complete observation nontrivial half initial origin mother packet)).trans (add_sub_cancel_right _ _)
 exact (congrArg (completeRSourceRead initial origin packet.1) restored).trans
  (complete_R_code_read observation nontrivial half initial origin packet.1 _ _)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialResidualAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
