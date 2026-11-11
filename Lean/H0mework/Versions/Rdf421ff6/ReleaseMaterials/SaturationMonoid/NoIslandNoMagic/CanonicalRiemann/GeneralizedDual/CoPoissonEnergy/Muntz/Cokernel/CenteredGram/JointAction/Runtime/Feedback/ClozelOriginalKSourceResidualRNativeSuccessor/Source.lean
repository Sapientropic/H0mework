import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceDifferentialResidualAction.Original
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceResidualRNativeSuccessor
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Prior
export OriginalKSourceDifferentialResidualAction
 (completeResidualRFactory completeResidualRPacket completeResidualRWholeTotal completeResidualRMaterial
  completeResidualRInherited completeResidualRReceived complete_residual_R_action_acceptance)
namespace L
export OriginalKSourceDifferentialResidualAction.L (Value groups)
end L
namespace SF
export OriginalKSourceDifferentialResidualAction.SF (Factory cfg)
end SF
namespace AS
export OriginalKSourceDifferentialResidualAction.AS (AdmissionPacket)
end AS
namespace R
export OriginalKSourceDifferentialResidualAction.OriginalR.C (Value Var)
end R
end Prior
namespace Native
export ActualCofinalSourceAction
 (nativePacket sourceBorn selected receipt nativeValue born_inventory born_pair_inventory born_ast)
end Native
namespace AS
export ActualCofinalSourceAction.AS (write)
end AS
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (oldPaid)
end WB
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local instance nextBaseGroups (initial : Nat) : ∀ target,AddCommGroup (Prior.L.Value (PairValue Prior.R.Value) initial target) :=
 Prior.L.groups (PairValue Prior.R.Value) initial
local instance nextOriginGroups (initial origin : Nat) : ∀ target,AddCommGroup
 (Prior.L.Value (Prior.L.Value (PairValue Prior.R.Value) initial) origin target) :=
 Prior.L.groups (Prior.L.Value (PairValue Prior.R.Value) initial) origin
local instance nextRuntimeGroups (initial origin grade : Nat) : ∀ target,AddCommGroup
 (Prior.L.Value (Prior.L.Value (Prior.L.Value (PairValue Prior.R.Value) initial) origin) grade target) :=
 Prior.L.groups (Prior.L.Value (Prior.L.Value (PairValue Prior.R.Value) initial) origin) grade
variable (initial origin : Nat)
variable (mother : Prior.SF.Factory (Prior.L.Value (Prior.L.Value (PairValue Prior.R.Value) initial) origin) Prior.R.Var ())
variable (packet : Prior.AS.AdmissionPacket (W:=Prior.L.Value (Prior.L.Value (PairValue Prior.R.Value) initial) origin) (X:=Prior.R.Var) (s:=()))

/-- This complete packet is emitted by the previous actual residual-R native receipt, with its born source current and seed. -/
def residualRNextBornPacket : Prior.AS.AdmissionPacket
 (W:=Prior.L.Value (Prior.L.Value (PairValue Prior.R.Value) initial) origin) (X:=Prior.R.Var) (s:=()) :=
 Native.sourceBorn (Prior.completeResidualRFactory observation nontrivial half initial origin mother)
 (Prior.completeResidualRPacket observation nontrivial half initial origin mother packet)

/-- The next native grade is read from its actual emitted packet, preserving the complete base carrier. -/
theorem next_born_actual_grade :
 (residualRNextBornPacket observation nontrivial half initial origin mother packet).1=packet.1+1 := rfl

/-- The next source environment comes from the genuine previous writer's complete same-whole total. -/
theorem next_born_whole_environment :
 (residualRNextBornPacket observation nontrivial half initial origin mother packet).2.1.1.activeEnvironment=
 AS.write (Prior.completeResidualRFactory observation nontrivial half initial origin mother) packet.1 packet.2.1
  (Prior.SF.cfg (Prior.completeResidualRFactory observation nontrivial half initial origin mother) packet.1 packet.2.1.2) rfl
  (Prior.completeResidualRWholeTotal observation nontrivial half initial origin mother packet) := by
 have native:=ActualCofinalSourceAction.born_environment
  (Prior.completeResidualRFactory observation nontrivial half initial origin mother)
  (Prior.completeResidualRPacket observation nontrivial half initial origin mother packet)
 have total:=OriginalKSourceCofinalNativeSuccessor.source_packet_whole_total
  (Prior.completeResidualRFactory observation nontrivial half initial origin mother)
  (Prior.completeResidualRPacket observation nontrivial half initial origin mother packet)
 exact native.trans (congrArg (fun value=>AS.write
  (Prior.completeResidualRFactory observation nontrivial half initial origin mother) packet.1 packet.2.1
  (Prior.SF.cfg (Prior.completeResidualRFactory observation nontrivial half initial origin mother) packet.1 packet.2.1.2) rfl value) total.symm)

/-- The new current's literal registered AST is the actual previous native selected request, not an old epoch or a value-matched field. -/
theorem next_born_actual_expression : type_of%
 (Native.born_ast (Prior.completeResidualRFactory observation nontrivial half initial origin mother)
  (Prior.completeResidualRPacket observation nontrivial half initial origin mother packet)) := Native.born_ast _ _

/-- Both complete previous inventories are already installed in this emitted source packet. -/
theorem next_born_actual_inventory :
 (type_of% (Native.born_inventory (Prior.completeResidualRFactory observation nontrivial half initial origin mother)
  (Prior.completeResidualRPacket observation nontrivial half initial origin mother packet))) ∧
 (type_of% (Native.born_pair_inventory (Prior.completeResidualRFactory observation nontrivial half initial origin mother)
  (Prior.completeResidualRPacket observation nontrivial half initial origin mother packet))) :=
 ⟨Native.born_inventory _ _,Native.born_pair_inventory _ _⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceResidualRNativeSuccessor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
