import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.PaidPrefix
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.ExactCurrent

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.PaidPrefix
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace PP
export ActualNativePaidPrefix
 (length current history paidMacro macro_target payment_whole_destination actual_tick_receipt suffix_stop)
end PP
namespace IC
export ActualCofinalSourceAction (nativePacket native_packet_actual receiver_ast)
end IC
namespace Prefix
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix (receipt_distance_exact)
end Prefix
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial)
end R
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (budget)
end N
local instance packetGroups (grade : Nat) : ∀ target, AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade

private theorem native_length_positive (factory : ActualSourceSegmentBornEffect.SF.Factory (PairValue C.Value) C.Var ()) (packet : ActualNativePaidPrefix.AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) :
 0 < PP.length (AS.nativeAfterAdmission factory packet) := by
 rcases packet with ⟨grade,data,configuration,⟨sameVar⟩⟩
 cases configuration with
 | mk lowVar datum inventory pairInventory =>
  change lowVar = C.Var at sameVar
  cases sameVar
  let packet : ActualNativePaidPrefix.AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()) := ⟨grade,data,⟨C.Var,datum,inventory,pairInventory⟩,⟨rfl⟩⟩
  let native := IC.nativePacket factory packet
  change 0 < (AS.localNativeReceipt native).1
  have distance : (AS.localNativeReceipt native).1 = remaining native.2.1.1.event.state.1 :=
   Prefix.receipt_distance_exact (AS.stockCfg native.2.2.1) native.2.1.1 0
  rw [distance]
  have credit := SourceRegisteredClaimClock.remainder_generated native.2.1.1
  have fee := N.budget (R.actualMaterial packet.2.1.1 packet.2.2.1)
  have ast := congrArg remaining (IC.receiver_ast factory packet)
  have depth : native.2.1.1.depth = 0 := rfl
  change remaining native.2.1.1.event.state.1 = remaining native.2.1.1.registered.input.expression - (native.2.1.1.depth+1) at credit
  have sourceBound : 2 ≤ remaining
   (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression
    (R.actualMaterial packet.2.1.1 packet.2.2.1)) := by omega
  have inputBound : 2 ≤ remaining native.2.1.1.registered.input.expression :=
   le_of_le_of_eq sourceBound ast.symm
  have clock := congrArg (fun value : Nat => remaining native.2.1.1.registered.input.expression - (value+1)) depth
  have remainder : remaining native.2.1.1.event.state.1 = remaining native.2.1.1.registered.input.expression - 1 :=
   credit.trans clock
  omega

attribute [local irreducible] AS.localNativeReceipt
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "native" => originalNative observation nontrivial half depth (ordinal+1)

def originalOffset : Fin (PP.length native) :=
 ⟨0,native_length_positive (D.factory observation nontrivial half)
  (originalPredecessor observation nontrivial half depth (ordinal+1))⟩

def originalHistory := PP.history native
def originalMacro := PP.paidMacro native (originalOffset observation nontrivial half depth ordinal)

/-- The complete original paid prefix reaches its literal stop, with every whole-row receipt. -/
theorem original_paid_stop :
 (originalMacro observation nontrivial half depth ordinal).target = PP.current native (PP.length native) ∧
 (∀ offset, type_of% (PP.payment_whole_destination native offset)) ∧
 (∀ offset, type_of% (PP.actual_tick_receipt native offset)) ∧
 (type_of% (PP.suffix_stop native)) ∧
 (type_of% (ExactCurrent.original_selected_current observation nontrivial half depth (ordinal+1))) :=
 ⟨PP.macro_target native (originalOffset observation nontrivial half depth ordinal),
  PP.payment_whole_destination native, PP.actual_tick_receipt native, PP.suffix_stop native,
  ExactCurrent.original_selected_current observation nontrivial half depth (ordinal+1)⟩

end OriginalKCofinalFullBranchFibre.KernelWrite.PaidPrefix
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
