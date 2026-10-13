import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNativeSourceReturn.Writeback
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNativeSourceReturn.Readback
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.EnvironmentUpdate.CurrentMaterial.RootedEffect.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNativeSourceReturn
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace SF
export OriginalKFiniteWard.SF (Factory)
end SF
open Complex MeasureTheory Set Filter
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace Pay
export SourceFamilyActualCurrentMaterialRootedEffect
  (born_actual_payment born_payment_whole_destination born_payment_entry born_payment_ledger born_payment_step)
end Pay

local instance paymentGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target

private theorem payment_born_at
    (factory : SF.Factory (PairValue C.Value) C.Var ())
    (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) :
    ActualNativeBornSourceEffect.born (Native.selected factory packet)
      (Native.nativePacket factory packet).2.2.1 =
      (Native.sourceBorn factory packet).2.1.1 := rfl

private theorem payment_at
    (factory : SF.Factory (PairValue C.Value) C.Var ())
    (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) : type_of%
    (Pay.born_payment_whole_destination (Native.selected factory packet)
      (Native.nativePacket factory packet).2.2.1) :=
  Pay.born_payment_whole_destination (Native.selected factory packet)
    (Native.nativePacket factory packet).2.2.1

private theorem payment_entry_at
    (factory : SF.Factory (PairValue C.Value) C.Var ())
    (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) : type_of%
    (Pay.born_payment_entry (Native.selected factory packet)
      (Native.nativePacket factory packet).2.2.1) :=
  Pay.born_payment_entry (Native.selected factory packet)
    (Native.nativePacket factory packet).2.2.1

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

theorem actual_action_payment_born (ordinal : Nat) : type_of%
    (payment_born_at (returnFactory observation nontrivial half) (returnPacket observation nontrivial half depth ordinal)) :=
  payment_born_at (returnFactory observation nontrivial half) (returnPacket observation nontrivial half depth ordinal)

theorem actual_action_payment (ordinal : Nat) : type_of%
    (payment_at (returnFactory observation nontrivial half) (returnPacket observation nontrivial half depth ordinal)) :=
  payment_at (returnFactory observation nontrivial half) (returnPacket observation nontrivial half depth ordinal)

theorem actual_action_payment_entry (ordinal : Nat) : type_of%
    (payment_entry_at (returnFactory observation nontrivial half) (returnPacket observation nontrivial half depth ordinal)) :=
  payment_entry_at (returnFactory observation nontrivial half) (returnPacket observation nontrivial half depth ordinal)

theorem actual_input_stage_payment_born (ordinal : Nat) : type_of%
    (payment_born_at (returnFactory observation nontrivial half)
      (returnParent observation nontrivial half depth ordinal)) :=
  payment_born_at (returnFactory observation nontrivial half) _

theorem actual_input_stage_payment (ordinal : Nat) : type_of%
    (payment_at (returnFactory observation nontrivial half)
      (returnParent observation nontrivial half depth ordinal)) :=
  payment_at (returnFactory observation nontrivial half) _

theorem actual_input_stage_payment_entry (ordinal : Nat) : type_of%
    (payment_entry_at (returnFactory observation nontrivial half)
      (returnParent observation nontrivial half depth ordinal)) :=
  payment_entry_at (returnFactory observation nontrivial half) _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNativeSourceReturn
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
