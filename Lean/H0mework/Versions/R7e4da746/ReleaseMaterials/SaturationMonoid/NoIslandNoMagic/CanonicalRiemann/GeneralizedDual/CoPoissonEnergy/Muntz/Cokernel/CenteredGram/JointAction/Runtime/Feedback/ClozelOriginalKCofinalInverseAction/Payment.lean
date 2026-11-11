import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalInverseAction.Consumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalInverseAction.Readback
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.EnvironmentUpdate.CurrentMaterial.RootedEffect.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalInverseAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
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

theorem actual_inverse_payment_born (ordinal : Nat) : type_of%
    (payment_born_at (factory observation nontrivial half) (actionPacket observation nontrivial half depth ordinal)) :=
  payment_born_at (factory observation nontrivial half) (actionPacket observation nontrivial half depth ordinal)

theorem actual_inverse_payment (ordinal : Nat) : type_of%
    (payment_at (factory observation nontrivial half) (actionPacket observation nontrivial half depth ordinal)) :=
  payment_at (factory observation nontrivial half) (actionPacket observation nontrivial half depth ordinal)

theorem actual_inverse_payment_entry (ordinal : Nat) : type_of%
    (payment_entry_at (factory observation nontrivial half) (actionPacket observation nontrivial half depth ordinal)) :=
  payment_entry_at (factory observation nontrivial half) (actionPacket observation nontrivial half depth ordinal)

theorem consume_actual_inverse (ordinal : Nat) :
    type_of% (parent_compiles observation nontrivial half depth ordinal) ∧
    type_of% (parent_whole observation nontrivial half depth ordinal) ∧
    type_of% (parent_next observation nontrivial half depth ordinal) ∧
    type_of% (actual_admitted_input observation nontrivial half depth ordinal) ∧
    type_of% (actual_R_born_input observation nontrivial half depth ordinal) ∧
    type_of% (actual_inverse_readback observation nontrivial half depth ordinal) ∧
    type_of% (actual_inverse_write observation nontrivial half depth ordinal) ∧
    type_of% (actual_inverse_born_environment observation nontrivial half depth ordinal) ∧
    type_of% (inverse_compiles observation nontrivial half depth ordinal) ∧
    type_of% (inverse_whole observation nontrivial half depth ordinal) ∧
    type_of% (inverse_next observation nontrivial half depth ordinal) ∧
    type_of% (actual_inverse_payment_born observation nontrivial half depth ordinal) ∧
    type_of% (actual_inverse_payment observation nontrivial half depth ordinal) ∧
    type_of% (actual_inverse_payment_entry observation nontrivial half depth ordinal) :=
  ⟨parent_compiles _ _ _ _ _, parent_whole _ _ _ _ _, parent_next _ _ _ _ _,
    actual_admitted_input _ _ _ _ _, actual_R_born_input _ _ _ _ _, actual_inverse_readback _ _ _ _ _,
    actual_inverse_write _ _ _ _ _, actual_inverse_born_environment _ _ _ _ _,
    inverse_compiles _ _ _ _ _, inverse_whole _ _ _ _ _, inverse_next _ _ _ _ _,
    actual_inverse_payment_born _ _ _ _ _, actual_inverse_payment _ _ _ _ _, actual_inverse_payment_entry _ _ _ _ _⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalInverseAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
