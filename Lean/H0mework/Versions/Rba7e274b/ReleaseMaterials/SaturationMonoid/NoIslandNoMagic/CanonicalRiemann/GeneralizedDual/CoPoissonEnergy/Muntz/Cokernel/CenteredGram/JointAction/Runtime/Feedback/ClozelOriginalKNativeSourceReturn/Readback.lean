import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNativeSourceReturn.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNativeSourceReturn
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace Dyn
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullSourceDynamics
  (packet_native_value collapse_generated_successor)
end Dyn
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
  (nativeAfterAdmission_grade)
end AS
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
end A
local instance readbackGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

private theorem input_updated_at
    (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()))
    (generated : AI.HasActualInput (inputCode observation nontrivial half) packet.1 packet.2.2.1 packet.2.2.2.down) :
    CF.collapseValue packet.1 ((R.actualMaterial packet.2.1.1 packet.2.2.1).raw.eval
      (N.input (R.actualMaterial packet.2.1.1 packet.2.2.1)).environment) = inputValue observation nontrivial half := by
  rcases packet with ⟨grade, packetData, programme, ⟨sameVar⟩⟩
  cases programme with
  | mk lowVar datum inventory pairInventory =>
    change lowVar = C.Var at sameVar
    cases sameVar
    let cfg : A.Programme (PhysicalValue := L.Value (PairValue C.Value) grade) (PhysicalVar := C.Var) (sort := ()) :=
      ⟨C.Var, datum, inventory, pairInventory⟩
    let packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()) :=
      ⟨grade, packetData, cfg, ⟨rfl⟩⟩
    have raw := eq_of_heq (Paid.material_raw_at (inputCode observation nontrivial half) packet generated)
    exact (congrArg (fun expression => CF.collapseValue grade (expression.eval
      (N.input (R.actualMaterial packetData.1 cfg)).environment)) raw).trans
      ((CF.code_base_value (inputCode observation nontrivial half) grade _).trans
        (input_code_source observation nontrivial half _))

-- Native xQ birth supplies the actual R input; only the same-source chart is transported.
theorem actual_input_return_input (ordinal : Nat) :
    actualEnvironment observation nontrivial half depth ordinal () () = inputValue observation nontrivial half := by
  let parent := returnParent observation nontrivial half depth ordinal
  let child := returnPacket observation nontrivial half depth ordinal
  let computed := (R.actualMaterial parent.2.1.1 parent.2.2.1).raw.eval
    (N.input (R.actualMaterial parent.2.1.1 parent.2.2.1)).environment
  have childGrade : child.1 = parent.1 + 1 := by
    unfold child returnPacket
    exact AS.nativeAfterAdmission_grade (returnFactory observation nontrivial half) parent
  have childValue : HEq (child.2.1.1.activeEnvironment () ()) computed := by
    unfold child returnPacket
    exact Dyn.packet_native_value (returnFactory observation nontrivial half) parent ()
  have actual := Dyn.collapse_generated_successor parent.1 child.1 childGrade _ computed childValue
  exact actual.trans (input_updated_at observation nontrivial half parent
    (input_born_input observation nontrivial half depth ordinal))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNativeSourceReturn
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
