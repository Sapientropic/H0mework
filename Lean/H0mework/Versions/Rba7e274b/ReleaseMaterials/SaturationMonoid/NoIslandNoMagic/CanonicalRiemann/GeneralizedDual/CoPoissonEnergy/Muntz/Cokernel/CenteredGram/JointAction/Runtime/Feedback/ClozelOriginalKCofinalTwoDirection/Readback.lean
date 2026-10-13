import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalTwoDirection.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalTwoDirection
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex MeasureTheory Set Filter
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

namespace Dyn
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullSourceDynamics
  (packet_native_value cofinal_native_value collapse_generated_successor)
end Dyn
namespace AD
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
  (packetAt_successor_grade)
end AD
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
  (nativeAfterAdmission_grade)
end AS

local instance readbackGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target

def packetTotal (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) : BurnolL2 :=
  totalBranches (CF.collapseValue packet.1 (packet.2.1.1.activeEnvironment () (), 0))

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

private theorem original_packet_total (ordinal : Nat) :
    packetTotal (D.packet observation nontrivial half depth ordinal) =
      D.raw observation nontrivial half depth ordinal := by
  unfold packetTotal totalBranches D.raw D.input
  change (_ + _) + (_ + _) = (_ + _) + (_ + _)
  abel

theorem actual_R_born_input (ordinal : Nat) :
    packetTotal (actionPacket observation nontrivial half depth ordinal) =
      D.raw observation nontrivial half depth (ordinal + 1) := by
  let parent := parentPacket observation nontrivial half depth ordinal
  let child := actionPacket observation nontrivial half depth ordinal
  let original := D.packet observation nontrivial half depth (ordinal + 1)
  let computed := (R.actualMaterial parent.2.1.1 parent.2.2.1).raw.eval
    (N.input (R.actualMaterial parent.2.1.1 parent.2.2.1)).environment
  have childGrade : child.1 = parent.1 + 1 := by
    unfold child actionPacket
    exact AS.nativeAfterAdmission_grade (factory observation nontrivial half) parent
  have childValue : HEq (child.2.1.1.activeEnvironment () ()) computed := by
    unfold child actionPacket
    exact Dyn.packet_native_value (factory observation nontrivial half) parent ()
  have originalGrade : original.1 = parent.1 + 1 :=
    AD.packetAt_successor_grade (D.factory observation nontrivial half)
      (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl (ordinal + 1)
  have originalValue : HEq (original.2.1.1.activeEnvironment () ()) computed :=
    Dyn.cofinal_native_value (D.factory observation nontrivial half)
      (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl (ordinal + 1) ()
  have own := Dyn.collapse_generated_successor parent.1 child.1 childGrade _ computed childValue
  have old := Dyn.collapse_generated_successor parent.1 original.1 originalGrade _ computed originalValue
  exact (congrArg totalBranches (own.trans old.symm)).trans
    (original_packet_total observation nontrivial half depth (ordinal + 1))

theorem actual_R_two_direction (ordinal : Nat) :
    directions (CF.collapseValue (actionPacket observation nontrivial half depth ordinal).1
      (receipt observation nontrivial half depth ordinal).2.2.1) =
      (burnolMultiplicativeDilation sourceShift (D.raw observation nontrivial half depth (ordinal + 2)),
       burnolMultiplicativeDilation (-sourceShift) (D.raw observation nontrivial half depth (ordinal + 2))) :=
  (actual_admitted_directions observation nontrivial half depth ordinal).trans
    (congrArg (fun value : BurnolL2 =>
      (burnolMultiplicativeDilation sourceShift value, burnolMultiplicativeDilation (-sourceShift) value))
      ((congrArg (P.R observation nontrivial half)
        (actual_R_born_input observation nontrivial half depth ordinal)).trans
          (D.raw_successor observation nontrivial half depth (ordinal + 1)).symm))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalTwoDirection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
