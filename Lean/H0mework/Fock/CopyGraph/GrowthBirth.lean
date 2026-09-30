import H0mework.Fock.CopyGraph.GrowthImage
import H0mework.Realization.HilbertTransfer.Composition

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphGrowth

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceOwnedObservationHistory
open SourceCopyProgram (Index)
open SourceConditionalGraphDecoder (decode inclusion)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

local instance oldImageComplete (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    CompleteSpace (oldAction depth index read).range :=
  SourceConditionalGraphDecoder.imageComplete depth depth index (oldRead depth read)

local instance taggedImageComplete (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    CompleteSpace (taggedAction depth index read).range :=
  SourceConditionalGraphDecoder.imageComplete (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read)

def oldResidual (depth : Nat) (index : Index depth) (read : Nat → Observed) : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  SourceConditionalGraphDecoder.residual depth depth index (oldRead depth read)

def taggedResidual (depth : Nat) (index : Index depth) (read : Nat → Observed) : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  SourceConditionalGraphDecoder.residual (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read)

def birthGain (depth : Nat) (index : Index depth) (read : Nat → Observed) : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  (taggedAction depth index read).comp
    (decode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read)) -
    (oldAction depth index read).comp (decode depth depth index (oldRead depth read))

theorem retained_transfer (depth : Nat) (index : Index depth) (read : Nat → Observed) (value : SourceJointClockGraph.Carrier) :
    IsometricRetainedTransfer.transfer (Current := SourceJointClockGraph.Carrier) (Next := (oldAction depth index read).range)
      (inclusion depth depth index (oldRead depth read)) value =
    IsometricRetainedTransfer.transfer (Current := (taggedAction depth index read).range) (Next := (oldAction depth index read).range)
      (retainedImageLift depth index read)
      (IsometricRetainedTransfer.transfer (Current := SourceJointClockGraph.Carrier) (Next := (taggedAction depth index read).range)
        (inclusion (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read)) value) := by
  have source := IsometricRetainedTransfer.transfer_comp (Source := SourceJointClockGraph.Carrier)
    (Mid := (taggedAction depth index read).range) (Target := (oldAction depth index read).range)
    (inclusion (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read)) (retainedImageLift depth index read)
  rw [retained_inclusion_comp] at source
  exact DFunLike.congr_fun source value

theorem birth_is_added (depth : Nat) (index : Index depth) (read : Nat → Observed) (value : SourceJointClockGraph.Carrier) :
    birthGain depth index read value =
      inclusion (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read)
        (IsometricRetainedTransfer.residual (Current := (taggedAction depth index read).range) (Next := (oldAction depth index read).range)
          (retainedImageLift depth index read)
          (IsometricRetainedTransfer.transfer (Current := SourceJointClockGraph.Carrier) (Next := (taggedAction depth index read).range)
            (inclusion (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read)) value)) := by
  change SourceConditionalGraphDecoder.action (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read)
      (decode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) value) -
    SourceConditionalGraphDecoder.action depth depth index (oldRead depth read) (decode depth depth index (oldRead depth read) value) = _
  rw [SourceConditionalGraphDecoder.encoded_decode, SourceConditionalGraphDecoder.encoded_decode, retained_transfer]
  change inclusion (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) _ -
    inclusion depth depth index (oldRead depth read) _ =
      inclusion (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) (_ - retainedImageLift depth index read _)
  rw [map_sub]
  rfl

theorem birth_residual (depth : Nat) (index : Index depth) (read : Nat → Observed) (value : SourceJointClockGraph.Carrier) :
    oldResidual depth index read value = taggedResidual depth index read value + birthGain depth index read value := by
  have source := IsometricRetainedTransfer.residual_comp (Source := SourceJointClockGraph.Carrier)
    (Mid := (taggedAction depth index read).range) (Target := (oldAction depth index read).range)
    (inclusion (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read)) (retainedImageLift depth index read) value
  rw [retained_inclusion_comp, ← birth_is_added] at source
  exact source

theorem birth_energy (depth : Nat) (index : Index depth) (read : Nat → Observed) (value : SourceJointClockGraph.Carrier) :
    ‖oldResidual depth index read value‖ ^ 2 = ‖taggedResidual depth index read value‖ ^ 2 + ‖birthGain depth index read value‖ ^ 2 := by
  have source := IsometricRetainedTransfer.residual_comp_energy (Source := SourceJointClockGraph.Carrier)
    (Mid := (taggedAction depth index read).range) (Target := (oldAction depth index read).range)
    (inclusion (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read)) (retainedImageLift depth index read) value
  rw [retained_inclusion_comp] at source
  rw [birth_is_added, (inclusion (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read)).norm_map]
  unfold oldResidual taggedResidual SourceConditionalGraphDecoder.residual
  with_reducible exact source

end
end SourceGraphGrowth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
