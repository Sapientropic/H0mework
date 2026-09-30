import H0mework.Versions.X.Fock.CopyGraph.BirthTagged

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphBirth

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceOwnedObservationHistory
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead taggedRead oldAction taggedAction oldResidual birthGain retainedLift)
open SourceConditionalGraphDecoder (decode inclusion sourceEquiv)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]
attribute [local instance] SourceGraphGrowth.oldImageComplete SourceGraphGrowth.taggedImageComplete

theorem old_transfer_tagged (depth : Nat) (index : Index depth) (read : Nat → Observed) (value : SourceJointClockGraph.Carrier) :
    IsometricRetainedTransfer.transfer (Current := SourceJointClockGraph.Carrier) (Next := (oldAction depth index read).range)
      (inclusion depth depth index (oldRead depth read))
      (taggedAction depth index read (decode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) value)) =
    IsometricRetainedTransfer.transfer (Current := SourceJointClockGraph.Carrier) (Next := (oldAction depth index read).range)
      (inclusion depth depth index (oldRead depth read)) value := by
  rw [SourceGraphGrowth.retained_transfer depth index read
    (taggedAction depth index read (decode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) value))]
  rw [SourceConditionalGraphDecoder.encoded_decode, IsometricRetainedTransfer.transfer_pullback]
  exact (SourceGraphGrowth.retained_transfer depth index read value).symm

theorem old_decode_tagged (depth : Nat) (index : Index depth) (read : Nat → Observed) (value : SourceJointClockGraph.Carrier) :
    decode depth depth index (oldRead depth read)
      (taggedAction depth index read (decode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) value)) =
      decode depth depth index (oldRead depth read) value := by
  change (sourceEquiv depth depth index (oldRead depth read)).symm
    (IsometricRetainedTransfer.transfer (Current := SourceJointClockGraph.Carrier) (Next := (oldAction depth index read).range)
      (inclusion depth depth index (oldRead depth read))
      (taggedAction depth index read (decode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) value))) =
    (sourceEquiv depth depth index (oldRead depth read)).symm
      (IsometricRetainedTransfer.transfer (Current := SourceJointClockGraph.Carrier) (Next := (oldAction depth index read).range)
        (inclusion depth depth index (oldRead depth read)) value)
  exact congrArg (sourceEquiv depth depth index (oldRead depth read)).symm (old_transfer_tagged depth index read value)

theorem birth_via_old_residual (depth : Nat) (index : Index depth) (read : Nat → Observed) (value : SourceJointClockGraph.Carrier) :
    birthGain depth index read value = oldResidual depth index read
      (taggedAction depth index read (decode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) value)) := by
  have generated := SourceConditionalGraphDecoder.reconstruction depth depth index (oldRead depth read)
    (taggedAction depth index read (decode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) value))
  rw [old_decode_tagged] at generated
  exact (eq_sub_iff_add_eq.mpr ((add_comm _ _).trans generated)).symm

def coefficient (depth : Nat) (index : Index depth) (read : Nat → Observed) (value : SourceJointClockGraph.Carrier) : ℂ :=
  decode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) value
    (taggedRead depth read (Fin.last (depth + 1)))

theorem birth_direction (depth : Nat) (index : Index depth) (read : Nat → Observed) (value : SourceJointClockGraph.Carrier) :
    birthGain depth index read value = coefficient depth index read value • innovation depth index read := by
  rw [birth_via_old_residual, action_decomposition, map_add, map_smul, SourceGraphGrowth.old_exact, zero_add]
  rfl

def innovationObserved (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    Space (observed (historyPMF (depth + 1)) (taggedRead depth read)) :=
  freshObserved depth read - retainedLift depth read (decode depth depth index (oldRead depth read) (fresh depth index))

theorem innovation_observed_source (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    taggedAction depth index read (innovationObserved depth index read) = innovation depth index read := by
  rw [innovationObserved, map_sub, fresh_observed_source, SourceGraphGrowth.retained_action]
  have generated := SourceConditionalGraphDecoder.reconstruction depth depth index (oldRead depth read) (fresh depth index)
  exact (eq_sub_iff_add_eq.mpr ((add_comm _ _).trans generated)).symm

end
end SourceGraphBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
