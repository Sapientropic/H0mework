import H0mework.Versions.X.Fock.CopyGraph.BirthDirection

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphBirth

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceOwnedObservationHistory
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead taggedRead oldAction taggedAction oldResidual taggedResidual birthGain)
open SourceConditionalGraphDecoder (decode)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem fresh_tagged_recovery (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    taggedResidual depth index read (fresh depth index) = 0 := by
  have decoded := congrArg (decode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read))
    (fresh_observed_source depth index read)
  rw [SourceConditionalGraphDecoder.decode_action] at decoded
  have original := SourceConditionalGraphDecoder.reconstruction (depth + 1) (depth + 1)
    (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) (fresh depth index)
  rw [← decoded, fresh_observed_source] at original
  exact add_left_cancel (original.trans (add_zero _).symm)

theorem fresh_birth (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    birthGain depth index read (fresh depth index) = innovation depth index read := by
  have generated := SourceGraphGrowth.birth_residual depth index read (fresh depth index)
  rw [fresh_tagged_recovery, zero_add] at generated
  exact generated.symm

theorem fresh_gain_positive (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    0 < ‖birthGain depth index read (fresh depth index)‖ ^ 2 := by
  rw [fresh_birth]
  exact sq_pos_of_pos (norm_pos_iff.mpr (innovation_ne_zero depth index read))

theorem innovation_fixed (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    birthGain depth index read (innovation depth index read) = innovation depth index read := by
  have original := SourceConditionalGraphDecoder.reconstruction depth depth index (oldRead depth read) (fresh depth index)
  have applied := congrArg (birthGain depth index read) original
  rw [map_add, SourceGraphGrowth.birth_on_old, zero_add, fresh_birth] at applied
  exact applied

end
end SourceGraphBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
