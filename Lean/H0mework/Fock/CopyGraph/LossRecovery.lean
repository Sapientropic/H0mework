import H0mework.Fock.CopyGraph.LossDirection

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphLoss

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceOwnedObservationHistory
open SourceCopyProgram (Index)
open SourceGraphGrowth (newRead taggedRead newAction forgettingLoss)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem fresh_loss (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    forgettingLoss depth index read (SourceGraphBirth.fresh depth index) = direction depth index read := by
  have original := SourceGraphGrowth.forgetting_residual depth index read (SourceGraphBirth.fresh depth index)
  rw [SourceGraphBirth.fresh_tagged_recovery, zero_add] at original
  exact original.symm

theorem loss_on_raw (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : Space (observed (historyPMF (depth + 1)) (newRead depth read))) :
    forgettingLoss depth index read (newAction depth index read value) = 0 := by
  have original := SourceGraphRefinement.gain_coarse_source (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index)
    (taggedRead depth read) Prod.fst value
  unfold forgettingLoss
  with_unfolding_all exact original

theorem direction_fixed (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    forgettingLoss depth index read (direction depth index read) = direction depth index read := by
  have original := SourceConditionalGraphDecoder.reconstruction (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index)
    (newRead depth read) (SourceGraphBirth.fresh depth index)
  have applied := congrArg (forgettingLoss depth index read) original
  rw [map_add, loss_on_raw, zero_add, fresh_loss] at applied
  exact applied

end
end SourceGraphLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
