import H0mework.Fock.CopyGraph.LossSource
import H0mework.Fock.CopyGraph.RefinementProjection

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphLoss

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceOwnedObservationHistory
open SourceCopyProgram (Index)
open SourceGraphGrowth (newRead taggedRead newAction taggedAction newResidual forgettingLoss)
open SourceConditionalGraphDecoder (decode)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

omit [MeasurableSingletonClass Observed] in
theorem raw_exact (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : Space (observed (historyPMF (depth + 1)) (newRead depth read))) :
    newResidual depth index read (newAction depth index read value) = 0 :=
  SourceGraphGrowth.old_exact (depth + 1) (FamilyModel.Fock.oldIndex depth index) read value

theorem loss_via_raw_residual (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    forgettingLoss depth index read value = newResidual depth index read
      (taggedAction depth index read (decode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) value)) := by
  have original := SourceGraphRefinement.gain_coarse_residual (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index)
    (taggedRead depth read) Prod.fst value
  simpa only [forgettingLoss, newResidual, SourceGraphGrowth.tagged_forget] using original

def coefficient (depth : Nat) (index : Index depth) (read : Nat → Observed) (value : SourceJointClockGraph.Carrier) : ℂ :=
  correction depth read (decode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (taggedRead depth read) value)

theorem loss_direction (depth : Nat) (index : Index depth) (read : Nat → Observed)
    (value : SourceJointClockGraph.Carrier) :
    forgettingLoss depth index read value = coefficient depth index read value • direction depth index read := by
  rw [loss_via_raw_residual, action_decomposition, map_add, map_smul, raw_exact, zero_add]
  rfl

def directionObserved (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    Space (observed (historyPMF (depth + 1)) (taggedRead depth read)) :=
  SourceGraphBirth.freshObserved depth read - SourceGraphRefinement.lift (depth + 1) (taggedRead depth read) Prod.fst
    (decode (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) (Prod.fst ∘ taggedRead depth read) (SourceGraphBirth.fresh depth index))

theorem direction_observed_source (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    taggedAction depth index read (directionObserved depth index read) = direction depth index read := by
  rw [directionObserved, map_sub, SourceGraphBirth.fresh_observed_source, SourceGraphRefinement.action_lift, SourceGraphGrowth.tagged_forget]
  have original := SourceConditionalGraphDecoder.reconstruction (depth + 1) (depth + 1)
    (FamilyModel.Fock.oldIndex depth index) (newRead depth read) (SourceGraphBirth.fresh depth index)
  exact (eq_sub_iff_add_eq.mpr ((add_comm _ _).trans original)).symm

end
end SourceGraphLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
