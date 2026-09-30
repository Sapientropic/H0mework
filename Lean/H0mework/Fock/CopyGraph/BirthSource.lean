import H0mework.Fock.CopyGraph.GrowthObservation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphBirth

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceGeneratedAtomicObservation
open SourceOwnedObservationHistory SourceHistoryGrowth
open SourceCopyProgram (Index)
noncomputable section

theorem copy_read_injective (depth bound : Nat) (index : Index depth) :
    Function.Injective (SourceConditionalGraph.copyRead depth bound index) := by
  intro left right same
  have zero : SourceConditionalGraph.copyRead depth bound index (left - right) = 0 := by
    rw [map_sub, same, sub_self]
  have energy := SourceConditionalGraph.copy_read_energy depth bound index (left - right)
  rw [zero, norm_zero, zero_pow (by decide : 2 ≠ 0)] at energy
  have massCost := sq_nonneg ‖SourceSuccessorBoundary.mass ℂ (SourceHistoryWord.word bound (left - right))‖
  have clockCost := mul_nonneg (sq_nonneg (SourceCopyProgram.scale depth index : ℝ))
    (sq_nonneg ‖SourceClockComplex.clock (SourceHistoryWord.word bound (left - right))‖)
  have vanished : ‖left - right‖ = 0 := by nlinarith only [energy, massCost, clockCost, norm_nonneg (left - right)]
  exact sub_eq_zero.mp (norm_eq_zero.mp vanished)

def fresh (depth : Nat) (index : Index depth) : SourceJointClockGraph.Carrier :=
  SourceConditionalGraph.copyRead (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index)
    (cotest (historyPMF (depth + 1)) (Fin.last (depth + 1)))

universe u
variable {Observed : Type u} [MeasurableSpace Observed]

def innovation (depth : Nat) (index : Index depth) (read : Nat → Observed) : SourceJointClockGraph.Carrier :=
  SourceGraphGrowth.oldResidual depth index read (fresh depth index)

theorem innovation_ne_zero (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    innovation depth index read ≠ 0 := by
  intro vanished
  have remaining : SourceConditionalGraphDecoder.residual depth depth index (SourceGraphGrowth.oldRead depth read)
      (fresh depth index) = 0 := vanished
  have generated := SourceConditionalGraphDecoder.reconstruction depth depth index (SourceGraphGrowth.oldRead depth read) (fresh depth index)
  rw [remaining, add_zero, SourceConditionalGraphDecoder.action_source,
    ← SourceGraphGrowth.tick_copy_read depth index] at generated
  change SourceConditionalGraph.copyRead (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) _ =
    SourceConditionalGraph.copyRead (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index)
      (cotest (historyPMF (depth + 1)) (Fin.last (depth + 1))) at generated
  have samples := copy_read_injective (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index) generated
  have newest := congrArg (fun value : Space (historyPMF (depth + 1)) => value (Fin.last (depth + 1))) samples
  rw [SourceGraphGrowth.normalized_new, cotest_value, if_pos rfl] at newest
  exact zero_ne_one newest

end
end SourceGraphBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
