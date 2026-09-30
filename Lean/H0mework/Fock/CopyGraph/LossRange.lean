import H0mework.Fock.CopyGraph.LossRecovery
import H0mework.Fock.CopyGraph.LossInventory

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphLoss

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceCopyProgram (Index)
open SourceGraphGrowth (oldRead forgettingLoss)
open scoped Classical
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem loss_range (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    (forgettingLoss depth index read).range = Submodule.span ℂ {direction depth index read} := by
  apply le_antisymm
  · rintro _ ⟨value, rfl⟩
    change forgettingLoss depth index read value ∈ Submodule.span ℂ {direction depth index read}
    rw [loss_direction]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    intro value inside
    rw [Set.mem_singleton_iff] at inside
    subst value
    exact ⟨direction depth index read, direction_fixed depth index read⟩

theorem rank_inventory (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    Module.finrank ℂ (forgettingLoss depth index read).range =
      if read (depth + 1) ∈ atoms (historyPMF depth) (oldRead depth read) then 1 else 0 := by
  rw [loss_range]
  by_cases present : read (depth + 1) ∈ atoms (historyPMF depth) (oldRead depth read)
  · rw [if_pos present]
    exact finrank_span_singleton (fun zero => (direction_zero_iff_novel depth index read).mp zero present)
  · rw [if_neg present, (direction_zero_iff_novel depth index read).mpr present]
    simp

end
end SourceGraphLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
