import H0mework.Versions.X.Fock.CopyGraph.BirthRecovery
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphBirth

open SourceCopyProgram (Index)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem birth_range (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    (SourceGraphGrowth.birthGain depth index read).range = Submodule.span ℂ {innovation depth index read} := by
  apply le_antisymm
  · rintro _ ⟨value, rfl⟩
    change SourceGraphGrowth.birthGain depth index read value ∈ Submodule.span ℂ {innovation depth index read}
    rw [birth_direction]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    intro value inside
    rw [Set.mem_singleton_iff] at inside
    subst value
    exact ⟨innovation depth index read, innovation_fixed depth index read⟩

theorem birth_finrank (depth : Nat) (index : Index depth) (read : Nat → Observed) :
    Module.finrank ℂ (SourceGraphGrowth.birthGain depth index read).range = 1 := by
  rw [birth_range]
  exact finrank_span_singleton (innovation_ne_zero depth index read)

end
end SourceGraphBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
