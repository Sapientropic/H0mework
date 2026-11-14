import H0mework.Realization.ObservationActions.MaterialCharpoly

/-! The finite material action itself bounds the first invariant observation kernel. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.MaterialRecurrence.Minimal

open scoped Classical

noncomputable section
universe r u
variable {R : Type r} [CommRing R] [Nontrivial R]
variable {C B : Type u} [AddCommGroup C] [Module R C] [Module.Free R C] [Module.Finite R C]
variable [AddCommGroup B] [Module R B]
variable (action : C →ₗ[R] C) (observation : C →ₗ[R] B)

def stable (length : Nat) : Prop :=
  LinearMap.ker (prefixEvaluator action observation length) ≤
    (LinearMap.ker (prefixEvaluator action observation length)).comap action

theorem source_has_stable_window : ∃ length, stable action observation length :=
  ⟨bound action, FiniteRecurrence.prefix_kernel_invariant action observation (bound action)
    (coefficients action) (observation_law action observation)⟩

def horizon : Nat := Nat.find (source_has_stable_window action observation)

theorem horizon_stable : stable action observation (horizon action observation) :=
  Nat.find_spec (source_has_stable_window action observation)

theorem horizon_le_material_bound : horizon action observation ≤ bound action :=
  Nat.find_min' (source_has_stable_window action observation)
    (FiniteRecurrence.prefix_kernel_invariant action observation (bound action)
      (coefficients action) (observation_law action observation))

theorem horizon_kernel :
    LinearMap.ker (prefixEvaluator action observation (horizon action observation)) =
      LinearMap.ker (sourceMap action observation) := by
  apply le_antisymm
  · apply invariant_submodule_le_kernel action observation _ _ (horizon_stable action observation)
    intro value invisible
    exact congrFun invisible 0
  · intro value invisible
    change prefixEvaluator action observation (horizon action observation) value = 0
    funext index
    exact (mem_kernel_iff action observation value).mp invisible index.val

theorem shorter_obstruction (length : Nat) (shorter : length < horizon action observation) :
    ∃ word : C, prefixEvaluator action observation length word = 0 ∧
      prefixEvaluator action observation length (action word) ≠ 0 := by
  have missing := Nat.find_min (source_has_stable_window action observation) shorter
  change ¬ ∀ word : C, word ∈ LinearMap.ker (prefixEvaluator action observation length) →
    word ∈ (LinearMap.ker (prefixEvaluator action observation length)).comap action at missing
  push Not at missing
  exact missing

theorem no_short_update (length : Nat) (shorter : length < horizon action observation) :
    ¬ ∃ advance : PrefixCarrier B length → PrefixCarrier B length,
      ∀ word : C, advance (prefixEvaluator action observation length word) =
        prefixEvaluator action observation length (action word) := by
  obtain ⟨word, hidden, exposed⟩ := shorter_obstruction action observation length shorter
  rintro ⟨advance, sourceLaw⟩
  have zero := sourceLaw 0
  simp only [map_zero] at zero
  have actual := sourceLaw word
  rw [hidden, zero] at actual
  exact exposed actual.symm

end
end SourceGeneratedActionObservationHistory.MaterialRecurrence.Minimal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
