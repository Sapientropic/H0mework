import H0mework.Versions.R2.Realization.SourceComparison.Maps

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot.SourceComparison

universe u v
variable {source : Dynamics.{u}} {target : Dynamics.{v}}

/-- Mutual local source maps force inverse recovery on the actual generated
carriers. Inverse laws are conclusions of the original recurrence. -/
def recovery (forward : Map source target) (backward : Map target source) :
    Generated source ≃ Generated target where
  toFun := forward.restrict
  invFun := backward.restrict
  left_inv current := by
    rcases current with ⟨_, index, rfl⟩
    change backward.restrict (forward.restrict (generatedAt source index)) = generatedAt source index
    rw [forward.restrict_at, backward.restrict_at]
  right_inv current := by
    rcases current with ⟨_, index, rfl⟩
    change forward.restrict (backward.restrict (generatedAt target index)) = generatedAt target index
    rw [backward.restrict_at, forward.restrict_at]

theorem recovery_at (forward : Map source target) (backward : Map target source) (index : ℕ) :
    recovery forward backward (generatedAt source index) = generatedAt target index :=
  forward.restrict_at index

theorem recovery_unique (forward : Map source target) (backward : Map target source)
    (candidate : Generated source ≃ Generated target)
    (generated : ∀ index, candidate (generatedAt source index) = generatedAt target index) :
    candidate = recovery forward backward := by
  apply Equiv.ext
  intro current
  rcases current with ⟨_, index, rfl⟩
  exact (generated index).trans (recovery_at forward backward index).symm

theorem recovery_advance (forward : Map source target) (backward : Map target source)
    (current : Generated source) :
    recovery forward backward (advance current) = advance (recovery forward backward current) :=
  forward.advance current

/-- The exact collision pattern is reflected, not discarded by unfolding
both dynamics to a bare natural-number sequence. -/
theorem generated_collision_iff (forward : Map source target) (backward : Map target source)
    (first last : ℕ) :
    currentAt source first = currentAt source last ↔
      currentAt target first = currentAt target last := by
  constructor
  · intro same
    simpa only [forward.generated] using congrArg forward.state same
  · intro same
    simpa only [backward.generated] using congrArg backward.state same

theorem generated_recovery (forward : Map source target) (backward : Map target source) :
    ∃! comparison : Generated source ≃ Generated target,
      (∀ index, comparison (generatedAt source index) = generatedAt target index) ∧
      (∀ current, comparison (advance current) = advance (comparison current)) := by
  exact ⟨recovery forward backward,
    ⟨recovery_at forward backward, recovery_advance forward backward⟩,
    fun candidate laws => recovery_unique forward backward candidate laws.1⟩

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RawGeneratedRoot.SourceComparison
