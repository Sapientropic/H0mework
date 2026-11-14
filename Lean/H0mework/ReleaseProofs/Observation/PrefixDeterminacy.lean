import H0mework.Realization.Operations.ObservationKernel

/-! A prefix admits a deterministic update precisely when its invisible kernel is the
whole future-observation kernel. The obstruction applies to arbitrary update functions. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory

universe r u

variable {R : Type r} [CommRing R]
variable {C B : Type u} [AddCommGroup C] [Module R C] [AddCommGroup B] [Module R B]
variable (action : C →ₗ[R] C) (observation : C →ₗ[R] B) (bound : Nat)

theorem prefix_has_update_iff_kernel_eq :
    (∃ update : PrefixCarrier B bound → PrefixCarrier B bound,
      ∀ x, update (prefixEvaluator action observation bound x) =
        prefixEvaluator action observation bound (action x)) ↔
    LinearMap.ker (prefixEvaluator action observation bound) =
      LinearMap.ker (sourceMap action observation) := by
  let window := prefixEvaluator action observation bound
  constructor
  · rintro ⟨update, next⟩
    apply le_antisymm
    · apply invariant_submodule_le_kernel action observation (LinearMap.ker window)
      · intro x hx
        change window x = 0 at hx
        exact congrFun hx 0
      · intro x hx
        change window x = 0 at hx
        change window (action x) = 0
        have zero : update 0 = 0 := by simpa only [map_zero] using next 0
        have nextAt := next x
        change update (window x) = window (action x) at nextAt
        rw [hx, zero] at nextAt
        exact nextAt.symm
    · intro x hx
      change window x = 0
      funext i
      exact (mem_kernel_iff action observation x).mp hx i.val
  · intro kernel
    classical
    refine ⟨fun y => if h : ∃ x, window x = y then window (action (Classical.choose h)) else 0, ?_⟩
    intro x
    let h : ∃ z, window z = window x := ⟨x, rfl⟩
    change (if h' : ∃ z, window z = window x then window (action (Classical.choose h')) else 0) =
      window (action x)
    rw [dif_pos h]
    have invisible : Classical.choose h - x ∈ LinearMap.ker window := by
      rw [LinearMap.mem_ker, map_sub, Classical.choose_spec h, sub_self]
    have future : Classical.choose h - x ∈ LinearMap.ker (sourceMap action observation) :=
      kernel ▸ invisible
    have next := kernel_invariant action observation future
    change action (Classical.choose h - x) ∈ LinearMap.ker (sourceMap action observation) at next
    rw [← kernel, LinearMap.mem_ker, map_sub, map_sub, sub_eq_zero] at next
    exact next

end SourceGeneratedActionObservationHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
