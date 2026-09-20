import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Complex.Basic

/-!
# Shared finite variation algebra

One type-generic finite-sum identity used independently by the matter,
mother-transport, and geometry variation modules.
-/

namespace SaturationMonoid.PhysicsCore.SU7ExteriorMatterFullVariations

theorem finiteSum_linear_apply_add_smul
    {Index Carrier : Type*}
    [Fintype Index]
    [AddCommMonoid Carrier]
    [Module ℂ Carrier]
    (linearAction : Index → Carrier →ₗ[ℂ] Carrier)
    (base variation : Index → Carrier)
    (coefficient : ℂ) :
    (∑ index : Index,
        linearAction index (base index + coefficient • variation index)) =
      (∑ index : Index, linearAction index (base index)) +
        coefficient •
          ∑ index : Index, linearAction index (variation index) := by
  calc
    _ = ∑ index : Index,
        (linearAction index (base index) +
          coefficient • linearAction index (variation index)) := by
      apply Finset.sum_congr rfl
      intro index _
      rw [map_add, map_smul]
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.smul_sum]

end SaturationMonoid.PhysicsCore.SU7ExteriorMatterFullVariations
