import H0mework.Chemistry.LAlanineSignedEvaluator.Arithmetic
import H0mework.Chemistry.LAlanineBandCache.SaturationSequence

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals
open BasinRefinement SourceSignedEvaluator SourceExponential

def negativeExp (penalty : ℚ) (steps : ℕ) : Pair :=
  if penalty = 0 then (1,1)
  else if 112 ≤ penalty then (0,1/scale)
  else (leafLower (-penalty) steps,leafUpper (-penalty) steps)

def ExpReductionValid (penalty : ℚ) (steps : ℕ) : Prop :=
  penalty ≠ 0 → penalty < 112 → |reducedArgument (-penalty) steps| ≤ 1/2

theorem exp_cut_bound : Real.exp (-(112 : ℝ)) ≤ (1/scale : ℚ) := by
  have bound := (leaf_contains (-112) 8 (by decide +kernel)).2.2
  have saturated := WholeBandSaturation.leaf_saturated (a := -112) (k := 8)
    (by decide +kernel) (Or.inl ⟨rfl,by decide +kernel⟩)
  rw [saturated.2] at bound
  exact_mod_cast bound

theorem negative_exp_contains (penalty : ℚ) (steps : ℕ) (valid : ExpReductionValid penalty steps) :
    Holds (negativeExp penalty steps) (Real.exp (-(penalty : ℝ))) := by
  unfold negativeExp
  split_ifs with zero large
  · simp [zero,Holds]
  · constructor
    · simpa only [Rat.cast_zero] using (Real.exp_pos (-(penalty : ℝ))).le
    · exact (Real.exp_le_exp.mpr (by exact_mod_cast neg_le_neg large)).trans exp_cut_bound
  · simpa only [Holds,Rat.cast_neg] using
      (leaf_contains (-penalty) steps (valid zero (lt_of_not_ge large))).2

end LAlanine40K2025.UnifiedOrbitals
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
