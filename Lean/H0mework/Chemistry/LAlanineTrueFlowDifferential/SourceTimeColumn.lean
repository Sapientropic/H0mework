import H0mework.Chemistry.LAlanineTrueFlowDifferential.SourceParameterMap
import Mathlib.Analysis.Calculus.Deriv.Pi

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferential

open SourceGaussianModel ContinuousGradient ContinuousSeed TrueTubeWholeActual WholeCellPartition
open Set
noncomputable section

/-- The time column of the actual parameter derivative is the original source gradient,
including the two closed time endpoints. -/
theorem trueJacobian_time_column (p : BandPoint) :
    trueJacobian p (Pi.single 2 1) = sourceGradient (trueParameterMap p.val) := by
  have seed_same (t : ℝ) :
      ContinuousParameterMap.initialMap 0 4 (Function.update p.val 2 t) =
        ContinuousParameterMap.initialMap 0 4 p.val := by
    simp [ContinuousParameterMap.initialMap, bandSeed, bandU]
  have curve_same : trueParameterMap ∘ Function.update p.val 2 = fullFlow p := by
    funext t
    change rawFlow (ContinuousParameterMap.initialMap 0 4 (Function.update p.val 2 t))
      ((Function.update p.val 2 t) 2) = rawFlow (ContinuousParameterMap.initialMap 0 4 p.val) t
    rw [seed_same, Function.update_self]
  have line_inside : MapsTo (Function.update p.val 2)
      (Icc (-(1 / 2) : ℝ) (1 / 2)) fullDomain := by
    intro t ht
    constructor <;> intro i <;> by_cases hi : i = 2
    · subst i
      simpa [fullLower, fullLowerQ, halfFlow_exact] using ht.1
    · simpa [Function.update_of_ne hi] using p.property.1 i
    · subst i
      simpa [fullUpper, fullUpperQ, halfFlow_exact] using ht.2
    · simpa [Function.update_of_ne hi] using p.property.2 i
  have time : p.val 2 ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := by
    have bounds := abs_le.mp (scaleAt_abs_le_one p)
    change -1 ≤ 2 * p.val 2 ∧ 2 * p.val 2 ≤ 1 at bounds
    constructor <;> linarith [bounds.1, bounds.2]
  have parameter_derivative := (actualMap_hasFDerivWithinAt p).comp_hasDerivWithinAt_of_eq
    (p.val 2) (hasDerivAt_update p.val (2 : Fin 3) (p.val 2)).hasDerivWithinAt
    line_inside (by simp)
  rw [curve_same] at parameter_derivative
  have unique := uniqueDiffOn_Icc (show (-(1 / 2) : ℝ) < 1 / 2 by norm_num) _ time
  exact (parameter_derivative.derivWithin unique).symm.trans
    ((fullFlow_original p (p.val 2) time).derivWithin unique)

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
