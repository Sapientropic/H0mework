import H0mework.Arithmetic.RiemannAnnulus.CoordinateMatchedAnnulusSource
import H0mework.Versions.V2.Arithmetic.RiemannAnnulus.CoreAnnulusDilationSource

/-!
# Dilation-stable coordinate-matched source

The coordinate-matched source is supported in `1 < |x| < 3`.  Its positive
dilation orbit through `log 16` therefore remains in the fixed Burnol compact
annulus carrier.  This is the source-owned input needed by the resolvent
closed-range landing.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace BurnolPhysicalState

open Complex
open scoped SchwartzMap

noncomputable section

theorem burnolCoordinateMatchedAnnulusSchwartz_zero_of_abs_le_one
    (coordinate : ℂ) {x : ℝ} (inside : |x| ≤ 1) :
    burnolCoordinateMatchedAnnulusSchwartz coordinate x = 0 := by
  have outside (u : ℝ) (bound : |u| ≤ 1) : u ∉ Set.Ioo (1 : ℝ) 3 := by
    intro membership
    have large : 1 < |u| := membership.1.trans_le (le_abs_self u)
    linarith
  rw [burnolCoordinateMatchedAnnulusSchwartz_apply]
  simp only [burnolCoordinateMatchedEvenRaw]
  rw [burnolCoordinateMatchedRealTest_eq_zero_of_not_mem coordinate
      (outside x inside),
    burnolCoordinateMatchedRealTest_eq_zero_of_not_mem coordinate
      (outside (-x) (by simpa using inside))]
  simp

theorem burnolCoordinateMatchedAnnulusSchwartz_zero_of_three_le_abs
    (coordinate : ℂ) {x : ℝ} (outsideBound : 3 ≤ |x|) :
    burnolCoordinateMatchedAnnulusSchwartz coordinate x = 0 := by
  have outside (u : ℝ) (bound : 3 ≤ |u|) : u ∉ Set.Ioo (1 : ℝ) 3 := by
    intro membership
    have upper : |u| < 3 := by
      rcases le_total u 0 with nonpositive | nonnegative
      · rw [abs_of_nonpos nonpositive]
        linarith [membership.1, membership.2]
      · rw [abs_of_nonneg nonnegative]
        exact membership.2
    linarith
  rw [burnolCoordinateMatchedAnnulusSchwartz_apply]
  simp only [burnolCoordinateMatchedEvenRaw]
  rw [burnolCoordinateMatchedRealTest_eq_zero_of_not_mem coordinate
      (outside x outsideBound),
    burnolCoordinateMatchedRealTest_eq_zero_of_not_mem coordinate
      (outside (-x) (by simpa using outsideBound))]
  simp

private theorem coordinateMatched_sqrt_exp_bounds
    {shift : ℝ} (nonnegative : 0 ≤ shift)
    (bounded : shift ≤ Real.log 16) :
    1 ≤ Real.sqrt (Real.exp shift) ∧
      Real.sqrt (Real.exp shift) ≤ 4 := by
  have expLower : 1 ≤ Real.exp shift := by
    simpa using Real.exp_le_exp.mpr nonnegative
  have expUpper : Real.exp shift ≤ 16 := by
    calc
      Real.exp shift ≤ Real.exp (Real.log 16) :=
        Real.exp_le_exp.mpr bounded
      _ = 16 := Real.exp_log (by norm_num)
  have square := Real.sq_sqrt (Real.exp_pos shift).le
  have nonneg := Real.sqrt_nonneg (Real.exp shift)
  constructor <;> nlinarith

/-- The actual coordinate-matched source after one positive quarter-dilation
inside the full stable segment. -/
def burnolCoordinateMatchedAnnulusDilationSource
    (coordinate : ℂ) (shift : ℝ) (nonnegative : 0 ≤ shift)
    (bounded : shift ≤ Real.log 16) : burnolCompactAnnulusSource :=
  ⟨quarterMuntzSchwartzDilationAction
      (Real.exp shift) (Real.exp_pos shift)
      (burnolCoordinateMatchedAnnulusSource coordinate).1,
    by
      obtain ⟨sqrtLower, sqrtUpper⟩ :=
        coordinateMatched_sqrt_exp_bounds nonnegative bounded
      refine ⟨?_, ?_, ?_⟩
      · intro x
        change positiveMellinQuarterDilationWeight (Real.exp shift) *
            burnolCoordinateMatchedAnnulusSchwartz coordinate
              (Real.sqrt (Real.exp shift) * -x) =
          positiveMellinQuarterDilationWeight (Real.exp shift) *
            burnolCoordinateMatchedAnnulusSchwartz coordinate
              (Real.sqrt (Real.exp shift) * x)
        rw [show Real.sqrt (Real.exp shift) * -x =
            -(Real.sqrt (Real.exp shift) * x) by ring]
        simp [burnolCoordinateMatchedEvenRaw, add_comm]
      · intro x inside
        change positiveMellinQuarterDilationWeight (Real.exp shift) *
          burnolCoordinateMatchedAnnulusSchwartz coordinate
            (Real.sqrt (Real.exp shift) * x) = 0
        rw [burnolCoordinateMatchedAnnulusSchwartz_zero_of_abs_le_one]
        · simp
        · rw [abs_mul, abs_of_nonneg
              (Real.sqrt_nonneg (Real.exp shift))]
          nlinarith
      · intro x outside
        change positiveMellinQuarterDilationWeight (Real.exp shift) *
          burnolCoordinateMatchedAnnulusSchwartz coordinate
            (Real.sqrt (Real.exp shift) * x) = 0
        rw [burnolCoordinateMatchedAnnulusSchwartz_zero_of_three_le_abs]
        · simp
        · rw [abs_mul, abs_of_nonneg
              (Real.sqrt_nonneg (Real.exp shift))]
          nlinarith⟩

theorem burnolCoordinateMatchedAnnulusDilationSource_coe
    (coordinate : ℂ) (shift : ℝ) (nonnegative : 0 ≤ shift)
    (bounded : shift ≤ Real.log 16) :
    (burnolCoordinateMatchedAnnulusDilationSource
      coordinate shift nonnegative bounded).1 =
      quarterMuntzSchwartzDilationAction
        (Real.exp shift) (Real.exp_pos shift)
        (burnolCoordinateMatchedAnnulusSource coordinate).1 := by
  rfl

end
end BurnolPhysicalState
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
