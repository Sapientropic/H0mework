import H0mework.Versions.V2.Arithmetic.RiemannDivision.QuarterEnergyRightResolventSource
import H0mework.Arithmetic.Tempered.VariableCoPoisson

/-!
# A compact core source stable under a positive dilation segment

The source is supported strictly inside the fixed Burnol annulus.  Hence every
positive dilation up to `log 16` remains an actual member of the same compact
source carrier.  This is source data, not a supplied closed-range witness.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex
open ClozelEndpointSourceEffect
open ClozelGeneralizedDual
open ClozelGeneralizedDual.BurnolPhysicalState
open scoped SchwartzMap

noncomputable section

/-- A concrete smooth source supported strictly in the core annulus
`1 < |x| < 3`. -/
def burnolCoreAnnulusSchwartz : SchwartzMap ℝ ℂ :=
  scaledSchwartzTest (1 / 4 : ℝ) (by norm_num)
    burnolEvenAnnulusSchwartz

@[simp] theorem burnolCoreAnnulusSchwartz_apply (x : ℝ) :
    burnolCoreAnnulusSchwartz x =
      burnolEvenAnnulusSchwartz ((1 / 4 : ℝ) * x) := by
  rfl

theorem burnolCoreAnnulusSchwartz_even (x : ℝ) :
    burnolCoreAnnulusSchwartz (-x) = burnolCoreAnnulusSchwartz x := by
  rw [burnolCoreAnnulusSchwartz_apply,
    burnolCoreAnnulusSchwartz_apply]
  rw [show (1 / 4 : ℝ) * -x = -((1 / 4 : ℝ) * x) by ring,
    burnolEvenAnnulusSchwartz_even]

theorem burnolCoreAnnulusSchwartz_zero_of_abs_le_one
    {x : ℝ} (inside : |x| ≤ 1) :
    burnolCoreAnnulusSchwartz x = 0 := by
  rw [burnolCoreAnnulusSchwartz_apply]
  apply burnolEvenAnnulusCompactSource.2.2.1
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  nlinarith

theorem burnolCoreAnnulusSchwartz_zero_of_three_le_abs
    {x : ℝ} (outside : 3 ≤ |x|) :
    burnolCoreAnnulusSchwartz x = 0 := by
  rw [burnolCoreAnnulusSchwartz_apply]
  simp only [burnolEvenAnnulusSchwartz, add_apply,
    burnolAnnulusSchwartzReflection_apply, burnolAnnulusSchwartz_apply]
  have scaled : 3 / 4 ≤ |(1 / 4 : ℝ) * x| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    nlinarith
  have scaledNeg : 3 / 4 ≤ |-((1 / 4 : ℝ) * x)| := by
    simpa only [abs_neg] using scaled
  rw [burnolAnnulusBump_zero_of_three_quarters_le_abs scaled,
    burnolAnnulusBump_zero_of_three_quarters_le_abs scaledNeg]
  norm_num

/-- The compact source owned by the core annulus. -/
def burnolCoreAnnulusCompactSource : burnolCompactAnnulusSource :=
  ⟨burnolCoreAnnulusSchwartz,
    ⟨burnolCoreAnnulusSchwartz_even,
      fun x inside => burnolCoreAnnulusSchwartz_zero_of_abs_le_one
        (inside.trans (by norm_num)),
      fun x outside => burnolCoreAnnulusSchwartz_zero_of_three_le_abs
        (by linarith)⟩⟩

private theorem sqrt_exp_bounds
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

/-- Every positive dilation up to `log 16` of the core source is still an
actual member of the fixed compact-annulus source carrier. -/
def burnolCoreAnnulusDilationCompactSource
    (shift : ℝ) (nonnegative : 0 ≤ shift)
    (bounded : shift ≤ Real.log 16) : burnolCompactAnnulusSource :=
  ⟨quarterMuntzSchwartzDilationAction
      (Real.exp shift) (Real.exp_pos shift) burnolCoreAnnulusSchwartz,
    by
      obtain ⟨sqrtLower, sqrtUpper⟩ :=
        sqrt_exp_bounds nonnegative bounded
      refine ⟨?_, ?_, ?_⟩
      · intro x
        change positiveMellinQuarterDilationWeight (Real.exp shift) *
            burnolCoreAnnulusSchwartz (Real.sqrt (Real.exp shift) * -x) =
          positiveMellinQuarterDilationWeight (Real.exp shift) *
            burnolCoreAnnulusSchwartz (Real.sqrt (Real.exp shift) * x)
        rw [show Real.sqrt (Real.exp shift) * -x =
            -(Real.sqrt (Real.exp shift) * x) by ring,
          burnolCoreAnnulusSchwartz_even]
      · intro x inside
        change positiveMellinQuarterDilationWeight (Real.exp shift) *
          burnolCoreAnnulusSchwartz
            (Real.sqrt (Real.exp shift) * x) = 0
        rw [burnolCoreAnnulusSchwartz_zero_of_abs_le_one]
        · simp
        · rw [abs_mul]
          have sqrtNonneg := Real.sqrt_nonneg (Real.exp shift)
          rw [abs_of_nonneg sqrtNonneg]
          nlinarith
      · intro x outside
        change positiveMellinQuarterDilationWeight (Real.exp shift) *
          burnolCoreAnnulusSchwartz
            (Real.sqrt (Real.exp shift) * x) = 0
        rw [burnolCoreAnnulusSchwartz_zero_of_three_le_abs]
        · simp
        · rw [abs_mul]
          have sqrtNonneg := Real.sqrt_nonneg (Real.exp shift)
          rw [abs_of_nonneg sqrtNonneg]
          nlinarith⟩

theorem burnolCoreAnnulusDilationCompactSource_coe
    (shift : ℝ) (nonnegative : 0 ≤ shift)
    (bounded : shift ≤ Real.log 16) :
    (burnolCoreAnnulusDilationCompactSource shift nonnegative bounded).1 =
      quarterMuntzSchwartzDilationAction
        (Real.exp shift) (Real.exp_pos shift)
        burnolCoreAnnulusCompactSource.1 := by
  rfl

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
