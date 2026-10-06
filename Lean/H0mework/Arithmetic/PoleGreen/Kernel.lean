import H0mework.Arithmetic.SonineCoupling.ModifiedWeakFEPoleTrace

/-!
# The explicit quarter-chart pole Green kernel

The two source corrections are the negative and positive half-line faces of
one function, `exp (-|x| / 4)`.  This is a pointwise identity, including the
origin; no almost-everywhere representative or boundary value is chosen.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex Set

noncomputable section

def clozelPoleGreenKernelReal (x : ℝ) : ℝ :=
  Real.exp (-|x| / 4)

def clozelPoleGreenKernel (x : ℝ) : ℂ :=
  clozelPoleGreenKernelReal x

theorem positiveMellinLogQuarterTransform_low_add_high
    (x : ℝ) :
    positiveMellinLogQuarterTransform
        (positiveClozelLowCorrection + positiveClozelHighCorrection) x =
      clozelPoleGreenKernel x := by
  rw [map_add, Pi.add_apply,
    positiveMellinLogQuarterTransform_lowCorrection,
    positiveMellinLogQuarterTransform_highCorrection]
  by_cases nonpositive : x ≤ 0
  · rw [indicator_of_mem (mem_Iic.mpr nonpositive),
      indicator_of_notMem (notMem_Ioi.mpr nonpositive)]
    simp only [add_zero]
    simp [clozelPoleGreenKernel, clozelPoleGreenKernelReal,
      abs_of_nonpos nonpositive]
  · have positive : 0 < x := lt_of_not_ge nonpositive
    rw [indicator_of_notMem (notMem_Iic.mpr positive),
      indicator_of_mem (mem_Ioi.mpr positive)]
    simp only [zero_add]
    simp [clozelPoleGreenKernel, clozelPoleGreenKernelReal,
      abs_of_pos positive]

theorem positiveMellinLogQuarterTransform_low_add_high_eq_ofReal
    (x : ℝ) :
    positiveMellinLogQuarterTransform
        (positiveClozelLowCorrection + positiveClozelHighCorrection) x =
      (clozelPoleGreenKernelReal x : ℂ) := by
  exact positiveMellinLogQuarterTransform_low_add_high x

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
