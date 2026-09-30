import H0mework.Versions.Y.Arithmetic.RieszEuler.GapEulerSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.GapEuler

open Complex
noncomputable section

def gapMean (radius : ℝ) (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  star (burnolRadiusMellinGapMoment radius coordinate.value) * (((2 * radius : ℝ) : ℂ)⁻¹)

theorem gapMean_primitive (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    (1 - star coordinate.value) * gapMean radius coordinate =
      (1 / 2 : ℂ) * (radius : ℂ) ^ (-star coordinate.value) := by
  have radiusNe : (radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  have oneNe : 1 - coordinate.value ≠ 0 := by
    intro zero
    have equal := congrArg Complex.re (sub_eq_zero.mp zero)
    simp only [Complex.one_re] at equal
    linarith [coordinate.belowOne]
  have conjugateNe : 1 - star coordinate.value ≠ 0 := by
    simpa only [star_sub, star_one] using star_ne_zero.mpr oneNe
  have argNe : (radius : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg positive.le]
    exact Real.pi_ne_zero.symm
  have conjugated :
      star ((radius : ℂ) ^ (1 - coordinate.value)) =
        (radius : ℂ) ^ (1 - star coordinate.value) := by
    have source := Complex.cpow_conj (radius : ℂ) (1 - coordinate.value) argNe
    simpa only [Complex.conj_ofReal, map_sub, map_one, Complex.star_def] using source.symm
  unfold gapMean burnolRadiusMellinGapMoment
  rw [star_div₀, star_sub, star_one, conjugated]
  have power : (radius : ℂ) ^ (1 - star coordinate.value) =
      (radius : ℂ) ^ (-star coordinate.value) * (radius : ℂ) := by
    rw [show 1 - star coordinate.value = -star coordinate.value + 1 by ring,
      Complex.cpow_add _ _ radiusNe, Complex.cpow_one]
  rw [power]
  push_cast
  field_simp [conjugateNe, radiusNe]

end
end OriginalRieszSource.GapEuler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
