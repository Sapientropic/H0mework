import H0mework.Versions.V2.Arithmetic.SonineSource.BalancedSonineEnergyFace
import H0mework.Versions.V2.Arithmetic.BurnolMellin.CompletedMellinPrimaryGenerator

/-!
# Source-exact quarter/additive Burnol rechart

The logarithmic quarter feature and the additive Burnol half-density are two
coordinates of the same compact co-Poisson source.  Reflection, the factor
two, and the half-scale are recorded explicitly.  No equality of unrelated
`L²` type aliases and no whole-carrier landing is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace BurnolPhysicalState

open SourceGeneratedTestHilbertGeneralizedDual

noncomputable section

/-- Pointwise graph-to-additive coordinate change forced by the reciprocal
co-sum and the square-root Mellin chart. -/
def burnolQuarterFeatureAdditiveRechart
    (value : ClozelPositiveMellinFunction) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * positiveMellinLogQuarterTransform value (-2 * x)

theorem burnolQuarterFeatureAdditiveRechart_compactRelation
    (source : burnolCompactAnnulusSource) (x : ℝ) :
    burnolQuarterFeatureAdditiveRechart
        (coPoissonQuarterMellinMap source.1) x =
      burnolCompactAdditiveHalfDensity source x := by
  rw [burnolQuarterFeatureAdditiveRechart,
    positiveMellinLogQuarterTransform_coPoissonQuarterMellinMap,
    burnolCompactAdditiveHalfDensity_eq_logOrbit]
  congr 2
  ring

theorem coPoissonQuarterEnergyMap_ae_eq_burnolHalfDensity_rechart
    (source : burnolCompactAnnulusSource) :
    (coPoissonQuarterEnergyMap source.1 : ℝ → ℂ) =ᵐ[MeasureTheory.volume]
      fun x : ℝ =>
        2 * burnolCompactAdditiveHalfDensity source (-x / 2) := by
  rw [coPoissonQuarterEnergyMap_eq_lpValue]
  filter_upwards [MeasureTheory.MemLp.coeFn_toLp
      (positiveMellinQuarterL2_memLp
        (coPoissonQuarterMellinL2Map source.1))] with x energyRead
  have energyRead' :
      (positiveMellinQuarterLpValue
        (coPoissonQuarterMellinL2Map source.1) : ℝ → ℂ) x =
        positiveMellinLogQuarterTransform
          (coPoissonQuarterMellinL2Map source.1).1 x := by
    simpa only [positiveMellinQuarterLpValue] using energyRead
  rw [energyRead']
  change positiveMellinLogQuarterTransform
      (coPoissonQuarterMellinMap source.1) x = _
  rw [positiveMellinLogQuarterTransform_coPoissonQuarterMellinMap,
    burnolCompactAdditiveHalfDensity_eq_logOrbit]
  ring_nf

/-- Quarter dilation by `exp (2h)` is additive half-density translation by
`-h` after the source-exact rechart. -/
theorem burnolQuarterFeatureAdditiveRechart_normalizedDilation
    (value : ClozelPositiveMellinFunction) (h x : ℝ) :
    burnolQuarterFeatureAdditiveRechart
        (positiveMellinQuarterNormalizedDilation
          (Real.exp (2 * h)) (Real.exp_pos _) value) x =
      burnolQuarterFeatureAdditiveRechart value (x - h) := by
  rw [burnolQuarterFeatureAdditiveRechart,
    positiveMellinLogQuarterTransform_normalizedDilation,
    Real.log_exp, burnolQuarterFeatureAdditiveRechart]
  congr 2
  ring

def burnolAdditiveRawNormalizedDilation
    (h : ℝ) (value : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Real.exp (h / 2) : ℂ) * value (Real.exp h * t)

def burnolAdditiveHalfDensityChart
    (value : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Real.exp (x / 2) : ℂ) * value (Real.exp x)

theorem burnolAdditiveHalfDensityChart_dilation
    (value : ℝ → ℂ) (h x : ℝ) :
    burnolAdditiveHalfDensityChart
        (burnolAdditiveRawNormalizedDilation h value) x =
      burnolAdditiveHalfDensityChart value (x + h) := by
  unfold burnolAdditiveHalfDensityChart burnolAdditiveRawNormalizedDilation
  have weight :
      (Real.exp (x / 2) : ℂ) * (Real.exp (h / 2) : ℂ) =
        (Real.exp ((x + h) / 2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  have argument : Real.exp h * Real.exp x = Real.exp (x + h) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc, weight, argument]

/-- The two action coordinates commute on the same literal source before
either completion or orthogonal projection. -/
theorem burnolCompactRelation_graphDilation_eq_additiveDilation
    (source : burnolCompactAnnulusSource) (h x : ℝ) :
    burnolQuarterFeatureAdditiveRechart
        (positiveMellinQuarterNormalizedDilation
          (Real.exp (2 * h)) (Real.exp_pos _)
          (coPoissonQuarterMellinMap source.1)) x =
      burnolAdditiveHalfDensityChart
        (burnolAdditiveRawNormalizedDilation (-h)
          (burnolCompactAdditiveCoSum source)) x := by
  rw [burnolQuarterFeatureAdditiveRechart_normalizedDilation,
    burnolQuarterFeatureAdditiveRechart_compactRelation,
    burnolAdditiveHalfDensityChart_dilation]
  change burnolCompactAdditiveHalfDensity source (x - h) =
    burnolCompactAdditiveHalfDensity source (x + -h)
  congr 2

theorem burnolCompactRelation_pairedGraphDilation_eq_pairedAdditiveDilation
    (source : burnolCompactAnnulusSource) (h x : ℝ) :
    (1 / 2 : ℂ) *
        (burnolQuarterFeatureAdditiveRechart
            (positiveMellinQuarterNormalizedDilation
              (Real.exp (2 * h)) (Real.exp_pos _)
              (coPoissonQuarterMellinMap source.1)) x +
          burnolQuarterFeatureAdditiveRechart
            (positiveMellinQuarterNormalizedDilation
              (Real.exp (2 * -h)) (Real.exp_pos _)
              (coPoissonQuarterMellinMap source.1)) x) =
      (1 / 2 : ℂ) *
        (burnolAdditiveHalfDensityChart
            (burnolAdditiveRawNormalizedDilation h
              (burnolCompactAdditiveCoSum source)) x +
          burnolAdditiveHalfDensityChart
            (burnolAdditiveRawNormalizedDilation (-h)
              (burnolCompactAdditiveCoSum source)) x) := by
  rw [burnolCompactRelation_graphDilation_eq_additiveDilation source h x,
    burnolCompactRelation_graphDilation_eq_additiveDilation source (-h) x]
  ring

/-- Exact source read: the factor four and parameter halving are part of the
coordinate law. -/
theorem burnolPrimaryRead_is_quarterMellinRead_on_actual_source
    (source : burnolCompactAnnulusSource)
    (coordinate : BurnolCompletedMellinCoordinate) :
    ((4 : ℂ) • burnolCompletedMellinEvaluator coordinate)
        (burnolCompactAdditivePhysicalState source) =
      quarterMellinL2Functional (coordinate.value / 2)
        (coPoissonQuarterMellinConvergentMap
          (coordinate.value / 2)
          (by
            rw [Complex.div_re]
            norm_num
            linarith [coordinate.rightHalf])
          (by
            rw [Complex.div_re]
            norm_num
            linarith [coordinate.belowOne])
          source.1) := by
  simpa only [smul_apply, smul_eq_mul] using
    four_mul_burnolCompletedMellinEvaluator_eq_quarterMellinRead
      source coordinate

end
end BurnolPhysicalState
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
