import H0mework.Arithmetic.MuntzAction.GaussianSchwartz
import H0mework.Versions.R2.Arithmetic.SonineCoupling.ConjugateTateGaussianSource

/-!
# The source Gaussian is an actual co-Poisson--Müntz relation

The square-root quarter chart is essential: scaling `exp (-πx²)` by `a` produces the theta
parameter `a²`.  This file identifies the already generated scalar Gaussian remainder with that
actual Schwartz relation and therefore kills its selected and reversal graph classes through the
existing relation map.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual

open Complex MeasureTheory
open ClozelEndpointSourceEffect
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open scoped SchwartzMap

noncomputable section

private theorem gaussian_integer_sum_at_scale
    (scale : ℝ) :
    (∑' n : ℤ, clozelGaussianSchwartz (scale * (n : ℝ))) =
      ((∑' n : ℤ,
          Real.exp (-Real.pi * ((n : ℝ) + 0) ^ 2 * scale ^ 2) : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rw [clozelGaussianSchwartz_apply]
  congr 2
  ring

private theorem gaussian_integral_at_scale
    (scale : ℝ) :
    (∫ x : ℝ, clozelGaussianSchwartz (scale * x)) =
      ((∫ x : ℝ,
          Real.exp (-Real.pi * scale ^ 2 * x ^ 2) : ℝ) : ℂ) := by
  simp_rw [clozelGaussianSchwartz_apply]
  rw [integral_complex_ofReal]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  congr 1
  ring

/-- Exact square-scale identity between the arbitrary-Schwartz co-Poisson remainder and the
source-generated scalar Gaussian remainder. -/
theorem coPoissonMuntzScaleRemainder_clozelGaussian
    (owner : GlobalGermOwner) {scale : ℝ} (positive : 0 < scale) :
    coPoissonMuntzScaleRemainder clozelGaussianSchwartz scale =
      generatedClozelGaussianRemainderKernel owner (scale ^ 2) := by
  rw [generatedClozelGaussianRemainderKernel_eq_scalarRemainder
    owner (scale ^ 2) (sq_pos_of_pos positive)]
  unfold coPoissonMuntzScaleRemainder
  rw [dif_pos positive, clozelTemperedRemainder_apply]
  simp only [scaledSchwartzTest_apply]
  rw [gaussian_integer_sum_at_scale, gaussian_integral_at_scale]
  simp [clozelGaussianSchwartz_apply]

/-- In the source-owned square-root chart, the actual Gaussian Schwartz relation is literally the
positive generated Gaussian remainder. -/
theorem coPoissonQuarterMellinMap_clozelGaussian
    (owner : GlobalGermOwner) :
    coPoissonQuarterMellinMap clozelGaussianSchwartz =
      positiveGeneratedClozelGaussianRemainder owner := by
  funext t
  have source := coPoissonMuntzScaleRemainder_clozelGaussian owner
    (Real.sqrt_pos.2 t.2)
  unfold coPoissonMuntzScaleRemainder at source
  rw [dif_pos (Real.sqrt_pos.2 t.2), Real.sq_sqrt t.2.le] at source
  exact source

/-- The selected zero-owned Gaussian test is not merely Mellin-annihilated: it is the image of the
concrete Gaussian under the existing arbitrary-Schwartz relation map. -/
theorem selectedGaussianQuarterTest_eq_coPoissonRelation
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedGaussianQuarterTest observation nontrivial =
      coPoissonQuarterMellinConvergentMap
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        clozelGaussianSchwartz := by
  apply Subtype.ext
  change positiveGeneratedClozelGaussianRemainder owner =
    coPoissonQuarterMellinMap clozelGaussianSchwartz
  exact (coPoissonQuarterMellinMap_clozelGaussian owner).symm

/-- The selected Gaussian class vanishes in the existing Müntz graph cokernel because it is an
actual relation, without extending the relation family. -/
theorem selectedGaussianGraphClass_eq_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    selectedGaussianGraphClass observation nontrivial = 0 := by
  unfold selectedGaussianGraphClass
  rw [selectedGaussianQuarterTest_eq_coPoissonRelation]
  exact coPoissonMuntzGraphSourceMap_relation
    (selectedCoPoissonMuntzParameter observation)
    (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
    (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
    clozelGaussianSchwartz

/-- The independently generated reversal Gaussian test is the same concrete relation at the
conjugate--Tate parameter. -/
theorem independentHighGaussianQuarterTest_eq_coPoissonRelation
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    independentHighGaussianQuarterTest observation nontrivial =
      coPoissonQuarterMellinConvergentMap
        (conjugateTateMellinParameter
          (selectedCoPoissonMuntzParameter observation))
        (conjugateTateMellinParameter_re_pos
          (selectedCoPoissonMuntzParameter observation)
          (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial))
        (conjugateTateMellinParameter_re_lt_half
          (selectedCoPoissonMuntzParameter observation)
          (selectedCoPoissonMuntzParameter_re_pos observation nontrivial))
        clozelGaussianSchwartz := by
  apply Subtype.ext
  change positiveGeneratedClozelGaussianRemainder owner =
    coPoissonQuarterMellinMap clozelGaussianSchwartz
  exact (coPoissonQuarterMellinMap_clozelGaussian owner).symm

/-- The reversal Gaussian class is killed by the same existing relation family. -/
theorem generatedHighGaussianGraphClass_eq_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    generatedHighGaussianGraphClass observation nontrivial = 0 := by
  unfold generatedHighGaussianGraphClass
  rw [independentHighGaussianQuarterTest_eq_coPoissonRelation]
  exact coPoissonMuntzGraphSourceMap_relation
    (conjugateTateMellinParameter
      (selectedCoPoissonMuntzParameter observation))
    (conjugateTateMellinParameter_re_pos
      (selectedCoPoissonMuntzParameter observation)
      (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial))
    (conjugateTateMellinParameter_re_lt_half
      (selectedCoPoissonMuntzParameter observation)
      (selectedCoPoissonMuntzParameter_re_pos observation nontrivial))
    clozelGaussianSchwartz

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
