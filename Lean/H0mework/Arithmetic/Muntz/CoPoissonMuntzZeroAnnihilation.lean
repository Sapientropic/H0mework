import H0mework.Arithmetic.Muntz.CoPoissonMuntzFactorization
import H0mework.Arithmetic.RiemannMellinOrbit.ZeroPositiveParameter

/-!
# Same-zero annihilation of the actual quarter co-Poisson range

The selected and reversal half-parameters are generated from the same
owner-indexed nontrivial zero occurrence.  The general Müntz factorization
therefore kills the complete arbitrary-Schwartz quarter range on both faces.
No separator, radial, fixedness, or critical-line premise is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open Complex FourierTransform MeasureTheory Set Filter Asymptotics
open ClozelEndpointSourceEffect
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open scoped SchwartzMap RealInnerProductSpace Topology

noncomputable section

theorem generatedQuarterMellinL2Functional_coPoissonQuarterMellinConvergentMap
    (owner : GlobalGermOwner) (test : SchwartzMap ℝ ℂ) (z : ℂ)
    (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ)) :
    quarterMellinL2Functional z
        (coPoissonQuarterMellinConvergentMap
          z positive belowHalf test) =
      generatedRiemannZeta owner (2 * z) *
        coPoissonQuarterMuntzSourceMellin test z := by
  rw [generatedRiemannZeta_eq_mathlib]
  exact quarterMellinL2Functional_coPoissonQuarterMellinConvergentMap
    test z positive belowHalf

theorem generatedQuarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
    (owner : GlobalGermOwner) (z : ℂ)
    (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (zero : generatedRiemannZeta owner (2 * z) = 0) :
    (quarterMellinL2Functional z).comp
      (coPoissonQuarterMellinConvergentMap z positive belowHalf) = 0 := by
  ext test
  change quarterMellinL2Functional z
      (coPoissonQuarterMellinConvergentMap
        z positive belowHalf test) = 0
  rw [generatedQuarterMellinL2Functional_coPoissonQuarterMellinConvergentMap,
    zero, zero_mul]

theorem selectedZero_quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (quarterMellinL2Functional (observation.coordinate / 2)).comp
      (coPoissonQuarterMellinConvergentMap
        (observation.coordinate / 2)
        (selectedPositiveParameter_re_pos observation nontrivial)
        (by
          have strip := observation.coordinate_re_lt_one
          rw [Complex.div_re]
          norm_num
          linarith)) = 0 := by
  apply generatedQuarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
  rw [show 2 * (observation.coordinate / 2) =
    observation.coordinate by ring]
  exact observation.zero

private theorem reversal_mathlibZero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    riemannZeta (coordinateReversal observation.coordinate) = 0 := by
  have strip := observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial
  have reversalPositive :
      0 < (coordinateReversal observation.coordinate).re := by
    simp [coordinateReversal]
    linarith
  have reversalNe : coordinateReversal observation.coordinate ≠ 0 := by
    intro equality
    have := congrArg Complex.re equality
    norm_num at this
    linarith
  rw [riemannZeta_def_of_ne_zero reversalNe,
    ← generatedCompletedRiemannZeta_eq_mathlib owner,
    observation.completed_reversal_eq_zero_of_nontrivial nontrivial,
    zero_div]

private theorem reversal_generatedZero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    generatedRiemannZeta owner
      (coordinateReversal observation.coordinate) = 0 := by
  rw [generatedRiemannZeta_eq_mathlib]
  exact reversal_mathlibZero observation nontrivial

theorem reversalZero_quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (quarterMellinL2Functional
      (coordinateReversal observation.coordinate / 2)).comp
      (coPoissonQuarterMellinConvergentMap
        (coordinateReversal observation.coordinate / 2)
        (reversalPositiveParameter_re_pos observation nontrivial)
        (by
          have strip :=
            observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial
          rw [Complex.div_re]
          norm_num
          simp [coordinateReversal]
          linarith)) = 0 := by
  apply generatedQuarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
  rw [show 2 * (coordinateReversal observation.coordinate / 2) =
    coordinateReversal observation.coordinate by ring]
  exact reversal_generatedZero observation nontrivial

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
