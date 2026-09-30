import H0mework.Arithmetic.SonineGap.BalancedSonineGapFace
import H0mework.Versions.Y.Arithmetic.Muntz.CoPoissonMuntzZeroAnnihilation

/-!
# Same-zero annihilation on the balanced Sonine source

The selected and reversal Mellin functionals kill the same fixed two-gap
source through the already generated co-Poisson relation map.
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

open Complex FourierTransform MeasureTheory
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open scoped SchwartzMap RealInnerProductSpace

noncomputable section

/-- Every source in the fixed face is killed by the selected zero-owned
Müntz functional through the already generated co-Poisson map. -/
theorem stageZeroBalancedSonineSource_selected_annihilation
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (source : StageZeroBalancedSonineSource) :
    quarterMellinL2Functional (observation.coordinate / 2)
        (coPoissonQuarterMellinConvergentMap
          (observation.coordinate / 2)
          (selectedPositiveParameter_re_pos observation nontrivial)
          (by
            have strip := observation.coordinate_re_lt_one
            rw [Complex.div_re]
            norm_num
            linarith)
          (source : SonineSchwartz)) = 0 := by
  have operatorZero :=
    selectedZero_quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
      observation nontrivial
  have evaluated := congrArg
    (fun operator : SonineSchwartz →ₗ[ℂ] ℂ ↦
      operator (source : SonineSchwartz)) operatorZero
  simpa using evaluated

/-- The same fixed source is killed on the reversal face from the same zero
occurrence. -/
theorem stageZeroBalancedSonineSource_reversal_annihilation
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (source : StageZeroBalancedSonineSource) :
    quarterMellinL2Functional
        (coordinateReversal observation.coordinate / 2)
        (coPoissonQuarterMellinConvergentMap
          (coordinateReversal observation.coordinate / 2)
          (reversalPositiveParameter_re_pos observation nontrivial)
          (by
            have strip :=
              observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial
            rw [Complex.div_re]
            norm_num
            simp [coordinateReversal]
            linarith)
          (source : SonineSchwartz)) = 0 := by
  have operatorZero :=
    reversalZero_quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
      observation nontrivial
  have evaluated := congrArg
    (fun operator : SonineSchwartz →ₗ[ℂ] ℂ ↦
      operator (source : SonineSchwartz)) operatorZero
  simpa using evaluated

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
