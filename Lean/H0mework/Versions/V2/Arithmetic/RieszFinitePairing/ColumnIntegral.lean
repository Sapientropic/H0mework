import H0mework.Versions.V2.Arithmetic.RieszFiniteSource.Bochner
import H0mework.Arithmetic.RieszResponse.Integration

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.ColumnIntegral

open Complex MeasureTheory
open scoped Topology
open OriginalRieszSource OriginalRieszFiniteSource

noncomputable section

/-- The existing scalar variation-of-constants engine consumes an actual L² Euler law. -/
theorem action_of_euler (coordinate : BurnolCompletedMellinCoordinate) (value forcing : BurnolL2)
    (source : GapEuler.euler (value : TemperedDistribution ℝ ℂ) +
      (star coordinate.value - 1 / 2) • (value : TemperedDistribution ℝ ℂ) =
        (forcing : TemperedDistribution ℝ ℂ)) (endpoint : ℝ) :
    burnolMultiplicativeDilation endpoint value =
      fullMellinTranslationCharacter (star coordinate.value) endpoint • value +
        nativeIntegral (star coordinate.value - 1 / 2) forcing endpoint := by
  apply LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume))
  ext test
  let read := fun time : ℝ =>
    (burnolMultiplicativeDilation time value : TemperedDistribution ℝ ℂ) test
  let forcingRead := fun time : ℝ =>
    (forcing : TemperedDistribution ℝ ℂ) (coPoissonSchwartzEnergyTranslation (-time) test)
  have derivative (time : ℝ) : HasDerivAt read
      (forcingRead time - (star coordinate.value - 1 / 2) * read time) time := by
    have evaluated := congrArg (fun state : TemperedDistribution ℝ ℂ =>
      state (coPoissonSchwartzEnergyTranslation (-time) test)) source
    simp only [add_apply, smul_apply, smul_eq_mul] at evaluated
    have actual := Dilation.original_weak_derivative value test time
    rw [OriginalRieszFiniteResponse.original_euler_action, eq_sub_of_add_eq evaluated] at actual
    simpa only [read, forcingRead, OriginalRieszFiniteResponse.original_read] using actual
  have generated := _root_.OriginalRieszFiniteResponse.Integration.finite_response read forcingRead
    (star coordinate.value - 1 / 2) derivative (nativeRead_continuous forcing test) endpoint
  have base : read 0 = (value : TemperedDistribution ℝ ℂ) test := by
    dsimp only [read]
    rw [OriginalRieszFiniteResponse.original_read, neg_zero,
      coPoissonSchwartzEnergyTranslation_zero]
  have character : fullMellinTranslationCharacter (star coordinate.value) endpoint =
      Complex.exp (-(star coordinate.value - 1 / 2) * (endpoint : ℂ)) := by
    unfold fullMellinTranslationCharacter
    congr 1
    ring
  rw [base] at generated
  change (Lp.toTemperedDistributionCLM ℂ volume 2 (burnolMultiplicativeDilation endpoint value)) test =
    (Lp.toTemperedDistributionCLM ℂ volume 2
      (fullMellinTranslationCharacter (star coordinate.value) endpoint • value +
        nativeIntegral (star coordinate.value - 1 / 2) forcing endpoint)) test
  rw [map_add, map_smul]
  simp only [add_apply, smul_apply, smul_eq_mul, Lp.toTemperedDistributionCLM_apply]
  rw [nativeIntegral_read, character]
  exact generated

theorem native_smul_sub (lambda coefficient : ℂ) (left right : BurnolL2) (endpoint : ℝ) :
    nativeIntegral lambda (coefficient • left - right) endpoint =
      coefficient • nativeIntegral lambda left endpoint - nativeIntegral lambda right endpoint := by
  unfold nativeIntegral
  rw [← intervalIntegral.integral_smul, ← intervalIntegral.integral_sub
    (f := fun time : ℝ => coefficient • nativeIntegrand lambda left endpoint time)
    (g := nativeIntegrand lambda right endpoint)
    (((nativeIntegrand_continuous lambda left endpoint).const_smul coefficient).intervalIntegrable 0 endpoint)
    (nativeIntegrand_integrable lambda right endpoint)]
  apply intervalIntegral.integral_congr
  intro time _
  simp only [nativeIntegrand, map_sub, map_smul]
  module

end
end OriginalRieszFinitePairing.ColumnIntegral
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
