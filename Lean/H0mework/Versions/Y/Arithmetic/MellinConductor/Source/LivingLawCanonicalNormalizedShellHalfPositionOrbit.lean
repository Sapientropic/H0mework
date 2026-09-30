import H0mework.Versions.Y.Arithmetic.MellinConductor.LivingLawCanonicalQuarterMellinHalfPositionTranslationCovariance
import H0mework.Versions.Y.Arithmetic.RiemannGraph.IntegralGraphKernelCompatibility

/-!
# Actual integral test orbits enter the half-position domain

The normalized source shell has compact logarithmic support, so its energy
lies in the maximal `x/2` domain.  Translation covariance propagates this to
every squared-scale basis orbit.  The integral group-ring basis then proves
domain admission for every actual selected and reversal event, without a
caller-supplied membership table.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace MuntzConductor
namespace HalfPositionSource

open Character.GlobalCoPoissonCurrent
open CenteredGram
open MeasureTheory Set
open HalfPositionDomain
open SourceGeneratedIntegralCharacterGroupRing
open ThetaJRoleRepresentation
open scoped ENNReal SchwartzMap

noncomputable section

theorem positiveMellinQuarterNoGoShellLp_mem_halfPositionDomain :
    positiveMellinQuarterNoGoShellLp ∈ HalfPositionOperator.domain := by
  rw [mem_halfPositionOperator_domain_iff]
  have measurable : AEStronglyMeasurable
      (fun x : ℝ => ((x / 2 : ℝ) : ℂ) *
        positiveMellinQuarterNoGoShellLp x) volume :=
    (by fun_prop)
  apply MemLp.of_le_mul (Lp.memLp positiveMellinQuarterNoGoShellLp)
    measurable
  filter_upwards [positiveMellinQuarterNoGoShellLp_coeFn_support]
    with x supportAt
  by_cases inside : x ∈ Ioc (-Real.log positiveMellinQuarterNoGoScale) 0
  · have logNonnegative : 0 ≤ Real.log positiveMellinQuarterNoGoScale :=
      positiveMellinQuarterNoGoScale_log_pos.le
    have absBound : |x / 2| ≤ Real.log positiveMellinQuarterNoGoScale := by
      have halfNonpositive : x / 2 ≤ 0 := by linarith [inside.2]
      rw [abs_of_nonpos halfNonpositive]
      linarith [inside.1]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right absBound
      (norm_nonneg _)
  · rw [supportAt inside]
    simp

theorem coPoissonMuntzQuarterShellFeature_eq_noGoShellLp
    (z : ℂ) (positive : 0 < z.re) :
    quarterMellinL2Feature z (coPoissonMuntzQuarterShellTest z positive) =
      positiveMellinQuarterNoGoShellLp := by
  rfl

theorem normalizedCoPoissonMuntzQuarterShellFeature_mem_domain
    (z : ℂ) (positive : 0 < z.re) :
    quarterMellinL2Feature z
        (normalizedCoPoissonMuntzQuarterShellTest z positive) ∈
      HalfPositionOperator.domain := by
  rw [normalizedCoPoissonMuntzQuarterShellTest, map_smul,
    coPoissonMuntzQuarterShellFeature_eq_noGoShellLp]
  exact HalfPositionOperator.domain.smul_mem _
    positiveMellinQuarterNoGoShellLp_mem_halfPositionDomain

theorem quarterDilationFeature_mem_halfPositionDomain
    (z : ℂ) (scale : ℝ) (scalePositive : 0 < scale)
    (value : QuarterMellinL2Test z)
    (membership : quarterMellinL2Feature z value ∈
      HalfPositionOperator.domain) :
    quarterMellinL2Feature z
        (quarterDilationTestAction z scale scalePositive value) ∈
      HalfPositionOperator.domain := by
  have translated := translation_mem_halfPositionOperator_domain
    (Real.log scale) ⟨quarterMellinL2Feature z value, membership⟩
  have covariance := LinearMap.congr_fun
    (quarterDilationFeature_covariance z scale scalePositive) value
  change positiveMellinQuarterEnergyTranslation (Real.log scale)
      (quarterMellinL2Feature z value) =
    quarterMellinL2Feature z
      (quarterDilationTestAction z scale scalePositive value) at covariance
  rw [← covariance]
  exact translated

theorem selectedIntegralDilationFeature_delta_mem_domain
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    quarterMellinL2Feature (selectedCoPoissonMuntzParameter observation)
        (selectedIntegralDilationTestOrbit observation nontrivial
          (delta scale)) ∈ HalfPositionOperator.domain := by
  rw [selectedIntegralDilationTestOrbit_delta]
  apply quarterDilationFeature_mem_halfPositionDomain
  exact normalizedCoPoissonMuntzQuarterShellFeature_mem_domain
    _ (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)

theorem reversalIntegralDilationFeature_delta_mem_domain
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    quarterMellinL2Feature (reversalCoPoissonMuntzParameter observation)
        (reversalIntegralDilationTestOrbit observation nontrivial
          (delta scale)) ∈ HalfPositionOperator.domain := by
  rw [reversalIntegralDilationTestOrbit_delta]
  apply quarterDilationFeature_mem_halfPositionDomain
  exact normalizedCoPoissonMuntzQuarterShellFeature_mem_domain
    _ (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)

def halfPositionIntegralDomain :
    Submodule ℤ PositiveMellinQuarterEnergy :=
  HalfPositionOperator.domain.restrictScalars ℤ

def selectedIntegralDilationEnergyOrbit
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    IntegralScaleCarrier →ₗ[ℤ] PositiveMellinQuarterEnergy :=
  ((quarterMellinL2Feature
    (selectedCoPoissonMuntzParameter observation)).restrictScalars ℤ).comp
      (selectedIntegralDilationTestOrbit observation nontrivial)

def reversalIntegralDilationEnergyOrbit
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    IntegralScaleCarrier →ₗ[ℤ] PositiveMellinQuarterEnergy :=
  ((quarterMellinL2Feature
    (reversalCoPoissonMuntzParameter observation)).restrictScalars ℤ).comp
      (reversalIntegralDilationTestOrbit observation nontrivial)

theorem selectedIntegralDilationFeature_mem_domain
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (event : IntegralScaleCarrier) :
    quarterMellinL2Feature (selectedCoPoissonMuntzParameter observation)
        (selectedIntegralDilationTestOrbit observation nontrivial event) ∈
      HalfPositionOperator.domain := by
  let admitted := halfPositionIntegralDomain.comap
    (selectedIntegralDilationEnergyOrbit observation nontrivial)
  have containsBasis :
      Set.range (canonicalBasis (G := Units NNReal)) ⊆
        (admitted : Set IntegralScaleCarrier) := by
    rintro value ⟨scale, rfl⟩
    change selectedIntegralDilationEnergyOrbit observation nontrivial
        (canonicalBasis scale) ∈ halfPositionIntegralDomain
    rw [canonicalBasis_apply]
    exact selectedIntegralDilationFeature_delta_mem_domain
      observation nontrivial scale
  have spanLe : Submodule.span ℤ
      (Set.range (canonicalBasis (G := Units NNReal))) ≤ admitted :=
    Submodule.span_le.mpr containsBasis
  have topLe : (⊤ : Submodule ℤ IntegralScaleCarrier) ≤ admitted := by
    rw [← canonicalBasis.span_eq]
    exact spanLe
  exact topLe (by simp)

theorem reversalIntegralDilationFeature_mem_domain
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (event : IntegralScaleCarrier) :
    quarterMellinL2Feature (reversalCoPoissonMuntzParameter observation)
        (reversalIntegralDilationTestOrbit observation nontrivial event) ∈
      HalfPositionOperator.domain := by
  let admitted := halfPositionIntegralDomain.comap
    (reversalIntegralDilationEnergyOrbit observation nontrivial)
  have containsBasis :
      Set.range (canonicalBasis (G := Units NNReal)) ⊆
        (admitted : Set IntegralScaleCarrier) := by
    rintro value ⟨scale, rfl⟩
    change reversalIntegralDilationEnergyOrbit observation nontrivial
        (canonicalBasis scale) ∈ halfPositionIntegralDomain
    rw [canonicalBasis_apply]
    exact reversalIntegralDilationFeature_delta_mem_domain
      observation nontrivial scale
  have spanLe : Submodule.span ℤ
      (Set.range (canonicalBasis (G := Units NNReal))) ≤ admitted :=
    Submodule.span_le.mpr containsBasis
  have topLe : (⊤ : Submodule ℤ IntegralScaleCarrier) ≤ admitted := by
    rw [← canonicalBasis.span_eq]
    exact spanLe
  exact topLe (by simp)

end
end HalfPositionSource
end MuntzConductor
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
