import Mathlib.Analysis.InnerProductSpace.GramMatrix
import H0mework.Versions.X.NavierStokes.CofinalReadout.StressDefect

set_option autoImplicit false
open scoped BigOperators ENNReal ComplexOrder

namespace SaturationMonoid.NavierStokes.NativeCofinalStressPositivity

open Filter Set Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeCofinalStress NativeCofinalStressDefect NativeCofinalFluxPairing
open NativePhysicalFourier NativeEndpointVelocityCarrier NativeStressSource

noncomputable section

abbrev Index := IntegerWavevector × Coordinate

def shiftedComponent (velocity : WholeRestartVelocityEndpointState) (index : Index) : ScalarSequence :=
  ⟨fun wave => wholeVelocity velocity (wave - index.1) index.2, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    have full : Summable (fun frequency => ‖wholeVelocity velocity frequency index.2‖ ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, scalarSequence] using
        (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num)
          (scalarSequence (wholeVelocity velocity) index.2)).summable
    exact full.comp_injective (fun _ _ equality => sub_left_injective equality)⟩

/-- The complete frequency/coordinate covariance is an actual Gram kernel. -/
theorem shiftedComponent_inner (velocity : WholeRestartVelocityEndpointState)
    (reality : WholeRestartVelocityEndpointReality velocity) (left right : Index) :
    inner ℂ (shiftedComponent velocity left) (shiftedComponent velocity right) =
      -bilinearFlux velocity velocity (left.1 - right.1) left.2 right.2 := by
  rw [bilinearFlux, neg_neg, lp.inner_eq_tsum]
  change (∑' wave : IntegerWavevector,
    inner ℂ (wholeVelocity velocity (wave - left.1) left.2)
      (wholeVelocity velocity (wave - right.1) right.2)) = _
  rw [← (Equiv.addRight right.1).tsum_eq]
  apply tsum_congr
  intro wave
  simp only [Equiv.coe_addRight, add_sub_cancel_right, RCLike.inner_apply,
    starRingEnd_apply]
  have reflected : star (wholeVelocity velocity (wave + right.1 - left.1) left.2) =
      wholeVelocity velocity (left.1 - right.1 - wave) left.2 := by
    have indexEq : left.1 - right.1 - wave = waveNeg (wave + right.1 - left.1) := by
      change left.1 - right.1 - wave = -(wave + right.1 - left.1)
      abel
    rw [indexEq, wholeVelocity_reality velocity reality]
    rfl
  rw [reflected]

theorem gram_posSemidef {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (vectors : ι → E) : Matrix.PosSemidef (Matrix.gram ℂ vectors) := by
  refine ⟨Matrix.isHermitian_gram ℂ vectors, ?_⟩
  intro coefficients
  have value : coefficients.sum (fun i a => coefficients.sum fun j b =>
      star a * Matrix.gram ℂ vectors i j * b) =
      inner ℂ (coefficients.sum fun i a => a • vectors i)
        (coefficients.sum fun i a => a • vectors i) := by
    rw [Finsupp.sum_inner]
    simp only [Finsupp.sum, inner_sum, inner_smul_left, inner_smul_right,
      Matrix.gram_apply, starRingEnd_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [value, inner_self_eq_norm_sq_to_K]
  positivity

def covariance {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu}
    (receipt : CofinalStressAt initial) : Matrix Index Index ℂ :=
  fun left right => -stressDefect receipt (left.1 - right.1) left.2 right.2

theorem fluctuation_reality {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu}
    (receipt : CofinalStressAt initial) (index : ℕ) :
    WholeRestartVelocityEndpointReality (fluctuation receipt index) := by
  intro wave coordinate
  change wholeRestartContactVelocityState initial (receipt.stage index) (nonzeroIntegerWavevectorNeg wave) coordinate -
      (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint
        (nonzeroIntegerWavevectorNeg wave) coordinate =
    star (wholeRestartContactVelocityState initial (receipt.stage index) wave coordinate -
      (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint wave coordinate)
  rw [wholeRestartContactVelocityState_reality,
    (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint_reality, star_sub]

/-- All finite tests on the complete frequency/coordinate carrier see a positive covariance.
The source itself remains full-frequency; no finite input or zero-defect branch is selected. -/
theorem covariance_posSemidef {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu}
    (receipt : CofinalStressAt initial) : Matrix.PosSemidef (covariance receipt) := by
  let matrices := fun index => Matrix.gram ℂ (shiftedComponent (fluctuation receipt index))
  have positive (index : ℕ) : Matrix.PosSemidef (matrices index) := gram_posSemidef _
  have convergence (left right : Index) : Tendsto (fun index => matrices index left right) atTop
      (nhds (covariance receipt left right)) := by
    have result := (fluctuation_stress_tendsto receipt (left.1 - right.1) left.2 right.2).neg
    have actual (index : ℕ) : matrices index left right =
        -quadraticFlux (wholeVelocity (fluctuation receipt index)) (left.1 - right.1) left.2 right.2 := by
      change inner ℂ (shiftedComponent (fluctuation receipt index) left)
        (shiftedComponent (fluctuation receipt index) right) = _
      rw [shiftedComponent_inner _ (fluctuation_reality receipt index), bilinearFlux_diagonal]
    simpa only [actual, covariance] using result
  refine ⟨?_, ?_⟩
  · ext left right
    change star (covariance receipt right left) = covariance receipt left right
    have reflected := (convergence right left).star
    have actual (index : ℕ) : star (matrices index right left) = matrices index left right :=
      congrFun (congrFun (positive index).1 left) right
    simp only [actual] at reflected
    exact tendsto_nhds_unique reflected (convergence left right)
  · intro coefficients
    have quadratic := tendsto_finsetSum coefficients.support (fun left _ =>
      tendsto_finsetSum coefficients.support (fun right _ =>
        ((tendsto_const_nhds (x := star (coefficients left))).mul (convergence left right)).mul
          (tendsto_const_nhds (x := coefficients right))))
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds quadratic (fun index => (positive index).2 coefficients)

end
end SaturationMonoid.NavierStokes.NativeCofinalStressPositivity
