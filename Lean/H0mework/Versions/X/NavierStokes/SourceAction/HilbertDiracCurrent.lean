import H0mework.Versions.X.NavierStokes.StressAction.StressPairingCarrier

set_option autoImplicit false
open scoped BigOperators Matrix Topology

namespace SaturationMonoid.NavierStokes.NativeHilbertDiracCurrent

open Filter Set MeasureTheory UnitAddTorus
open PhysicsCore.DiracCliffordRepresentation
open PhysicsCore.StageNineFullDiracAdjointMaterial (diracAdjointSpinSwap)
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open NativeStressPairingCarrier NativeEndpointVelocityCarrier NativePhysicalFourier
open NativeCofinalStress NativeStressSource

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev Spinor (data : Data) := Fin 4 → Fin 2 → Space data

def action (data : Data) (matrix : DiracMatrix) : Spinor data →ₗ[ℂ] Spinor data where
  toFun vector spin color := ∑ other : Fin 4, matrix spin other • vector other color
  map_add' left right := by
    funext spin color
    simp [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' scalar vector := by
    funext spin color
    simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro other _
    rw [mul_comm]

def canonicalDual (data : Data) (vector : Spinor data) : Module.Dual ℂ (Spinor data) where
  toFun candidate := ∑ spin : Fin 4, ∑ color : Fin 2, inner ℂ (action data diracAdjointSpinSwap vector spin color) (candidate spin color)
  map_add' left right := by simp only [Pi.add_apply, inner_add_right, Finset.sum_add_distrib]
  map_smul' scalar candidate := by simp only [Pi.smul_apply, inner_smul_right, Finset.mul_sum, RingHom.id_apply, smul_eq_mul]

def matter (data : Data) (wave : IntegerWavevector) : Spinor data :=
  !![0, 0; 0, 0;
    background data wave + (1 / 4 : ℂ) • component data (wave, 2),
      (1 / 4 : ℂ) • (component data (wave, 0) - Complex.I • component data (wave, 1));
    (1 / 4 : ℂ) • (component data (wave, 0) + Complex.I • component data (wave, 1)),
      background data wave - (1 / 4 : ℂ) • component data (wave, 2)]

def diracCurrent (data : Data) (direction : Fin 4) (wave : IntegerWavevector) : ℂ :=
  canonicalDual data (matter data wave) (action data (diracGamma direction) (matter data 0))

theorem component_background (data : Data) (wave : IntegerWavevector) (coordinate : Fin 3) :
    inner ℂ (component data (wave, coordinate)) (background data 0) = wholeVelocity data.mean wave coordinate := by
  rw [WithLp.prod_inner_apply]
  change inner ℂ (NativeCofinalStressPositivity.shiftedComponent data.mean (wave, coordinate)) (lp.single 2 0 (1 : ℂ)) + inner ℂ _ 0 = _
  rw [inner_zero_right, add_zero, lp.inner_single_right]
  simp only [RCLike.inner_apply, one_mul, starRingEnd_apply]
  change star (wholeVelocity data.mean (0 - wave) coordinate) = _
  rw [zero_sub]
  have reality : wholeVelocity data.mean (-wave) coordinate = star (wholeVelocity data.mean wave coordinate) :=
    congrFun (wholeVelocity_reality data.mean data.reality wave) coordinate
  rw [reality, star_star]

theorem background_pairing (data : Data) (wave : IntegerWavevector) :
    NativePairedCurrentFourier.baseline wave = 2 * inner ℂ (background data wave) (background data 0) := by
  have orthogonal := (orthonormal_iff_ite.mp (orthonormal_mFourier (d := Fin 3))) wave 0
  have integral : (∫ place : Torus, mFourier (-wave) place) = if wave = 0 then (1 : ℂ) else 0 := by
    simpa [ContinuousMap.inner_toLp, ← mFourier_neg, mFourier_zero] using orthogonal
  unfold NativePairedCurrentFourier.baseline mFourierCoeff
  simp only [smul_eq_mul, integral_mul_const, integral]
  rw [WithLp.prod_inner_apply]
  change (if wave = 0 then (1 : ℂ) else 0) * 2 = 2 *
    (inner ℂ (lp.single 2 wave (1 : ℂ) : ScalarSequence) (lp.single 2 0 1) +
      inner ℂ (0 : NativePositiveKernelCarrier.Space (kernel data)) 0)
  rw [inner_zero_left, add_zero, lp.inner_single_left]
  by_cases zero : wave = 0
  · subst wave
    simp
  · simp [zero]

theorem diracCurrent_eq (data : Data) (direction : Fin 4) (wave : IntegerWavevector)
    (symmetric : ∀ output input : Coordinate, data.stress wave output input = data.stress wave input output) :
    diracCurrent data direction wave = pairedCurrent data direction wave := by
  rw [pairedCurrent_eq]
  have reverse10 := symmetric 1 0
  have reverse20 := symmetric 2 0
  have reverse21 := symmetric 2 1
  have vacuum := background_pairing data wave
  refine Fin.cases ?_ (fun spatial => ?_) direction <;>
    simp only [NativePairedCurrentFourier.coefficient, Fin.cases_zero, Fin.cases_succ]
  all_goals try fin_cases spatial
  all_goals
    simp [-WithLp.prod_inner_apply, diracCurrent, canonicalDual, action, matter, diracAdjointSpinSwap, diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree, Fin.sum_univ_four, Fin.sum_univ_two,
      inner_sub_right, inner_smul_right,
      background_component, component_background, component_inner,
      NativePairedCurrentFourier.trace, Fin.sum_univ_three, vacuum, reverse10, reverse20, reverse21]
  · linear_combination (data.stress wave 1 1 / 8) * Complex.I_sq
  · ring
  · linear_combination -(wholeVelocity data.mean wave 1) * Complex.I_sq
  · ring

variable {nu : Viscosity}

theorem cofinal_stress_symmetric (initial : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector) (output input : Coordinate) :
    (cofinal initial).stress wave output input = (cofinal initial).stress wave input output := by
  let source := sourceGeneratedCofinalStress initial
  have first := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp source.stress_tendsto wave) output) input
  have second := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp source.stress_tendsto wave) input) output
  apply tendsto_nhds_unique first
  apply second.congr'
  exact Eventually.of_forall fun index => quadraticFlux_symmetric _ wave input output

theorem cofinal_current (initial : GeneratedWholeRestartCurrent nu) (direction : Fin 4) (wave : IntegerWavevector) :
    diracCurrent (cofinal initial) direction wave = NativeCofinalPairedCurrent.source initial direction wave :=
  (diracCurrent_eq _ direction wave (cofinal_stress_symmetric initial wave)).trans (NativeStressPairingCarrier.cofinal_current initial direction wave)

end
end SaturationMonoid.NavierStokes.NativeHilbertDiracCurrent
