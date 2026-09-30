import H0mework.NavierStokes.GlobalAction.GlobalHilbertAction
import H0mework.NavierStokes.GlobalAction.GlobalPhysicalCarrier
import H0mework.NavierStokes.SourceAction.Pressure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

set_option autoImplicit false
open scoped Topology ENNReal BigOperators ComplexConjugate

namespace SaturationMonoid.NavierStokes.NativeGlobalPhysicalAction

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeEndpointVelocityCarrier NativeMomentumIntegral NativeTimeJetCarrier NativeStressSource
open NativeNegativeFourMomentum NativeGlobalHilbertAction NativePhysicalFourier NativePhysicalSource

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {nu : Viscosity}

theorem embed_row (value : WholeRestartVelocityEndpointState) (wave : IntegerWavevector) :
    wholeVelocity (embed value) wave = weight wave • wholeVelocity value wave := by
  by_cases zero : wave = 0
  · subst wave
    simp
  · funext coordinate
    simp only [wholeVelocity_nonzero _ ⟨wave, zero⟩, Pi.smul_apply]
    rfl

theorem embed_reality (value : WholeRestartVelocityEndpointState) (reality : FiniteStateFourierReality (wholeVelocity value)) :
    FiniteStateFourierReality (wholeVelocity (embed value)) := by
  intro wave
  rw [embed_row, embed_row, reality wave]
  funext coordinate
  simp [weight, vectorConj, Complex.real_smul]

theorem action_reality (value : WholeRestartVelocityEndpointState)
    (reality : FiniteStateFourierReality (wholeVelocity value)) :
    ∀ wave, action nu value (waveNeg wave) = vectorConj (action nu value wave) := by
  intro wave
  have divergence :
      nativeFluidStressDivergenceCoefficient (quadraticFlux (wholeVelocity value)) (waveNeg wave) =
        vectorConj (nativeFluidStressDivergenceCoefficient (quadraticFlux (wholeVelocity value)) wave) := by
    funext output
    simp only [nativeFluidStressDivergenceCoefficient, vectorConj]
    simp_rw [NativePressureFullOrder.quadraticFlux_reality _ reality]
    simp [complexWavevector, waveNeg]
  simp only [action, projectedDivergenceCLM_apply, row]
  change transverseProjection (waveNeg wave)
    (nativeFluidStressDivergenceCoefficient (quadraticFlux (wholeVelocity value)) (waveNeg wave)) - _ = _
  rw [divergence, transverseProjection_waveNeg_vectorConj, reality wave]
  funext coordinate
  simp [vectorConj, integerWaveViscousMultiplier, Complex.real_smul]
  rfl

theorem actionState_row (value : WholeRestartVelocityEndpointState) (wave : IntegerWavevector) :
    wholeVelocity (actionState nu value) wave = weight wave • action nu value wave := by
  by_cases zero : wave = 0
  · subst wave
    simp [weight, integerWaveNormSq]
  · funext coordinate
    rw [wholeVelocity_nonzero _ ⟨wave, zero⟩, actionState_apply]
    rfl

theorem actionState_reality (value : WholeRestartVelocityEndpointState) (reality : FiniteStateFourierReality (wholeVelocity value)) :
    FiniteStateFourierReality (wholeVelocity (actionState nu value)) := by
  intro wave
  rw [actionState_row, actionState_row, action_reality value reality wave]
  funext coordinate
  simp [weight, vectorConj, Complex.real_smul]

def state (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : Lp PhysicalSpace 2 (volume : Measure Torus) :=
  physicalCLM (sourceState seed time)

def tangent (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : Lp PhysicalSpace 2 (volume : Measure Torus) :=
  physicalCLM (sourceAction seed time)

theorem state_fourier (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (coordinate : Coordinate) (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (fun point => (state seed time point coordinate : ℂ)) wave =
      weight wave * wholeVelocity (NativeAbsoluteEventualControl.velocity seed time) wave coordinate := by
  rw [show state seed time = realField (wholeVelocity (embed (NativeAbsoluteEventualControl.velocity seed time))) from rfl,
    realField_fourier _ (embed_reality _ (NativeGlobalPhysicalCarrier.source_reality seed time)), embed_row]
  rfl

theorem tangent_fourier (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (coordinate : Coordinate) (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (fun point => (tangent seed time point coordinate : ℂ)) wave =
      weight wave * action nu (NativeAbsoluteEventualControl.velocity seed time) wave coordinate := by
  rw [show tangent seed time = realField (wholeVelocity (actionState nu (NativeAbsoluteEventualControl.velocity seed time))) from rfl,
    realField_fourier _ (actionState_reality _ (NativeGlobalPhysicalCarrier.source_reality seed time)), actionState_row]
  rfl

theorem tangent_norm (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖tangent seed time‖ = ‖sourceAction seed time‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact (realField_norm_sq _ (actionState_reality _ (NativeGlobalPhysicalCarrier.source_reality seed time))).trans
    (wholeVelocity_mass _)

theorem source_tangent_Linfty (seed : GeneratedWholeRestartCurrent nu) :
    MemLp (tangent seed) ∞ (volume.restrict (Ici (0 : ℝ))) ∧
      eLpNorm (tangent seed) ∞ (volume.restrict (Ici (0 : ℝ))) ≤ ENNReal.ofReal (sourceBudget seed) := by
  have measurable := physicalCLM.continuous.comp_aestronglyMeasurable (sourceAction_aestronglyMeasurable seed)
  have bounded : ∀ᵐ time ∂volume.restrict (Ici (0 : ℝ)), ‖tangent seed time‖ ≤ sourceBudget seed :=
    Eventually.of_forall fun time => (tangent_norm seed time).le.trans (sourceAction_bound seed time)
  exact ⟨memLp_top_of_bound measurable _ bounded, eLpNormEssSup_le_of_ae_bound bounded⟩

theorem tangent_intervalIntegrable (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    IntervalIntegrable (tangent seed) volume 0 horizon := by
  have source := sourceAction_intervalIntegrable seed horizon nonnegative
  exact ⟨physicalCLM.integrable_comp source.1, physicalCLM.integrable_comp source.2⟩

theorem source_integral (seed : GeneratedWholeRestartCurrent nu) (a b : ℝ) (a0 : 0 ≤ a) (b0 : 0 ≤ b) :
    state seed b - state seed a = ∫ time in a..b, tangent seed time := by
  have paid := (sourceAction_intervalIntegrable seed a a0).symm.trans (sourceAction_intervalIntegrable seed b b0)
  have source := congrArg physicalCLM (source_integral_write seed a b a0 b0)
  rw [map_sub, ← physicalCLM.intervalIntegral_comp_comm paid] at source
  exact source

theorem source_derivative_ae (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (positive : 0 < horizon) :
    ∀ᵐ time : ℝ, time ∈ Ioo (0 : ℝ) horizon → HasDerivAt (state seed) (tangent seed time) time := by
  filter_upwards [(tangent_intervalIntegrable seed horizon positive.le).ae_hasDerivAt_integral] with time differentiates inside
  have deriv := (differentiates (by rw [uIcc_of_le positive.le]; exact ⟨inside.1.le, inside.2.le⟩)
    0 (by rw [uIcc_of_le positive.le]; exact ⟨le_rfl, positive.le⟩)).add_const (state seed 0)
  apply deriv.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds inside.1] with sample nonnegative
  rw [← source_integral seed 0 sample le_rfl nonnegative.le]
  simp

end
end SaturationMonoid.NavierStokes.NativeGlobalPhysicalAction
