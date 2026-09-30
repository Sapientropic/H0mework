import H0mework.NavierStokes.SourceWindow.PairingReadout
import H0mework.NavierStokes.PairedAction.PairedCarrierJets
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false
open scoped BigOperators Topology ENNReal ComplexOrder

namespace SaturationMonoid.NavierStokes.NativeForwardWindowPairingMoments

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeCompleteStressAction NativeEndpointVelocityCarrier NativeForwardWindowSource
open NativeForwardWindowPairingReadout NativeCofinalStressPositivity NativeStressPairingCarrier

noncomputable section

def shiftedRead (index : Index) : FullSpace →L[ℝ] NativePhysicalFourier.ScalarSequence :=
  (NativePairedCarrierJets.shiftedCLM index.1 index.2).comp (wholeVelocityCLM.comp meanRead)

def meanTest (coefficients : Index →₀ ℂ) : FullSpace →L[ℝ] NativePhysicalFourier.ScalarSequence :=
  coefficients.sum fun index scalar => scalar • shiftedRead index

def stressTest (coefficients : Index →₀ ℂ) : FullSpace →L[ℝ] ℂ :=
  coefficients.sum fun left a => coefficients.sum fun right b =>
    (-star a * b) • stressRead (left.1 - right.1) left.2 right.2

theorem meanTest_apply (coefficients : Index →₀ ℂ) (value : FullSpace) :
    meanTest coefficients value = coefficients.sum fun index scalar =>
      scalar • shiftedComponent value.fst index := by
  simp only [meanTest, Finsupp.sum, sum_apply, smul_apply]
  rfl

theorem stressTest_apply (coefficients : Index →₀ ℂ) (value : FullSpace) :
    stressTest coefficients value = coefficients.sum fun left a => coefficients.sum fun right b =>
      star a * (-NativeCompleteStressCarrier.read value.snd (left.1 - right.1) left.2 right.2) * b := by
  simp only [stressTest, Finsupp.sum, sum_apply, smul_apply, smul_eq_mul,
    stressRead, ContinuousLinearMap.comp_apply, WithLp.sndL_apply, NativeCompleteStressCarrier.readCLM_apply]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  ring

theorem meanTest_square (coefficients : Index →₀ ℂ) (value : FullSpace)
    (reality : ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint.WholeRestartVelocityEndpointReality value.fst) :
    (‖meanTest coefficients value‖ ^ 2 : ℂ) =
      coefficients.sum fun left a => coefficients.sum fun right b =>
        star a * (-NativeStressSource.quadraticFlux (wholeVelocity value.fst)
          (left.1 - right.1) left.2 right.2) * b := by
  have self : inner ℂ (meanTest coefficients value) (meanTest coefficients value) =
      (‖meanTest coefficients value‖ ^ 2 : ℂ) := by
    convert! inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (meanTest coefficients value) using 1
  rw [← self, meanTest_apply, Finsupp.sum_inner]
  simp only [Finsupp.sum, inner_sum, inner_smul_left, inner_smul_right,
    shiftedComponent_inner value.fst reality, NativeCofinalFluxPairing.bilinearFlux_diagonal,
    starRingEnd_apply]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  ring

theorem covariance_test (coefficients : Index →₀ ℂ) (value : FullSpace)
    (reality : ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint.WholeRestartVelocityEndpointReality value.fst) :
    coefficients.sum (fun left a => coefficients.sum fun right b => star a *
      NativeStressPairingCarrier.covariance value.fst (NativeCompleteStressCarrier.read value.snd) left right * b) =
        stressTest coefficients value - (‖meanTest coefficients value‖ ^ 2 : ℂ) := by
  rw [stressTest_apply, meanTest_square coefficients value reality]
  simp only [NativeStressPairingCarrier.covariance, Finsupp.sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro left _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro right _
  ring

variable {nu : Viscosity}

theorem square_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (read : FullSpace →L[ℝ] E)
    (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    Integrable (fun shift => ‖read (NativeUnifiedCompleteSource.source seed (time - shift))‖ ^ 2) averageMeasure := by
  apply Integrable.of_bound ((read.integrable_comp (original_integrable seed time)).aestronglyMeasurable.norm.pow 2)
    ((‖read‖ * NativeUnifiedCompleteSource.budget seed) ^ 2)
  filter_upwards with shift
  change ‖‖read (NativeUnifiedCompleteSource.source seed (time - shift))‖ ^ 2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) ((read.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (NativeUnifiedCompleteSource.source_bound seed (time - shift)) (norm_nonneg _))) 2

theorem original_square_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    Integrable (fun shift => ‖NativeUnifiedCompleteSource.source seed (time - shift)‖ ^ 2) averageMeasure := by
  simpa only [ContinuousLinearMap.id_apply] using
    square_integrable (ContinuousLinearMap.id ℝ FullSpace) seed time

end
end SaturationMonoid.NavierStokes.NativeForwardWindowPairingMoments
