import H0mework.Versions.X.NavierStokes.UnheatedWriterGradient.Account
import H0mework.Versions.X.NavierStokes.NativeAction.VelocityCurl
import H0mework.Versions.X.NavierStokes.NativeAction.Pairing
import H0mework.Versions.X.NavierStokes.StressNegativeOne.Momentum

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnheatedSourceGradient

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open NativeResolventCompactness NativeWholeResolvent NativeWholeH1Mixed NativeWholeH1Pairing
open NativeEndpointVelocityCarrier

noncomputable section
variable {nu : Viscosity}

def physical (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time) : wholePhysical := by
  refine ⟨(NativeUnifiedCompleteSource.source seed time).fst, ?_, (NativeCompletePairedAction.source seed time).reality⟩
  intro wave
  have actual := NativeCompleteVelocityCurl.source_transverse seed time nonnegative wave.1
  have same : wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst wave.1 =
      fun coordinate => (NativeUnifiedCompleteSource.source seed time).fst wave coordinate := by
    funext coordinate
    exact wholeVelocity_nonzero _ wave coordinate
  rwa [same] at actual

theorem physical_row (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time) (wave : Wave) :
    gradientDensity (physical seed time nonnegative) wave.1 = row seed wave time := by
  change integerWaveNormSq wave.1 * ‖NativeCompleteStressAction.euclideanCLM
    (wholeVelocity (physical seed time nonnegative).1 wave.1)‖ ^ 2 = _
  rw [NativeWholeH1Equation.euclidean_whole_row]
  rfl

theorem gradient_support (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time) :
    Function.support (gradientDensity (physical seed time nonnegative)) ⊆ {wave | wave ≠ 0} := by
  intro wave member
  by_contra zero
  have equal : wave = 0 := not_ne_iff.mp zero
  subst wave
  simp [gradientDensity, integerWaveNormSq] at member

theorem H1_of_summable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (paid : Summable (fun wave => row seed wave time)) : H1 (physical seed time nonnegative) := by
  have rows : Summable (fun wave : Wave => gradientDensity (physical seed time nonnegative) wave.1) :=
    paid.congr (fun wave => (physical_row seed time nonnegative wave).symm)
  exact ((hasSum_subtype_iff_of_support_subset (gradient_support seed time nonnegative)).mp rows.hasSum).summable

theorem physical_mass (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time) :
    gradientMass (physical seed time nonnegative) = mass seed time := by
  change (∑' wave, gradientDensity (physical seed time nonnegative) wave) = ∑' wave, row seed wave time
  rw [← tsum_subtype_eq_of_support_subset (gradient_support seed time nonnegative)]
  exact tsum_congr (physical_row seed time nonnegative)

theorem physical_H1_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, ∀ nonnegative : 0 ≤ time, H1 (physical seed time nonnegative) := by
  filter_upwards [row_summable_ae seed] with time generated nonnegative
  exact H1_of_summable seed time nonnegative (generated nonnegative)

end
end SaturationMonoid.NavierStokes.NativeUnheatedSourceGradient
