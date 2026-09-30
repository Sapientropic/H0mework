import H0mework.NavierStokes.SourceWindow.PairingAverage

set_option autoImplicit false
open scoped BigOperators Topology ENNReal ComplexOrder

namespace SaturationMonoid.NavierStokes.NativeForwardWindowPairing

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeCompleteStressAction NativeEndpointVelocityCarrier NativeForwardWindowSource
open NativeForwardWindowPairingReadout NativeForwardWindowPairingMoments
open NativeCofinalStressPositivity NativeStressPairingCarrier

noncomputable section

variable {nu : Viscosity}

theorem source_positive (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    (NativeStressPairingCarrier.covariance (source seed time).fst
      (NativeCompleteStressCarrier.read (source seed time).snd)).PosSemidef := by
  rw [source_probability_integral]
  exact NativeForwardWindowPairingAverage.covariance_positive averageMeasure
    (fun shift => NativeUnifiedCompleteSource.source seed (time - shift))
    (original_integrable seed time) (original_square_integrable seed time)
    (fun shift => (NativeCompletePairedAction.source seed (time - shift)).reality)
    (fun shift => (NativeCompletePairedAction.source seed (time - shift)).positive)

/-- The same averaged complete input generates its canonical Gram-pair data. -/
def data (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : NativeStressPairingCarrier.Data where
  mean := (source seed time).fst
  reality := mean_reality seed time
  stress := NativeCompleteStressCarrier.read (source seed time).snd
  positive := source_positive seed time

theorem pairedCurrent_average (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (direction : Fin 4) (wave : ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector) :
    NativeStressPairingCarrier.pairedCurrent (data seed time) direction wave =
      ∫ shift, NativeForwardWindowSource.kernel shift • NativeHilbertDiracCurrent.diracCurrent
        (NativeCompletePairedAction.source seed (time - shift)) direction wave := by
  rw [NativeStressPairingCarrier.pairedCurrent_eq]
  exact current_integral seed time direction wave

theorem diracCurrent_average (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (direction : Fin 4) (wave : ThreeDimensionalPeriodicIntegerCharacterCoarseFilter.IntegerWavevector) :
    NativeHilbertDiracCurrent.diracCurrent (data seed time) direction wave =
      ∫ shift, NativeForwardWindowSource.kernel shift • NativeHilbertDiracCurrent.diracCurrent
        (NativeCompletePairedAction.source seed (time - shift)) direction wave := by
  rw [NativeHilbertDiracCurrent.diracCurrent_eq _ direction wave (stress_symmetric seed time wave)]
  exact pairedCurrent_average seed time direction wave

end
end SaturationMonoid.NavierStokes.NativeForwardWindowPairing
