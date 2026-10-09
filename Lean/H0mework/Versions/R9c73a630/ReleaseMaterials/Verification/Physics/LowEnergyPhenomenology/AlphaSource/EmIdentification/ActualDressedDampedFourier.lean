import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFrequencyAmputation
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedGaugePole

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedFrequencyHalf
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open PreparationVacuumPhysicalHalfAxis PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualDressedSylvester ActualDressedStaticResponse ActualEMAction ActualEMDressedGaugePole
open Filter Set MeasureTheory
open scoped Topology Matrix BigOperators Interval
attribute [local irreducible] frequencyInputNormalizer frequencyQuantumCorrection frequencyResponsePencil
  frequencyNormalizedWindow frequencyHalfPolarization emOriginalJacobi

/-- The original physical Fourier clock, with a separate positive observation damping. -/
def dampedFourierClock (omega sigma : ℝ) : ℂ := (sigma:ℂ)-Complex.I*(omega:ℂ)

attribute [local irreducible] dampedFourierClock

theorem damped_fourier_source_domain (omega sigma : ℝ) (k : PhysicalMomentum) (positive : 0<sigma) :
    sourceClockGrowth (physicalFrequencyMomentum omega k)<(dampedFourierClock omega sigma).re := by
  simpa [sourceClockGrowth,physicalFrequencyMomentum,dampedFourierClock,Complex.mul_re] using positive

/-- No factor of the oscillation frequency enters the input normalization. -/
theorem damped_fourier_input_normalizer (omega sigma : ℝ) (k : PhysicalMomentum) (positive : 0<sigma) :
    frequencyInputNormalizer (physicalFrequencyMomentum omega k) (dampedFourierClock omega sigma)=(sigma:ℂ) := by
  have domain:=damped_fourier_source_domain omega sigma k positive
  have inputOff : (physicalFrequencyMomentum omega k 0).re<(dampedFourierClock omega sigma).re :=
    (le_max_right 0 _).trans_lt domain
  rw [frequency_input_normalizer_generated _ _ inputOff]
  simp only [physicalFrequencyMomentum,Fin.cases_zero,dampedFourierClock]
  ring

theorem damped_fourier_response (event : DressedEvent) (transfer : PhysicalMomentum)
    (omega sigma : ℝ) (k : PhysicalMomentum) (positive : 0<sigma) :
    frequencyResponsePencil event transfer (physicalFrequencyMomentum omega k) (dampedFourierClock omega sigma)=
      emOriginalJacobi (physicalFrequencyMomentum omega k)-(sigma:ℂ) •
        frequencyHalfPolarization event transfer (physicalFrequencyMomentum omega k) (dampedFourierClock omega sigma) := by
  unfold frequencyResponsePencil frequencyQuantumCorrection
  rw [damped_fourier_input_normalizer omega sigma k positive]

theorem damped_fourier_window_limit (event : DressedEvent) (transfer : PhysicalMomentum)
    (omega sigma : ℝ) (k : PhysicalMomentum) (positive : 0<sigma) :
    Tendsto (frequencyNormalizedWindow event transfer (physicalFrequencyMomentum omega k)
      (dampedFourierClock omega sigma)) atTop
      (𝓝 (frequencyResponsePencil event transfer (physicalFrequencyMomentum omega k)
        (dampedFourierClock omega sigma))) :=
  frequency_normalized_window_limit event transfer _ _
    (damped_fourier_source_domain omega sigma k positive)

theorem damped_fourier_window_tail (event : DressedEvent) (transfer : PhysicalMomentum)
    (omega sigma : ℝ) (k : PhysicalMomentum) (positive : 0<sigma)
    (T : ℝ) (future : 0≤T) (i j : Fin 289) :
    ‖frequencyResponsePencil event transfer (physicalFrequencyMomentum omega k) (dampedFourierClock omega sigma) i j-
      frequencyNormalizedWindow event transfer (physicalFrequencyMomentum omega k) (dampedFourierClock omega sigma) T i j‖ ≤
      Real.exp (-sigma*T)*‖emOriginalJacobi (physicalFrequencyMomentum omega k) i j‖+
        sigma*dressedSignalTailPrice event transfer (physicalFrequencyMomentum omega k) (dampedFourierClock omega sigma) T := by
  have original:=frequency_response_window_tail event transfer _ _
    (damped_fourier_source_domain omega sigma k positive) T future i j
  have difference : dampedFourierClock omega sigma-physicalFrequencyMomentum omega k 0=(sigma:ℂ) := by
    simp only [dampedFourierClock,physicalFrequencyMomentum,Fin.cases_zero]
    ring
  rw [difference,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive] at original
  have exponent : (physicalFrequencyMomentum omega k 0).re-(dampedFourierClock omega sigma).re= -sigma := by
    simp [dampedFourierClock,physicalFrequencyMomentum,Complex.mul_re]
  simpa only [exponent] using! original

/-- The same original spatial transfer and single-i source sheet clock are retained. -/
theorem damped_source_sheet_response (event : DressedEvent) (e s sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0<sigma) :
    frequencyResponsePencil event ((e^2:ℝ) • n) (frequencyRay e s n)
        (dampedFourierClock (sourceFrequency e s) sigma)=
      emOriginalJacobi (frequencyRay e s n)-(sigma:ℂ) •
        frequencyHalfPolarization event ((e^2:ℝ) • n) (frequencyRay e s n)
          (dampedFourierClock (sourceFrequency e s) sigma) := by
  have frequency : sourceFrequency e s=s*e^2 := by unfold sourceFrequency;ring
  simpa only [frequency,frequencyRay] using!
    damped_fourier_response event ((e^2:ℝ) • n) (sourceFrequency e s) sigma ((e^2:ℝ) • n) positive

end LowEnergy.GaussComposite.ActualDressedFrequencyHalf
