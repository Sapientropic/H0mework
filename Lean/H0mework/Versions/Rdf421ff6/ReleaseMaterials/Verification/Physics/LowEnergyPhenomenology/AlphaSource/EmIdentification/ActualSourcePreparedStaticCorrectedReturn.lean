import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedPhotonPoleRead
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCorrectedGreen

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LowEnergy.GaussComposite.ActualSourcePreparedStaticCorrectedReturn
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedFullCoulomb ActualDressedFrequencyHalf ActualDressedSylvester
open ActualDressedSignal
open ActualDressedPhysicalRayNumerator ActualDressedCorrectedGreen ActualEMAction
open ActualSourcePreparedNoetherPi ActualSourcePreparedPhotonPoleRead
open scoped Matrix BigOperators

attribute [local irreducible] frequencyHalfPolarization dressedSignalHalfOperator
  frequencyResponsePencil correctedGreen emOriginalJacobi sourcePreparedPiEntry

/-- The original input-integral normalization supplies sigma once. -/
def sourcePreparedStaticPencil (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) ℂ :=
  let response : Matrix (Fin 289) (Fin 289) ℂ :=
    fun i j => sourcePreparedPiEntry event ((epsilon^2 : ℝ) • n) (sigma : ℂ) i j
  emOriginalJacobi (frequencyRay epsilon 0 n) - (sigma : ℂ) • response

private theorem static_prepared_polarization (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) :
    frequencyHalfPolarization event ((epsilon^2 : ℝ) • n) (frequencyRay epsilon 0 n)
      (dampedFourierClock (sourceFrequency epsilon 0) sigma) =
    (fun i j => sourcePreparedPiEntry event ((epsilon^2 : ℝ) • n) (sigma : ℂ) i j) := by
  have clock : dampedFourierClock (sourceFrequency epsilon 0) sigma = (sigma : ℂ) := by
    simp [dampedFourierClock, sourceFrequency]
  have static : frequencyRay epsilon 0 n 0 = 0 := by
    simp [frequencyRay, physicalFrequencyMomentum]
  have paid : 0 < (sigma : ℂ).re := by simpa using positive
  ext i j
  rw [clock]
  unfold frequencyHalfPolarization
  exact (dressed_static_polarization_actual event ((epsilon^2 : ℝ) • n)
    (frequencyRay epsilon 0 n) static (sigma : ℂ) paid i j).trans
    (source_prepared_pi_actual event ((epsilon^2 : ℝ) • n) (sigma : ℂ) paid i j).symm

/-- The source-point field response is the actual existing corrected pencil. -/
theorem source_prepared_static_pencil_actual (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) :
    sourcePreparedStaticPencil event epsilon sigma n =
      frequencyResponsePencil event ((epsilon^2 : ℝ) • n) (frequencyRay epsilon 0 n)
        (dampedFourierClock (sourceFrequency epsilon 0) sigma) := by
  rw [damped_source_sheet_response event epsilon 0 sigma n positive,
    static_prepared_polarization event epsilon sigma n positive]
  rfl

/-- The old full Green consumes the generated preparation response on its exact
source determinant region; no replacement propagator or inverse is introduced. -/
theorem source_prepared_static_green_inverse (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma)
    (regular : correctedDet event epsilon 0 sigma n ≠ 0) :
    sourcePreparedStaticPencil event epsilon sigma n * correctedGreen event epsilon 0 sigma n = 1 ∧
      correctedGreen event epsilon 0 sigma n * sourcePreparedStaticPencil event epsilon sigma n = 1 := by
  rw [source_prepared_static_pencil_actual event epsilon sigma n positive]
  exact actual_corrected_green_inverse event epsilon 0 sigma n positive regular

theorem source_prepared_static_response_equation (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma)
    (regular : correctedDet event epsilon 0 sigma n ≠ 0) (forcing : Fin 289 → ℂ) :
    sourcePreparedStaticPencil event epsilon sigma n *ᵥ
      correctedResponse event epsilon 0 sigma n forcing = forcing := by
  rw [source_prepared_static_pencil_actual event epsilon sigma n positive]
  exact actual_corrected_response_equation event epsilon 0 sigma n positive regular forcing

end LowEnergy.GaussComposite.ActualSourcePreparedStaticCorrectedReturn
