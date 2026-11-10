import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedStaticCorrectedReturn
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedZeroClockQuantumResidue

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LowEnergy.GaussComposite.ActualSourcePreparedZeroClockReturn
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationPhysicalNativePhotonFluxReturn
open ActualDressedFullCoulomb ActualDressedFrequencyHalf ActualDressedCorrectedGreen
open ActualDressedZeroClockVector ActualDressedEMQuantumThreshold ActualEMAction
open ActualSourcePreparedNoetherPi ActualSourcePreparedPhotonPoleRead
open ActualSourcePreparedStaticCorrectedReturn
open Filter Set
open scoped Topology BigOperators Matrix

attribute [local irreducible] sourcePreparedPiEntry sourcePreparedModeResponse
  sourcePreparedPhotonPoleResponse sourcePhotonLeftReaderCLM zeroClockQuantumResponse

/-- The actual source sheet supplies the original frequency-residue factorization
for this generated full response, without choosing a pole pivot. -/
theorem source_prepared_photon_frequency_residue (event : DressedEvent)
    (transfer : PhysicalMomentum) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n = 1) (lambda : ℂ) :
    ∀ᶠ e in scaleApproach,
      sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *ᵥ
          sourcePreparedModeResponse event transfer lambda
            (sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n) =
        sourcePreparedPhotonPoleResponse event transfer branch e.val
          (sourceSheet branch n unit e.val) n lambda •
            sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n := by
  filter_upwards [sourceWholePhotonResidue_factor branch n unit] with e factor
  unfold sourceWholePhotonFrequencyResidue
  rw [Matrix.smul_mulVec, factor]
  unfold sourcePreparedPhotonPoleResponse
  rw [source_photon_left_reader_original]
  unfold sourceNativeFrequencyPolarization
  exact smul_comm _ _ _

theorem source_prepared_static_pencil_threshold (event : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum)
    (regular : (zeroClockClearing event epsilon n).eval (0 : ℂ) ≠ 0)
    (balanced : PencilClockBalanced event epsilon n) :
    Tendsto (fun sigma : ℝ => sourcePreparedStaticPencil event epsilon sigma n)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockThresholdPencil event epsilon 0 n)) := by
  apply Tendsto.congr' _ (actual_zero_clock_threshold_pencil event epsilon 0 n regular balanced)
  filter_upwards [self_mem_nhdsWithin] with sigma positive
  exact (source_prepared_static_pencil_actual event epsilon sigma n positive).symm

/-- The normalized full quantum response survives as the original source Q0;
the clock-balance and clearing-chart obligations stay explicit. -/
theorem source_prepared_zero_clock_quantum_matrix (event : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum)
    (regular : (zeroClockClearing event epsilon n).eval (0 : ℂ) ≠ 0)
    (balanced : PencilClockBalanced event epsilon n) :
    Tendsto (fun sigma : ℝ => (sigma : ℂ) •
      (fun i j => sourcePreparedPiEntry event ((epsilon^2 : ℝ) • n) (sigma : ℂ) i j))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockQuantumResponse event epsilon 0 n)) := by
  have pencil := source_prepared_static_pencil_threshold event epsilon n regular balanced
  have original : Tendsto (fun _ : ℝ => emOriginalJacobi (frequencyRay epsilon 0 n))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (emOriginalJacobi (frequencyRay epsilon 0 n))) := tendsto_const_nhds
  have limit := original.sub pencil
  rw [actual_zero_clock_threshold_quantum event epsilon 0 n regular] at limit
  simpa only [sourcePreparedStaticPencil, sub_sub_cancel] using limit

theorem source_prepared_zero_clock_pole_read (event : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ)
    (regular : (zeroClockClearing event epsilon n).eval (0 : ℂ) ≠ 0)
    (balanced : PencilClockBalanced event epsilon n) :
    Tendsto (fun sigma : ℝ => (sigma : ℂ) *
        sourcePreparedPhotonPoleResponse event ((epsilon^2 : ℝ) • n) branch epsilon sheet n (sigma : ℂ))
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (sourcePhotonLeftReader branch epsilon sheet n
        (zeroClockQuantumResponse event epsilon 0 n *ᵥ
          sourceNativeFrequencyPolarization branch epsilon sheet n))) := by
  let U := sourceNativeFrequencyPolarization branch epsilon sheet n
  let L := sourcePhotonLeftReaderCLM branch epsilon sheet n
  have vector : Continuous (fun M : Matrix (Fin 289) (Fin 289) ℂ => M *ᵥ U) :=
    continuous_id.matrix_mulVec continuous_const
  have reading : Continuous (fun M : Matrix (Fin 289) (Fin 289) ℂ => L (M *ᵥ U)) :=
    L.continuous.comp vector
  have limit := (reading.tendsto _).comp
    (source_prepared_zero_clock_quantum_matrix event epsilon n regular balanced)
  have same : (fun sigma : ℝ => L (((sigma : ℂ) •
      (fun i j => sourcePreparedPiEntry event ((epsilon^2 : ℝ) • n) (sigma : ℂ) i j)) *ᵥ U)) =ᶠ[nhdsWithin 0 (Ioi 0)]
      (fun sigma : ℝ => (sigma : ℂ) * sourcePreparedPhotonPoleResponse event
        ((epsilon^2 : ℝ) • n) branch epsilon sheet n (sigma : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with sigma positive
    have paid : 0 < (sigma : ℂ).re := by simpa using positive
    rw [Matrix.smul_mulVec, map_smul, smul_eq_mul]
    unfold sourcePreparedPhotonPoleResponse
    rw [source_prepared_mode_response_actual event ((epsilon^2 : ℝ) • n) (sigma : ℂ) paid]
  have result := limit.congr' same
  simpa only [source_photon_left_reader_original, Function.comp_def, L, U] using result

end LowEnergy.GaussComposite.ActualSourcePreparedZeroClockReturn
