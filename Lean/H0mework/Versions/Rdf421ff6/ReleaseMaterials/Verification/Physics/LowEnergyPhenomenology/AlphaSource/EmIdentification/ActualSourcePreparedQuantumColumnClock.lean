import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedQuantumDriverCofactor
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMColumnThreshold

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LowEnergy.GaussComposite.ActualSourcePreparedQuantumColumnClock
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic ActualEMAction ActualDressedFullCoulomb
open ActualDressedCorrectedGreen ActualDressedUniformMaterialCoefficients
open ActualDressedPhysicalRayNumerator
open LowEnergy.GaussComposite.ActualDressedVisiblePole
open ActualDressedEMTensorClock ActualDressedOrderedStatic ActualDressedZeroClockFrequency
open ActualDressedEMZeroClockColumns ActualSourcePreparedEMEnclosure
open ActualSourcePreparedStaticCorrectedReturn ActualSourcePreparedTemporalEMConstraint
open ActualSourcePreparedN3MovingResponse
open ActualSourcePreparedTemporalQuantumWard ActualSourcePreparedTemporalQuantumIR
open ActualSourcePreparedQuantumDriverCofactor Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] commonClearedPencil commonJacobi commonNumerator
  commonDenominator commonDeterminant sourcePreparedFullGreenRead

private theorem polynomial_drive {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (J N : Matrix ι ι R) (d s : R) (E : ι → R) :
    s • (N *ᵥ ((d • J - s • N).adjugate *ᵥ E)) =
      J *ᵥ (d • ((d • J - s • N).adjugate *ᵥ E)) -
        (d • J - s • N).det • E := by
  have adj := congrArg (fun M : Matrix ι ι R => M *ᵥ E)
    (Matrix.mul_adjugate (d • J - s • N))
  rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at adj
  rw [Matrix.mulVec_smul]
  exact (sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp adj).trans (add_comm _ _))).symm

/-- Both numerators are restrictions of the same original cofactor occurrence.
The quantum numerator is generated from its temporal EM column equation. -/
theorem source_quantum_numerator_em_column (event : DressedEvent) (n : PhysicalMomentum) :
    sourceQuantumDriverNumerator event n =
      commonJacobi n *ᵥ commonEMSourceColumn event n 0 -
        commonDeterminant event n • (fun i => MvPolynomial.C (sourceTemporalEMForce i)) := by
  unfold sourceQuantumDriverNumerator commonEMSourceColumn commonDeterminant commonClearedPencil
  change _ = commonJacobi n *ᵥ (commonDenominator event n •
      ((commonDenominator event n • commonJacobi n -
        (MvPolynomial.X 1 : Parameters) • commonNumerator event n).adjugate *ᵥ
          (fun i => MvPolynomial.C (sourceTemporalEMForce i)))) - _
  exact polynomial_drive _ _ _ _ _

/-- Only the actual temporal column needs clock divisibility. The complete
quantum driver inherits it on the same spatial-clock carrier. -/
theorem source_quantum_driver_clock_from_column (event : DressedEvent) (n : PhysicalMomentum)
    (column : ∀ i, (X : (ℂ[X])[X]) ^ sourceClockOrder event n ∣
      staticIRClockSlice (commonEMSourceColumn event n 0 i)) :
    ∀ i, (X : (ℂ[X])[X]) ^ sourceClockOrder event n ∣
      staticIRClockSlice (sourceQuantumDriverNumerator event n i) := by
  intro i
  have same := congrArg (fun v : Fin 289 → Parameters => staticIRClockSlice (v i))
    (source_quantum_numerator_em_column event n)
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    map_sub, map_sum, map_mul] at same
  rw [same]
  apply dvd_sub
  · apply Finset.dvd_sum
    intro j _
    exact dvd_mul_of_dvd_right (column j) _
  · exact dvd_mul_of_dvd_left (source_clock_factor event n) _

/-- The actual prepared temporal field is the original whole EM forcing column. -/
theorem source_quantum_field_em_column (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma)
    (regular : correctedDet event epsilon 0 sigma n ≠ 0) :
    sourceTemporalCorrectedField event epsilon sigma n =
      correctedEMColumn event epsilon 0 sigma n 0 := by
  unfold sourceTemporalCorrectedField correctedEMColumn sourceTemporalEMForce
  rw [source_prepared_full_green_original event epsilon sigma n positive regular]

/-- This equation consumes the entire original quantum/contact matrix and its
actual external field; it does not isolate a selected insertion. -/
theorem source_quantum_driver_em_column (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (positive : 0 < sigma)
    (regular : correctedDet event e.val 0 sigma n ≠ 0) :
    sourceTemporalActualQuantumDriver event e sigma n =
      emOriginalJacobi (frequencyRay e.val 0 n) *ᵥ
        correctedEMColumn event e.val 0 sigma n 0 - sourceTemporalEMForce := by
  have equation := source_temporal_corrected_field_equation event e.val sigma n positive regular
  change (emOriginalJacobi (frequencyRay e.val 0 n) -
    sourcePreparedClockQuantumMatrix event e.val sigma n) *ᵥ
    sourceTemporalCorrectedField event e.val sigma n = sourceTemporalEMForce at equation
  rw [Matrix.sub_mulVec] at equation
  have driver : sourceTemporalActualQuantumDriver event e sigma n =
      emOriginalJacobi (frequencyRay e.val 0 n) *ᵥ
        sourceTemporalCorrectedField event e.val sigma n - sourceTemporalEMForce :=
    (sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp equation).trans (add_comm _ _))).symm
  rw [driver, source_quantum_field_em_column event e.val sigma n positive regular]

/-- The clock return of the actual quantum drive uses the same original EM
column, without requiring the entire quantum pencil to be clock-balanced. -/
theorem source_quantum_driver_column_clock_return (event : DressedEvent) (e : scaleDomain)
    (n : PhysicalMomentum)
    (regular : (zeroClockFrequencyDenominator event e.val n).eval (0 : ℂ) ≠ 0)
    (finite : EMColumnsClockFinite event e.val n) :
    Tendsto (fun sigma : ℝ => sourceTemporalActualQuantumDriver event e sigma n)
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (emOriginalJacobi (frequencyRay e.val 0 n) *ᵥ
        zeroClockEMColumnRead event e.val 0 n 0 - sourceTemporalEMForce)) := by
  have column := actual_zero_clock_em_column event e.val 0 n 0 regular finite
  have multiply : Continuous (fun v : Fin 289 → ℂ =>
      emOriginalJacobi (frequencyRay e.val 0 n) *ᵥ v) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  have limit := ((multiply.tendsto _).comp column).sub_const sourceTemporalEMForce
  apply Tendsto.congr' _ limit
  filter_upwards [source_zero_clock_frequency_chart event e.val n 0 regular] with sigma chart
  exact (source_quantum_driver_em_column event e sigma n chart.1 chart.2).symm

end LowEnergy.GaussComposite.ActualSourcePreparedQuantumColumnClock
