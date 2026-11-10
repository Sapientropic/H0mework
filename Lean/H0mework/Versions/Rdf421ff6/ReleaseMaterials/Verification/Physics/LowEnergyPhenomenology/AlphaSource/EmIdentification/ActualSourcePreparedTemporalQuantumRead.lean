import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedTemporalSchur

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedTemporalQuantumRead
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCharacteristic
open PreparationVacuumOriginalGreenFeedback PreparationVacuumStaticPoleResponse
open PreparationPhysicalVoltageCompleteReturn
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open ActualEMAction ActualEMDressedSchur ActualEMDressedConstraint ActualDressedNullNative ActualEMResponseSplit
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedNoetherCoulombUnit
open ActualSourcePreparedNoetherPi ActualSourcePreparedStaticCorrectedReturn
open ActualSourcePreparedEMEnclosure ActualSourcePreparedN3MovingResponse ActualSourcePreparedN3EMChargeRead
open ActualSourcePreparedStaticNativeConstraint ActualSourcePreparedTemporalEMConstraint
open ActualSourcePreparedTemporalQuantumWard ActualSourcePreparedTemporalSchur
open scoped Matrix BigOperators
attribute [local irreducible] sourceGreen sourceNull sourceNullLift emOriginalJacobi

theorem source_temporal_detector_null_column (p : Fin 4 → ℂ) (static : p 0=0) (row : Fin 9) :
    dotProduct sourceTemporalEMForce (originalNullColumn p row)=0 := by
  have opposite : (-p) 0=0 := by simp only [Pi.neg_apply, static, neg_zero]
  have rows := congrFun (source_em_temporal_cokernel (-p) opposite) row
  rw [original_null_cokernel] at rows
  simp only [Pi.zero_apply] at rows
  change dotProduct (originalNullColumn (-(-p)) row) sourceTemporalEMForce = 0 at rows
  rw [neg_neg, dotProduct_comm] at rows
  exact rows

/-- The temporal detector and null lift are opposite-covector restrictions of
one original source table, not an assumed identification of left and right rows. -/
theorem source_temporal_detector_null_lift (p : Fin 4 → ℂ) (static : p 0=0) (x : Fin 9 → ℂ) :
    dotProduct sourceTemporalEMForce (sourceNullLift p x)=0 := by
  conv_lhs => arg 2; arg 2; rw [pi_eq_sum_univ' x]
  rw [map_sum, dotProduct_sum]
  simp only [map_smul, original_null_lift_single, dotProduct_smul,
    source_temporal_detector_null_column p static, smul_zero, Finset.sum_const_zero]

private theorem static_time_zero (e : scaleDomain) (n : PhysicalMomentum) :
    frequencyRay e.val 0 n 0=0 := by
  change -Complex.I*((0*e.val^2 : ℝ) : ℂ)=0
  simp only [zero_mul, Complex.ofReal_zero, mul_zero]

/-- No feedback chart is required here: the original native left equation and
the actual complete pencil return the whole field plus its original null part. -/
theorem source_temporal_actual_native_field (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (small : e.val^2 ≤ staticRadius)
    (positive : 0 < sigma) (regular : correctedDet event e.val 0 sigma n ≠ 0) :
    let a := sourceTemporalCorrectedField event e.val sigma n
    a = sourceNull (frequencyRay e.val 0 n)*ᵥa + sourceNativeStaticMatrix e.val n*ᵥ
      (sourceTemporalEMForce + sourcePreparedClockQuantumMatrix event e.val sigma n*ᵥa) := by
  dsimp only
  let a := sourceTemporalCorrectedField event e.val sigma n
  have equation := source_temporal_corrected_field_equation event e.val sigma n positive regular
  change (emOriginalJacobi (frequencyRay e.val 0 n)-sourcePreparedClockQuantumMatrix event e.val sigma n)*ᵥa =
    sourceTemporalEMForce at equation
  rw [Matrix.sub_mulVec] at equation
  have native : sourceGreen (sourceTemporalStaticPoint e n unit small) *
      originalJacobi (sourceTemporalStaticPoint e n unit small).val =
      1-sourceNull (sourceTemporalStaticPoint e n unit small).val := by
    simpa only [sourceNull] using sourceGreen_original_left (sourceTemporalStaticPoint e n unit small)
  have native_point : sourceNativeStaticMatrix e.val n =
      sourceGreen (sourceTemporalStaticPoint e n unit small) := by
    simpa only [sourceTemporalStaticPoint] using source_native_static_original e n unit small
  rw [←native_point] at native
  have ray : (sourceTemporalStaticPoint e n unit small).val = frequencyRay e.val 0 n :=
    source_static_spatial_ray e.val n
  rw [ray, ←em_jacobi_source] at native
  have paid := congrArg (fun v => sourceNativeStaticMatrix e.val n*ᵥv) equation
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, native, Matrix.sub_mulVec, Matrix.one_mulVec] at paid
  rw [Matrix.mulVec_add]
  linear_combination paid

/-- The complete temporal correction is native-propagated Pi acting on the
actual corrected field. Only the direct null read is eliminated. -/
theorem source_temporal_actual_quantum_read (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (small : e.val^2 ≤ staticRadius)
    (positive : 0 < sigma) (regular : correctedDet event e.val 0 sigma n ≠ 0) :
    sourceN3TemporalEMCoefficient event e.val sigma n - noetherPairScale^2 *
      dotProduct sourceTemporalEMForce (sourceNativeStaticMatrix e.val n*ᵥsourceTemporalEMForce) =
      noetherPairScale^2 * dotProduct sourceTemporalEMForce
        (sourceNativeStaticMatrix e.val n*ᵥ(sourcePreparedClockQuantumMatrix event e.val sigma n*ᵥ
          sourceTemporalCorrectedField event e.val sigma n)) := by
  have returned := source_temporal_actual_native_field event e sigma n unit small positive regular
  dsimp only at returned
  have read := congrArg (dotProduct sourceTemporalEMForce) returned
  rw [dotProduct_add, ←source_null_coordinates_generated,
    source_temporal_detector_null_lift _ (static_time_zero e n), zero_add,
    Matrix.mulVec_add, dotProduct_add] at read
  unfold sourceN3TemporalEMCoefficient sourcePreparedEMTensorRead emResponseTensor
  rw [Matrix.mul_assoc]
  change noetherPairScale^2 * dotProduct sourceTemporalEMForce
    (sourcePreparedFullGreenRead event e.val sigma n*ᵥsourceTemporalEMForce)-_=_
  change dotProduct sourceTemporalEMForce
    (sourcePreparedFullGreenRead event e.val sigma n*ᵥsourceTemporalEMForce)=_ at read
  linear_combination noetherPairScale^2 * read

def sourceTemporalNativeQuantumArm (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (A : Matrix (Fin 289) (Fin 289) ℂ) : ℂ :=
  noetherPairScale^2 * dotProduct sourceTemporalEMForce
    (sourceNativeStaticMatrix e.val n*ᵥ(((sigma : ℂ) • A)*ᵥ
      sourceTemporalCorrectedField event e.val sigma n))

/-- The same complete actual time field consumes moving light, heavy, outside
and tail. These are polarization arms, not independent light propagators. -/
theorem source_temporal_actual_moving_quantum_read (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (small : e.val^2 ≤ staticRadius)
    (reference : SourceCoordinateSlice) (bits : ℕ)
    (positive : 0 < sigma) (regular : correctedDet event e.val 0 sigma n ≠ 0) :
    sourceN3TemporalEMCoefficient event e.val sigma n - noetherPairScale^2 *
      dotProduct sourceTemporalEMForce (sourceNativeStaticMatrix e.val n*ᵥsourceTemporalEMForce) =
    sourceTemporalNativeQuantumArm event e sigma n (sourcePreparedMovingLightMatrix event e.val sigma n reference bits) +
      sourceTemporalNativeQuantumArm event e sigma n (sourcePreparedMovingHeavyMatrix event e.val sigma n reference bits) +
      sourceTemporalNativeQuantumArm event e sigma n (sourcePreparedMovingOutsideMatrix event e.val sigma n bits) +
      sourceTemporalNativeQuantumArm event e sigma n (sourcePreparedMovingTailMatrix event e.val sigma n bits) := by
  have quantum : sourcePreparedClockQuantumMatrix event e.val sigma n = (sigma : ℂ) •
      (sourcePreparedMovingLightMatrix event e.val sigma n reference bits +
        sourcePreparedMovingHeavyMatrix event e.val sigma n reference bits +
        sourcePreparedMovingOutsideMatrix event e.val sigma n bits +
        sourcePreparedMovingTailMatrix event e.val sigma n bits) := by
    unfold sourcePreparedClockQuantumMatrix
    change (sigma : ℂ) • (fun i j => sourcePreparedPiEntry event ((e.val^2 : ℝ) • n) (sigma : ℂ) i j :
      Matrix (Fin 289) (Fin 289) ℂ) = _
    rw [source_prepared_moving_pi_partition event e.val sigma n reference bits positive]
  rw [source_temporal_actual_quantum_read event e sigma n unit small positive regular, quantum]
  simp only [sourceTemporalNativeQuantumArm, smul_add, Matrix.add_mulVec, Matrix.mulVec_add,
    dotProduct_add, mul_add]

end LowEnergy.GaussComposite.ActualSourcePreparedTemporalQuantumRead
