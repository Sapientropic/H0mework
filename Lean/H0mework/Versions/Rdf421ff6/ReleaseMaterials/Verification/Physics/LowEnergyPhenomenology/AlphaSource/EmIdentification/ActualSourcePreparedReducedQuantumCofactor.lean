import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedClockReducedPencil

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedReducedQuantumCofactor
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic
open ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualSourcePreparedFourClockCarrier ActualSourcePreparedClockReducedPencil
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedTemporalQuantumWard
open ActualDressedEMTensorClock ActualDressedOrderedStatic ActualDressedZeroDamping
open ActualDressedUniformMaterialCoefficients ActualDressedUniformClockNonzero
open ActualSourcePreparedStaticCorrectedReturn ActualSourcePreparedQuantumColumnClock
open ActualSourcePreparedTemporalQuantumIR ActualEMAction
open ActualSourcePreparedN3EMChargeRead ActualSourcePreparedEMEnclosure ActualDressedNoetherCoulombUnit
open ActualEMResponseSplit ActualEMDressedSchur ActualDressedNullNative ActualEMDressedConstraint
open PreparationVacuumOriginalGreenFeedback
open scoped Matrix
attribute [local irreducible] sourceClockReducedPencil sourceFourClockDenominator
  commonDenominator sourcePreparedStaticPencil emOriginalJacobi sourceTemporalCorrectedField

def sourceReducedClockMatrix (event : DressedEvent) (n : PhysicalMomentum) (epsilon sigma : ℝ) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  (sourceClockReducedPencil event n).map (sourceClockEval epsilon sigma)

def sourceReducedClockDeterminant (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) : ℂ :=
  (sourceReducedClockMatrix event n epsilon sigma).det

def sourceReducedClockFieldNumerator (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) : Fin 289 → ℂ :=
  ((sigma : ℂ)^3 * sourceClockEval epsilon sigma (sourceFourClockDenominator event n)) •
    ((sourceReducedClockMatrix event n epsilon sigma).adjugate *ᵥ sourceTemporalEMForce)

private theorem cofactor_field {R ι : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] (K : Matrix ι ι R) (a E : ι → R) (c : R)
    (field : K *ᵥ a = c • E) : K.det • a = c • (K.adjugate *ᵥ E) := by
  have adj := congrArg (fun M : Matrix ι ι R => M *ᵥ a) (Matrix.adjugate_mul K)
  rw [← Matrix.mulVec_mulVec, field, Matrix.mulVec_smul, Matrix.smul_mulVec,
    Matrix.one_mulVec] at adj
  exact adj.symm

/-- The cofactor is read from the actual restriction of the same common K.
The original source field equation pays its entire forcing and clock factor. -/
theorem source_reduced_clock_actual_field_clear (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) (positive : 0 < sigma)
    (regular : correctedDet event epsilon 0 sigma n ≠ 0) :
    sourceReducedClockDeterminant event n epsilon sigma •
      sourceTemporalCorrectedField event epsilon sigma n =
      sourceReducedClockFieldNumerator event n epsilon sigma := by
  exact cofactor_field (sourceReducedClockMatrix event n epsilon sigma)
    (sourceTemporalCorrectedField event epsilon sigma n) sourceTemporalEMForce
    ((sigma : ℂ)^3 * sourceClockEval epsilon sigma (sourceFourClockDenominator event n))
    (source_clock_reduced_actual_field event n epsilon sigma positive regular)

theorem source_reduced_clock_denominator_nonzero (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) (positive : 0 < sigma) :
    sourceClockEval epsilon sigma (sourceFourClockDenominator event n) ≠ 0 := by
  have factor := congrArg (sourceClockEval epsilon sigma)
    (source_four_clock_denominator_factor event n)
  have nonzero : sourceClockEval epsilon sigma (sourceFourClockClearing event n) ≠ 0 := by
    change (clockSpecialize epsilon (staticIRClockSlice (commonDenominator event n))).eval
      (sigma : ℂ) ≠ 0
    rw [ir_clock_specialize, damping_slice_eval]
    exact actual_common_ir_denominator_nonzero event n epsilon sigma 0 positive
  intro zero
  simp only [map_mul, zero, mul_zero] at factor
  exact nonzero factor.symm

/-- Regularity is inherited from the original full Green, rather than supplied
as a new reduced determinant assumption. -/
theorem source_reduced_clock_determinant_nonzero (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) (positive : 0 < sigma)
    (regular : correctedDet event epsilon 0 sigma n ≠ 0) :
    sourceReducedClockDeterminant event n epsilon sigma ≠ 0 := by
  have native := Matrix.det_ne_zero_of_right_inverse
    (source_prepared_static_green_inverse event epsilon sigma n positive regular).1
  have factor := mul_ne_zero (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr positive.ne'))
    (source_reduced_clock_denominator_nonzero event n epsilon sigma positive)
  rw [sourceReducedClockDeterminant, sourceReducedClockMatrix,
    source_clock_reduced_pencil_actual event n epsilon sigma positive, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ factor) native

def sourceReducedClockDriverNumerator (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) : Fin 289 → ℂ :=
  emOriginalJacobi (frequencyRay epsilon 0 n) *ᵥ
    sourceReducedClockFieldNumerator event n epsilon sigma -
      sourceReducedClockDeterminant event n epsilon sigma • sourceTemporalEMForce

/-- The complete quantum/contact drive uses the same field cofactor and the
same determinant. Its numerator includes the original forcing subtraction. -/
theorem source_reduced_clock_actual_driver_clear (event : DressedEvent) (n : PhysicalMomentum)
    (e : scaleDomain) (sigma : ℝ) (positive : 0 < sigma)
    (regular : correctedDet event e.val 0 sigma n ≠ 0) :
    sourceReducedClockDeterminant event n e.val sigma •
      sourceTemporalActualQuantumDriver event e sigma n =
      sourceReducedClockDriverNumerator event n e.val sigma := by
  have driver := source_quantum_driver_em_column event e sigma n positive regular
  rw [← source_quantum_field_em_column event e.val sigma n positive regular] at driver
  rw [driver, smul_sub, ← Matrix.mulVec_smul,
    source_reduced_clock_actual_field_clear event n e.val sigma positive regular]
  rfl

private theorem vector_fraction {ι : Type*} (d : ℂ) (a N : ι → ℂ)
    (nonzero : d ≠ 0) (clear : d • a = N) (i : ι) : a i = N i / d := by
  apply (eq_div_iff nonzero).mpr
  have entry := congrFun clear i
  change d * a i = N i at entry
  exact (mul_comm _ _).trans entry

theorem source_reduced_clock_actual_field_fraction (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) (positive : 0 < sigma)
    (regular : correctedDet event epsilon 0 sigma n ≠ 0) (i : Fin 289) :
    sourceTemporalCorrectedField event epsilon sigma n i =
      sourceReducedClockFieldNumerator event n epsilon sigma i /
        sourceReducedClockDeterminant event n epsilon sigma :=
  vector_fraction _ _ _
    (source_reduced_clock_determinant_nonzero event n epsilon sigma positive regular)
    (source_reduced_clock_actual_field_clear event n epsilon sigma positive regular) i

theorem source_reduced_clock_actual_driver_fraction (event : DressedEvent) (n : PhysicalMomentum)
    (e : scaleDomain) (sigma : ℝ) (positive : 0 < sigma)
    (regular : correctedDet event e.val 0 sigma n ≠ 0) (i : Fin 289) :
    sourceTemporalActualQuantumDriver event e sigma n i =
      sourceReducedClockDriverNumerator event n e.val sigma i /
        sourceReducedClockDeterminant event n e.val sigma :=
  vector_fraction _ _ _
    (source_reduced_clock_determinant_nonzero event n e.val sigma positive regular)
    (source_reduced_clock_actual_driver_clear event n e sigma positive regular) i

theorem source_reduced_clock_temporal_coefficient (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) (positive : 0 < sigma)
    (regular : correctedDet event epsilon 0 sigma n ≠ 0) :
    sourceN3TemporalEMCoefficient event epsilon sigma n =
      noetherPairScale^2 * dotProduct sourceTemporalEMForce
        (sourceReducedClockFieldNumerator event n epsilon sigma) /
          sourceReducedClockDeterminant event n epsilon sigma := by
  have clear := congrArg (dotProduct sourceTemporalEMForce)
    (source_reduced_clock_actual_field_clear event n epsilon sigma positive regular)
  simp only [dotProduct_smul, smul_eq_mul] at clear
  have coefficient : sourceN3TemporalEMCoefficient event epsilon sigma n =
      noetherPairScale^2 * dotProduct sourceTemporalEMForce
        (sourceTemporalCorrectedField event epsilon sigma n) := by
    unfold sourceN3TemporalEMCoefficient sourcePreparedEMTensorRead emResponseTensor
    rw [Matrix.mul_assoc]
    unfold sourceTemporalCorrectedField sourceTemporalEMForce
    rfl
  rw [coefficient]
  apply (eq_div_iff
    (source_reduced_clock_determinant_nonzero event n epsilon sigma positive regular)).mpr
  calc
    _ = noetherPairScale^2 * (sourceReducedClockDeterminant event n epsilon sigma *
        dotProduct sourceTemporalEMForce (sourceTemporalCorrectedField event epsilon sigma n)) := by ring
    _ = _ := by rw [clear]

/-- All nine original source rows annihilate the complete driver numerator
even outside a regular Green chart. No EM or contact arm is dropped. -/
theorem source_reduced_clock_driver_cokernel (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) :
    sourceCokernel (frequencyRay epsilon 0 n)
      (sourceReducedClockDriverNumerator event n epsilon sigma) = 0 := by
  have static : frequencyRay epsilon 0 n 0 = 0 := by
    change -Complex.I*((0*epsilon^2 : ℝ) : ℂ)=0
    simp only [zero_mul, Complex.ofReal_zero, mul_zero]
  have classical : ∀ a : Fin 289 → ℂ,
      sourceCokernel (frequencyRay epsilon 0 n)
        (emOriginalJacobi (frequencyRay epsilon 0 n) *ᵥ a) = 0 := by
    intro a
    rw [em_jacobi_source]
    exact (source_compatibility_nine _ _).mp (source_compatibility_euler _ _)
  unfold sourceReducedClockDriverNumerator
  rw [map_sub, map_smul, classical, source_em_temporal_cokernel _ static, smul_zero, sub_self]

end LowEnergy.GaussComposite.ActualSourcePreparedReducedQuantumCofactor
