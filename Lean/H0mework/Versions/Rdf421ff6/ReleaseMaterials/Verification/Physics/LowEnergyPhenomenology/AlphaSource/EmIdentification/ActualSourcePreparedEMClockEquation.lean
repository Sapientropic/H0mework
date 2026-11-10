import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMTwoClockCarrier
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedReducedQuantumCofactor

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedEMClockEquation
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedUniformMaterialCoefficients ActualDressedOrderedStatic
open ActualDressedZeroDamping ActualSourcePreparedFourClockCarrier
open ActualDressedCorrectedGreen
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedReducedQuantumCofactor
open ActualSourcePreparedEMTwoClockCarrier ActualSourcePreparedTemporalEMConstraint
open ActualSourcePreparedTemporalQuantumWard ActualDressedEMTensorClock
open scoped Matrix BigOperators
attribute [local irreducible] commonNumerator commonDenominator commonJacobi sourceClockReducedPencil
  sourceFourClockResponseNumerator sourceEMTwoClockResponseNumerator sourceFourClockDenominator
  sourceFourClockOrder sourceFourClockClearing sourceTemporalEMForce

def sourceEMClockForce (i : Fin 289) : (ℂ[X])[X] := C (C (sourceTemporalEMForce i))

attribute [local irreducible] sourceEMClockForce sourceEMClockNumerator
  sourceFourClockNumerator sourceEMTwoClockNumerator

def sourceEMClockJacobiRow (n : PhysicalMomentum) (j : Fin 289) : (ℂ[X])[X] :=
  ∑ i : Fin 289, sourceEMClockForce i * staticIRClockSlice (commonJacobi n i j)

private theorem original_numerator_row (event : DressedEvent) (n : PhysicalMomentum) (j : Fin 289) :
    sourceEMClockNumerator event n j =
      ∑ i : Fin 289, sourceEMClockForce i * staticIRClockSlice (commonNumerator event n i j) := by
  unfold sourceEMClockNumerator sourceEMClockForce
  simp only [map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp [staticIRClockSlice]

/-- The stronger EM quotient removes two clock powers from the corresponding
row of the same full numerator, before spatial specialization. -/
theorem source_em_clock_full_response_row (event : DressedEvent) (n : PhysicalMomentum)
    (j : Fin 289) :
    ∑ i : Fin 289, sourceEMClockForce i * sourceFourClockResponseNumerator event n i j =
      X^2 * sourceEMTwoClockResponseNumerator event n j := by
  apply mul_left_cancel₀ (pow_ne_zero (sourceFourClockOrder event n)
    (X_ne_zero : (X : (ℂ[X])[X]) ≠ 0))
  calc
    _ = ∑ i : Fin 289, sourceEMClockForce i *
        (X^sourceFourClockOrder event n * sourceFourClockResponseNumerator event n i j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i : Fin 289, sourceEMClockForce i * sourceFourClockNumerator event n i j := by
      simp_rw [source_four_clock_response_factor]
    _ = X^4 * sourceEMClockNumerator event n j := by
      rw [original_numerator_row]
      simp only [sourceFourClockNumerator, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = X^2 * sourceEMTwoClockNumerator event n j := by
      unfold sourceEMTwoClockNumerator
      ring
    _ = _ := by
      rw [← source_em_two_clock_response_factor]
      ring

def sourceEMClockReducedRow (event : DressedEvent) (n : PhysicalMomentum)
    (j : Fin 289) : (ℂ[X])[X] :=
  X * sourceFourClockDenominator event n * sourceEMClockJacobiRow n j -
    sourceEMTwoClockResponseNumerator event n j

/-- All original Jacobi columns and full polarization remain in this exact
source row factor. It is not a balance assumption on the other 288 rows. -/
theorem source_em_clock_reduced_pencil_row (event : DressedEvent) (n : PhysicalMomentum)
    (j : Fin 289) :
    ∑ i : Fin 289, sourceEMClockForce i * sourceClockReducedPencil event n i j =
      X^2 * sourceEMClockReducedRow event n j := by
  simp only [sourceClockReducedPencil, sourceClockReducedNumerator, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  rw [source_em_clock_full_response_row]
  unfold sourceEMClockReducedRow sourceEMClockJacobiRow
  rw [mul_sub]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem clock_force_eval (eps sigma : ℝ) (i : Fin 289) :
    sourceClockEval eps sigma (sourceEMClockForce i) = sourceTemporalEMForce i := by
  simp [sourceClockEval, clockSpecialize, sourceEMClockForce]

private theorem clock_X_eval (eps sigma : ℝ) :
    sourceClockEval eps sigma (X : (ℂ[X])[X]) = (sigma : ℂ) := by
  simp [sourceClockEval, clockSpecialize]

private theorem row_contract {ι : Type*} [Fintype ι]
    (E a : ι → ℂ) (K : Matrix ι ι ℂ) :
    dotProduct E (K *ᵥ a) = ∑ j, (∑ i, E i * K i j) * a j := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The actual full G E0 field consumes the source row after its two clock
factors cancel. No endpoint or normalized forcing is supplied. -/
theorem source_em_clock_reduced_actual_field (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (positive : 0 < sigma)
    (regular : correctedDet event eps 0 sigma n ≠ 0) :
    ∑ j : Fin 289, sourceClockEval eps sigma (sourceEMClockReducedRow event n j) *
      sourceTemporalCorrectedField event eps sigma n j =
      (sigma : ℂ) * sourceClockEval eps sigma (sourceFourClockDenominator event n) *
        dotProduct sourceTemporalEMForce sourceTemporalEMForce := by
  have field := congrArg (dotProduct sourceTemporalEMForce)
    (source_clock_reduced_actual_field event n eps sigma positive regular)
  rw [row_contract] at field
  simp only [dotProduct_smul, smul_eq_mul] at field
  have rows (j : Fin 289) := congrArg (sourceClockEval eps sigma)
    (source_em_clock_reduced_pencil_row event n j)
  simp only [map_sum, map_mul, map_pow, clock_force_eval, clock_X_eval] at rows
  change (∑ j, (∑ i, sourceTemporalEMForce i *
    sourceClockEval eps sigma (sourceClockReducedPencil event n i j)) *
      sourceTemporalCorrectedField event eps sigma n j) = _ at field
  simp_rw [rows] at field
  have factored : (sigma : ℂ)^2 *
      (∑ j : Fin 289, sourceClockEval eps sigma (sourceEMClockReducedRow event n j) *
        sourceTemporalCorrectedField event eps sigma n j) =
      (sigma : ℂ)^3 * sourceClockEval eps sigma (sourceFourClockDenominator event n) *
        dotProduct sourceTemporalEMForce sourceTemporalEMForce := by
    simpa only [Finset.mul_sum, mul_assoc] using field
  apply mul_left_cancel₀ (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr positive.ne'))
  calc
    _ = (sigma : ℂ)^3 * sourceClockEval eps sigma (sourceFourClockDenominator event n) *
        dotProduct sourceTemporalEMForce sourceTemporalEMForce := factored
    _ = _ := by ring

/-- The same actual field cofactor now consumes the lower-clock EM equation
with the original det K and its complete sigma-cubed field numerator. -/
theorem source_em_clock_reduced_cofactor_field (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (positive : 0 < sigma)
    (regular : correctedDet event eps 0 sigma n ≠ 0) :
    ∑ j : Fin 289, sourceClockEval eps sigma (sourceEMClockReducedRow event n j) *
      sourceReducedClockFieldNumerator event n eps sigma j =
      sourceReducedClockDeterminant event n eps sigma *
        ((sigma : ℂ) * sourceClockEval eps sigma (sourceFourClockDenominator event n) *
          dotProduct sourceTemporalEMForce sourceTemporalEMForce) := by
  rw [← source_reduced_clock_actual_field_clear event n eps sigma positive regular]
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    _ = sourceReducedClockDeterminant event n eps sigma *
        ∑ j : Fin 289, sourceClockEval eps sigma (sourceEMClockReducedRow event n j) *
          sourceTemporalCorrectedField event eps sigma n j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [source_em_clock_reduced_actual_field event n eps sigma positive regular]

end LowEnergy.GaussComposite.ActualSourcePreparedEMClockEquation
