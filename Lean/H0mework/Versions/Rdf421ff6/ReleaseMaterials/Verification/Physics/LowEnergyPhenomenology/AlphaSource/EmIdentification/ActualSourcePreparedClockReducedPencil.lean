import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedFourClockCarrier

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedClockReducedPencil
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualEMAction ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedUniformMaterialCoefficients ActualDressedOrderedStatic ActualDressedZeroDamping
open ActualDressedEMTensorClock ActualDressedSylvester
open ActualDressedFrequencyHalf ActualDressedSignal
open ActualSourcePreparedFourClockCarrier ActualSourcePreparedStaticCorrectedReturn
open ActualSourcePreparedN3MovingResponse ActualSourcePreparedNoetherPi
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedTemporalQuantumWard
open ActualSourcePreparedTemporalQuantumIR ActualSourcePreparedQuantumColumnClock
open scoped Matrix BigOperators
attribute [local irreducible] commonJacobi commonDenominator commonNumerator
  sourceFourClockDenominator sourceFourClockResponseNumerator sourceFourClockClearing

def sourceClockEval (epsilon sigma : ℝ) : (ℂ[X])[X] →+* ℂ :=
  (Polynomial.evalRingHom (sigma : ℂ)).comp (clockSpecialize epsilon)

private theorem clock_eval_X (epsilon sigma : ℝ) :
    sourceClockEval epsilon sigma (X : (ℂ[X])[X]) = (sigma : ℂ) := by
  simp only [sourceClockEval, RingHom.comp_apply, clockSpecialize,
    Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.coe_evalRingHom, eval_X]

private theorem clock_eval_slice (epsilon sigma : ℝ) (P : Parameters) :
    sourceClockEval epsilon sigma (staticIRClockSlice P) =
      MvPolynomial.eval (irValues epsilon sigma 0) P := by
  change (clockSpecialize epsilon (staticIRClockSlice P)).eval (sigma : ℂ) = _
  rw [ir_clock_specialize, damping_slice_eval]

private theorem normalized_clear (c d n D N s response : ℂ) (nonzero : c ≠ 0)
    (den : c*d = D) (num : c*n = s*N) (clear : D*response = N) :
    d*s*response = n := by
  apply mul_left_cancel₀ nonzero
  calc
    c*(d*s*response) = s*(c*d*response) := by ring
    _ = s*N := by rw [den, clear]
    _ = c*n := num.symm

/-- This generated quotient feeds the complete original response, with its
sigma-four normalization paid before the spatial parameter is specialized. -/
theorem source_clock_reduced_pi_clear (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) (positive : 0 < sigma) (i j : Fin 289) :
    sourceClockEval epsilon sigma (sourceFourClockDenominator event n) * (sigma : ℂ)^4 *
      sourcePreparedPiEntry event (epsilon^2 • n) (sigma : ℂ) i j =
      sourceClockEval epsilon sigma (sourceFourClockResponseNumerator event n i j) := by
  have den := congrArg (sourceClockEval epsilon sigma) (source_four_clock_denominator_factor event n)
  have num := congrArg (sourceClockEval epsilon sigma) (source_four_clock_response_factor event n i j)
  simp only [map_mul, map_pow, clock_eval_X] at den num
  rw [sourceFourClockClearing, clock_eval_slice] at den
  rw [sourceFourClockNumerator, map_mul, map_pow, clock_eval_X, clock_eval_slice] at num
  have clear := congrFun (congrFun (actual_common_ir_pi_clear event n epsilon sigma 0 positive) i) j
  have static : frequencyRay epsilon 0 n 0 = 0 := by
    simp [frequencyRay, physicalFrequencyMomentum]
  have clock : dampedFourierClock (sourceFrequency epsilon 0) sigma = (sigma : ℂ) := by
    simp [dampedFourierClock, sourceFrequency]
  rw [clock] at clear
  have same := dressed_static_polarization_actual event (epsilon^2 • n)
    (frequencyRay epsilon 0 n) static (sigma : ℂ) (by simpa using positive) i j
  have prepared := source_prepared_pi_actual event (epsilon^2 • n) (sigma : ℂ)
    (by simpa using positive) i j
  change MvPolynomial.eval (irValues epsilon sigma 0) (commonDenominator event n) *
    _ = MvPolynomial.eval (irValues epsilon sigma 0) (commonNumerator event n i j) at clear
  rw [← prepared] at same
  change ActualDressedFrequencyHalf.frequencyHalfPolarization event (epsilon^2 • n)
    (frequencyRay epsilon 0 n) (sigma : ℂ) i j = _ at same
  rw [same] at clear
  exact normalized_clear _ _ _ _ _ _ _
    (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr positive.ne')) den num clear

def sourceClockReducedNumerator (event : DressedEvent) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) (ℂ[X])[X] :=
  sourceFourClockResponseNumerator event n

/-- The complete corrected pencil is generated from the same reduced clock
carrier; the surviving cubic clock multiplier is retained. -/
def sourceClockReducedPencil (event : DressedEvent) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) (ℂ[X])[X] :=
  (X^3 * sourceFourClockDenominator event n) • (commonJacobi n).map staticIRClockSlice -
    sourceClockReducedNumerator event n

private theorem reduced_entry (d s J response N : ℂ) (clear : d*s^4*response = N) :
    s^3*d*J-N = (s^3*d)*(J-s*response) := by rw [← clear]; ring

theorem source_clock_reduced_pencil_actual (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) (positive : 0 < sigma) :
    (sourceClockReducedPencil event n).map (sourceClockEval epsilon sigma) =
      ((sigma : ℂ)^3 * sourceClockEval epsilon sigma (sourceFourClockDenominator event n)) •
        sourcePreparedStaticPencil event epsilon sigma n := by
  have jacobi := common_jacobi_eval n epsilon sigma 0
  ext i j
  have J := congrFun (congrFun jacobi i) j
  change MvPolynomial.eval (irValues epsilon sigma 0) (commonJacobi n i j) = _ at J
  change sourceClockEval epsilon sigma (sourceClockReducedPencil event n i j) = _
  simp only [sourceClockReducedPencil, sourceClockReducedNumerator, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_sub, map_mul, map_pow,
    clock_eval_X, clock_eval_slice, J]
  change _ = ((sigma : ℂ)^3 * sourceClockEval epsilon sigma (sourceFourClockDenominator event n)) *
    (emOriginalJacobi (frequencyRay epsilon 0 n) i j -
      (sigma : ℂ) * sourcePreparedPiEntry event (epsilon^2 • n) (sigma : ℂ) i j)
  exact reduced_entry _ _ _ _ _ (source_clock_reduced_pi_clear event n epsilon sigma positive i j)

theorem source_clock_reduced_actual_field (event : DressedEvent) (n : PhysicalMomentum)
    (epsilon sigma : ℝ) (positive : 0 < sigma)
    (regular : correctedDet event epsilon 0 sigma n ≠ 0) :
    (sourceClockReducedPencil event n).map (sourceClockEval epsilon sigma) *ᵥ
      sourceTemporalCorrectedField event epsilon sigma n =
      ((sigma : ℂ)^3 * sourceClockEval epsilon sigma (sourceFourClockDenominator event n)) •
        sourceTemporalEMForce := by
  rw [source_clock_reduced_pencil_actual event n epsilon sigma positive, Matrix.smul_mulVec,
    source_temporal_corrected_field_equation event epsilon sigma n positive regular]

theorem source_clock_reduced_actual_driver (event : DressedEvent) (n : PhysicalMomentum)
    (e : scaleDomain) (sigma : ℝ) (positive : 0 < sigma) :
    (sourceClockReducedNumerator event n).map (sourceClockEval e.val sigma) *ᵥ
      sourceTemporalCorrectedField event e.val sigma n =
      ((sigma : ℂ)^3 * sourceClockEval e.val sigma (sourceFourClockDenominator event n)) •
        sourceTemporalActualQuantumDriver event e sigma n := by
  have matrix : (sourceClockReducedNumerator event n).map (sourceClockEval e.val sigma) =
      sourceClockEval e.val sigma (sourceFourClockDenominator event n) •
        ((sigma : ℂ)^4 • (fun i j => sourcePreparedPiEntry event (e.val^2 • n) (sigma : ℂ) i j :
          Matrix (Fin 289) (Fin 289) ℂ)) := by
    ext i j
    simpa only [sourceClockReducedNumerator, Matrix.map_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
      mul_assoc] using (source_clock_reduced_pi_clear event n e.val sigma positive i j).symm
  rw [matrix, Matrix.smul_mulVec, Matrix.smul_mulVec]
  unfold sourceTemporalActualQuantumDriver sourcePreparedClockQuantumMatrix
  rw [Matrix.smul_mulVec]
  simp only [smul_smul]
  congr 1
  ring

end LowEnergy.GaussComposite.ActualSourcePreparedClockReducedPencil
