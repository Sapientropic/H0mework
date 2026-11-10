import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedTemporalEMConstraint
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticHalfPencil

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedTemporalQuantumWard
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalFeedback PreparationVacuumOriginalGreenFeedback
open PreparationVacuumGaugeSourceInjection
open ActualEMAction ActualEMDressedSchur ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualEMDressedConstraint
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedEMEnclosure
open ActualSourcePreparedStaticCorrectedReturn ActualSourcePreparedNoetherPi
open ActualDressedConstraintWard ActualDressedNativeConstraint ActualDressedStaticResponse
open ActualDressedSylvester ActualDressedPencil ActualDressedSignal
open Filter Set MeasureTheory
open scoped Matrix BigOperators Topology Interval
attribute [local irreducible] emOriginalJacobi sourcePreparedPiEntry correctedGreen

def sourceTemporalCorrectedField (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) : Fin 289 → ℂ :=
  sourcePreparedFullGreenRead event epsilon sigma n *ᵥ sourceTemporalEMForce

private theorem source_static_time_zero (epsilon : ℝ) (n : PhysicalMomentum) :
    frequencyRay epsilon 0 n 0 = 0 := by
  change -Complex.I*((0*epsilon^2 : ℝ) : ℂ)=0
  simp only [zero_mul, Complex.ofReal_zero, mul_zero]

theorem source_temporal_corrected_field_equation (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma)
    (regular : correctedDet event epsilon 0 sigma n ≠ 0) :
    sourcePreparedStaticPencil event epsilon sigma n *ᵥ
      sourceTemporalCorrectedField event epsilon sigma n = sourceTemporalEMForce := by
  have inverse := (source_prepared_static_green_inverse event epsilon sigma n positive regular).1
  rw [←source_prepared_full_green_original event epsilon sigma n positive regular] at inverse
  unfold sourceTemporalCorrectedField
  rw [Matrix.mulVec_mulVec, inverse, Matrix.one_mulVec]

/-- The complete quantum response to the actual corrected temporal field
satisfies all nine original source rows. No zero-clock or pole-mode premise enters. -/
theorem source_temporal_quantum_cokernel (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma)
    (regular : correctedDet event epsilon 0 sigma n ≠ 0) :
    sourceCokernel (frequencyRay epsilon 0 n)
      ((fun i j => sourcePreparedPiEntry event ((epsilon^2 : ℝ) • n) (sigma : ℂ) i j :
        Matrix (Fin 289) (Fin 289) ℂ) *ᵥ
          sourceTemporalCorrectedField event epsilon sigma n) = 0 := by
  have field := source_temporal_corrected_field_equation event epsilon sigma n positive regular
  unfold sourcePreparedStaticPencil at field
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec] at field
  have rows := congrArg (sourceCokernel (frequencyRay epsilon 0 n)) field
  have original : sourceCokernel (frequencyRay epsilon 0 n)
      (emOriginalJacobi (frequencyRay epsilon 0 n)*ᵥsourceTemporalCorrectedField event epsilon sigma n)=0 := by
    rw [em_jacobi_source]
    exact (source_compatibility_nine _ _).mp (source_compatibility_euler _ _)
  rw [map_sub, map_smul, original, source_em_temporal_cokernel _ (source_static_time_zero epsilon n),
    zero_sub] at rows
  have paid := neg_eq_zero.mp rows
  exact (smul_eq_zero.mp paid).resolve_left (Complex.ofReal_ne_zero.mpr positive.ne')

private theorem prepared_pi_matrix (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) :
    (fun i j => sourcePreparedPiEntry event ((epsilon^2 : ℝ) • n) (sigma : ℂ) i j :
      Matrix (Fin 289) (Fin 289) ℂ) =
    dressedStaticPolarization event ((epsilon^2 : ℝ) • n) (sigma : ℂ) := by
  ext i j
  exact source_prepared_pi_actual event ((epsilon^2 : ℝ) • n) (sigma : ℂ) (by simpa using positive) i j

/-- The same field enters both quadratures, reference deviation and contact of
 the actual Noether history before the source window is sent to the halfline. -/
theorem source_temporal_quantum_history_return (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma)
    (regular : correctedDet event epsilon 0 sigma n ≠ 0) (row : Fin 9) :
    let p := frequencyRay epsilon 0 n
    let a := sourceTemporalCorrectedField event epsilon sigma n
    Tendsto (fun T : ℝ => ∫t in (0 : ℝ)..T, laplaceWeight (sigma : ℂ) t *
      (nativeConstraintHistory event ((epsilon^2 : ℝ) • n) p row a t-
        nativeConstraintDeviation event ((epsilon^2 : ℝ) • n) p row a t)) atTop (𝓝 0) := by
  dsimp only
  let p := frequencyRay epsilon 0 n
  let a := sourceTemporalCorrectedField event epsilon sigma n
  have window := static_polarization_window_limit event ((epsilon^2 : ℝ) • n) p
    (source_static_time_zero epsilon n) (sigma : ℂ) (by simpa using positive)
  have continuity : Continuous (fun M : Matrix (Fin 289) (Fin 289) ℂ => sourceCokernel p (M*ᵥa) row) := by
    exact (continuous_apply row).comp ((sourceCokernel p).toContinuousLinearMap.continuous.comp
      (by unfold Matrix.mulVec dotProduct; fun_prop))
  have limit := (continuity.tendsto _).comp window
  have zero := source_temporal_quantum_cokernel event epsilon sigma n positive regular
  rw [prepared_pi_matrix event epsilon sigma n positive] at zero
  have coordinate := congrFun zero row
  rw [coordinate] at limit
  simpa only [Function.comp_def, source_constraint_native_history, Pi.zero_apply] using limit

end LowEnergy.GaussComposite.ActualSourcePreparedTemporalQuantumWard
