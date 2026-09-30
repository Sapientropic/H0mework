import H0mework.Versions.X.NavierStokes.SourceAction.ScalarGain
import H0mework.Versions.X.NavierStokes.SourceAction.EndpointEnergy

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeEndpointPositiveTime

open Set MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalTimeConsumer
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open NativeFullOrderEnergy NativeFullOrderAction NativeFullOrderEvolution NativePositiveTimeMoments
open NativeFullOrderRecovery NativeScalarPositiveTime

noncomputable section

variable {nu : Viscosity}

def endpointBudget (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (activityBudget : ℝ) (order : ℕ) (delta : ℝ) : ℝ :=
  positiveBudget nu.coeff (‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2) activityBudget
    (fun rank => wordRate rank nu) order delta

def endpointWindow (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) (left right : ℝ) (leftNonnegative : 0 ≤ left) (ordered : left ≤ right) (rightLe : right ≤ 1)
    (activityBudget : ℝ)
    (activityPaid : (∫ time in left..right, finiteStateVelocityMajorant (wholeRestartModes radius)
      ((ledger.family.stage radius).trajectory time) ^ 2) ≤ activityBudget)
    (ceiling : ℝ) (ceilingNonnegative : 0 ≤ ceiling) :
    DissipativeWindow left right nu.coeff (‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2) activityBudget := by
  let stage := ledger.family.stage radius
  let energy (order : ℕ) (time : ℝ) :=
    weightedVelocityEnergy (wholeRestartModes radius) (wordWeight order ceiling) (stage.trajectory time)
  let dissipation (order : ℕ) (time : ℝ) :=
    weightedVelocityDissipation (wholeRestartModes radius) (wordWeight order ceiling) (stage.trajectory time)
  let activity (time : ℝ) := finiteStateVelocityMajorant (wholeRestartModes radius) (stage.trajectory time) ^ 2
  have subset : Icc left right ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc leftNonnegative rightLe
  have pathContinuous : ContinuousOn stage.trajectory (Icc left right) :=
    HasDerivAt.continuousOn (fun time inside => (stage.physical time (subset inside)).1)
  refine {
    energy := energy
    dissipation := dissipation
    activity := activity
    rate := fun order => wordRate order nu
    ordered := ordered
    viscosity_pos := nu.coeff_pos
    kinetic_nonneg := sq_nonneg _
    activityBudget_nonneg := (intervalIntegral.integral_nonneg ordered
      (fun _ _ => sq_nonneg _)).trans activityPaid
    rate_nonneg := fun order => wordRate_nonneg order nu
    energy_nonneg := ?_
    dissipation_nonneg := ?_
    activity_nonneg := fun _ => sq_nonneg _
    energy_continuous := ?_
    dissipation_continuous := ?_
    activity_continuous := ?_
    derivative_continuous := ?_
    differentiable := fun order time inside =>
      (endpoint_energy_action_hasDerivAt stage (wordWeight order ceiling) time (subset inside)).differentiableAt
    action := fun order time inside => endpoint_energy_retained_dissipation stage order ceiling
      ceilingNonnegative time (subset inside)
    gain := fun order time => energy_succ_le_dissipation radius order ceiling ceilingNonnegative (stage.trajectory time)
    initial_bound := ?_
    activity_paid := activityPaid }
  · intro order time
    dsimp only [energy]
    rw [← weightedVelocityRead_norm_sq]
    exact sq_nonneg _
  · intro order time
    unfold dissipation weightedVelocityDissipation
    apply Finset.sum_nonneg
    intro wave _
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (by
      unfold integerWaveViscousMultiplier
      exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg _))) (complexCoordinateVectorNormSq_nonneg _)
  · intro order
    have actual := ((weightedVelocityRead (wholeRestartModes radius) (wordWeight order ceiling)).continuous.comp_continuousOn
      pathContinuous).norm.pow 2
    exact actual.congr (fun time _ => (weightedVelocityRead_norm_sq (wholeRestartModes radius)
      (wordWeight order ceiling) (stage.trajectory time)).symm)
  · intro order
    unfold dissipation weightedVelocityDissipation complexCoordinateVectorNormSq
    apply continuousOn_finsetSum
    intro wave _
    apply ContinuousOn.const_mul
    apply continuousOn_finsetSum
    intro coordinate _
    have velocity := (velocityRead wave).continuous.comp_continuousOn pathContinuous
    exact Complex.continuous_normSq.comp_continuousOn ((continuous_apply coordinate).comp_continuousOn velocity)
  · intro time inside
    exact ((finiteStateVelocityMajorant_continuousAt_of_hasDerivAt (wholeRestartModes radius)
      stage.trajectory time _ (stage.physical time (subset inside)).1).pow 2).continuousWithinAt
  · intro order
    let read := weightedVelocityRead (wholeRestartModes radius) (wordWeight order ceiling)
    have generated := (finiteStateVorticityGenerator_contDiff (wholeRestartModes radius) nu.coeff).continuous.comp_continuousOn
      pathContinuous
    have continuity : ContinuousOn (fun time => (2 : ℝ) *
        inner ℝ (read (finiteStateVorticityGenerator (wholeRestartModes radius) nu.coeff (stage.trajectory time)))
          (read (stage.trajectory time))) (Icc left right) :=
      ((read.continuous.comp_continuousOn generated).inner
        (read.continuous.comp_continuousOn pathContinuous)).const_mul 2
    apply continuity.congr
    intro time inside
    dsimp only [read]
    rw [real_inner_comm, weightedVelocityRead_inner]
    exact (endpoint_energy_hasDerivAt stage (wordWeight order ceiling) time (subset inside)).deriv
  · intro time inside
    have paid := mul_le_mul_of_nonneg_left (ledger.kinetic_energy_le radius ⟨time, subset inside⟩) (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [energy, weightedVelocityEnergy, wordWeight, pow_zero, one_pow, one_mul,
      finiteStateVorticityKineticEnergy, ← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num] using paid

theorem endpoint_positive_time_energy_bound
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) (left right : ℝ) (leftNonnegative : 0 ≤ left) (ordered : left ≤ right) (rightLe : right ≤ 1)
    (activityBudget : ℝ)
    (activityPaid : (∫ time in left..right, finiteStateVelocityMajorant (wholeRestartModes radius)
      ((ledger.family.stage radius).trajectory time) ^ 2) ≤ activityBudget)
    (order : ℕ) (delta : ℝ) (positive : 0 < delta) (fits : left + delta ≤ right)
    (ceiling : ℝ) (ceilingNonnegative : 0 ≤ ceiling) (time : ℝ) (inside : time ∈ Icc (left + delta) right) :
    weightedVelocityEnergy (wholeRestartModes radius) (wordWeight order ceiling)
      ((ledger.family.stage radius).trajectory time) ≤ endpointBudget ledger activityBudget order delta :=
  energy_bound (endpointWindow ledger radius left right leftNonnegative ordered rightLe activityBudget activityPaid
    ceiling ceilingNonnegative) order delta positive fits time inside

end
end SaturationMonoid.NavierStokes.NativeEndpointPositiveTime
