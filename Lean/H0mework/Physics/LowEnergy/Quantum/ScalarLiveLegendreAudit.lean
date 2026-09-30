import H0mework.Physics.LowEnergy.Quantum.ScalarLiveLegendre
import H0mework.Physics.SpinPair.Actual

/-! Independent consumers at the actual source lapse and a shifted coframe.
The shifted configuration tests the general mouth; it is not a new source
occurrence. All scalar vectors remain in the original complex35 carrier. -/
set_option autoImplicit false
namespace SourceScalarLiveLegendreAudit
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource RawLorentzianMetricHodgeRecovery
open StageNineGlobalIntegratedAction StageNineDynamicBreakingVacuum
open StageNineHolonomicField StageNineEnrichedProofFreeSource
open StageNineScalarPointwiseEquation StageNineScalarActionSecondJetLocalActualLift
open StageNineP286GaugeConnectionActionVariation
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open SourceScalarLiveLegendre
open scoped BigOperators Matrix
noncomputable section

theorem source_lapse_ne_one : lapse ≠ 1 := by
  intro equal
  have square := lapse_sq
  rw [equal] at square
  norm_num at square

theorem actual_metric_inverse (p : BasePoint) :
    (lorentzianMetricOfCoframe (actual.coframe p))⁻¹ =
      Matrix.diagonal ![-(lapse ^ 2)⁻¹, 1, 1, 1] := by
  rw [actual_coframe]
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzianMetricOfCoframe, homogeneousCoframe, minkowskiInternalMetric,
      Matrix.mul_apply, Fin.sum_univ_four]
  rw [← pow_two]
  exact inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt lapse_pos))

theorem actual_h_row (p : BasePoint) (mu : LorentzianIndex) :
    h (actual.coframe p) 0 mu = if mu = 0 then -lapse⁻¹ else 0 := by
  unfold h
  rw [actual_metric_inverse, actual_coframe, homogeneousCoframe_det, abs_of_pos lapse_pos]
  fin_cases mu <;> simp
  field_simp

theorem actual_noncharacteristic (p : BasePoint) : h (actual.coframe p) 0 0 ≠ 0 := by
  rw [actual_h_row]
  simp [ne_of_gt lapse_pos]

theorem actual_momentum (p : BasePoint) (u : LorentzianIndex → Scalar) :
    momentum (actual.coframe p) u = (-lapse⁻¹) • u 0 := by
  simp [momentum, actual_h_row]

theorem source_actual_momentum (p : BasePoint) (d : Scalar) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource actual d 0 p =
      -lapse⁻¹ * pair d (holonomicScalarCovariantDerivative actual p 0) := by
  rw [original_momentum, actual_momentum]
  exact scalarCoordinatePairingRe_real_smul_right _ _ _

theorem source_actual_velocity (p : BasePoint) :
    velocity (actual.coframe p)
      (scalarActionRealDual
        (StageNineScalarActionTemporalMomentumLegendreVelocity.scalarTemporalMomentumDualAt
          positiveSmoothUnifiedSource actual p))
      (fun i => holonomicScalarCovariantDerivative actual p i.succ) =
        holonomicScalarCovariantDerivative actual p 0 :=
  original_velocity positiveSmoothUnifiedSource actual p (actual_noncharacteristic p)

theorem source_actual_Hamiltonian (p : BasePoint) :
    sourceHamiltonian positiveSmoothUnifiedSource actual p
      (momentum (actual.coframe p) (holonomicScalarCovariantDerivative actual p)) =
      pair (momentum (actual.coframe p) (holonomicScalarCovariantDerivative actual p))
        (fieldDirectionalDerivative actual.scalar p 0) -
      generatedVolumeDensity (toContinuumPointField actual p) *
        (generatedScalarKineticDensity positiveSmoothUnifiedSource 0 p (toContinuumPointField actual p) -
          generatedScalarPotential positiveSmoothUnifiedSource 0 p (actual.scalar p)) :=
  source_Hamiltonian_is_original_Legendre positiveSmoothUnifiedSource actual p (actual_noncharacteristic p)

def shiftedFrame : LorentzianCoframe :=
  !![1,1,0,0; 0,2,0,0; 0,0,1,0; 0,0,0,1]

theorem shifted_determinant : shiftedFrame.det = 2 := by
  rw [Matrix.det_succ_row_zero]
  simp [shiftedFrame, Fin.sum_univ_four, Matrix.det_fin_three]

theorem shifted_metric_inverse :
    (lorentzianMetricOfCoframe shiftedFrame)⁻¹ =
      !![-3/4,-1/4,0,0; -1/4,1/4,0,0; 0,0,1,0; 0,0,0,1] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shiftedFrame, lorentzianMetricOfCoframe, minkowskiInternalMetric,
      Matrix.mul_apply, Fin.sum_univ_four]
  all_goals norm_num

theorem shifted_h : h shiftedFrame =
    !![-3/2,-1/2,0,0; -1/2,1/2,0,0; 0,0,2,0; 0,0,0,2] := by
  unfold h
  rw [shifted_determinant, shifted_metric_inverse]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

theorem shifted_noncharacteristic : h shiftedFrame 0 0 ≠ 0 := by
  rw [shifted_h]
  norm_num

theorem shifted_momentum (u : LorentzianIndex → Scalar) :
    momentum shiftedFrame u = (-3/2 : ℝ) • u 0 + (-1/2 : ℝ) • u 1 := by
  simp [momentum, shifted_h, Fin.sum_univ_four]

theorem shifted_shift (w : Fin 3 → Scalar) :
    shiftMomentum shiftedFrame w = (-1/2 : ℝ) • w 0 := by
  simp [shiftMomentum, shifted_h, Fin.sum_univ_three]

def shiftedConfiguration (C : StageNineHolonomicConfiguration) : StageNineHolonomicConfiguration :=
  { C with coframe := fun _ => shiftedFrame }

theorem shifted_original_momentum (C : StageNineHolonomicConfiguration) (p : BasePoint) (d : Scalar) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource (shiftedConfiguration C) d 0 p =
      pair d ((-3/2 : ℝ) • holonomicScalarCovariantDerivative (shiftedConfiguration C) p 0 +
        (-1/2 : ℝ) • holonomicScalarCovariantDerivative (shiftedConfiguration C) p 1) := by
  rw [original_momentum]
  exact congrArg (pair d) (shifted_momentum _)

theorem shifted_original_velocity (C : StageNineHolonomicConfiguration) (p : BasePoint) :
    velocity shiftedFrame
      (scalarActionRealDual
        (StageNineScalarActionTemporalMomentumLegendreVelocity.scalarTemporalMomentumDualAt
          positiveSmoothUnifiedSource (shiftedConfiguration C) p))
      (fun i => holonomicScalarCovariantDerivative (shiftedConfiguration C) p i.succ) =
        holonomicScalarCovariantDerivative (shiftedConfiguration C) p 0 :=
  original_velocity positiveSmoothUnifiedSource (shiftedConfiguration C) p shifted_noncharacteristic

theorem shifted_original_Hamiltonian (C : StageNineHolonomicConfiguration) (p : BasePoint) :
    sourceHamiltonian positiveSmoothUnifiedSource (shiftedConfiguration C) p
      (momentum shiftedFrame (holonomicScalarCovariantDerivative (shiftedConfiguration C) p)) =
      pair (momentum shiftedFrame (holonomicScalarCovariantDerivative (shiftedConfiguration C) p))
        (fieldDirectionalDerivative C.scalar p 0) -
      generatedVolumeDensity (toContinuumPointField (shiftedConfiguration C) p) *
        (generatedScalarKineticDensity positiveSmoothUnifiedSource 0 p
          (toContinuumPointField (shiftedConfiguration C) p) -
         generatedScalarPotential positiveSmoothUnifiedSource 0 p (C.scalar p)) :=
  source_Hamiltonian_is_original_Legendre positiveSmoothUnifiedSource (shiftedConfiguration C) p shifted_noncharacteristic

theorem actual_shift_cancels (x : Scalar) :
    velocity shiftedFrame (momentum shiftedFrame ![0,x,0,0])
      (fun i => (![0,x,0,0] : LorentzianIndex → Scalar) i.succ) = 0 :=
  inverse_velocity shiftedFrame ![0,x,0,0] shifted_noncharacteristic

theorem omitting_shift_changes_velocity (x : Scalar) :
    (h shiftedFrame 0 0)⁻¹ • momentum shiftedFrame ![0,x,0,0] = (1/3 : ℝ) • x := by
  rw [shifted_momentum, shifted_h]
  norm_num [smul_smul]

theorem omitting_shift_is_wrong (x : Scalar) (nonzero : x ≠ 0) :
    (h shiftedFrame 0 0)⁻¹ • momentum shiftedFrame ![0,x,0,0] ≠ 0 := by
  rw [omitting_shift_changes_velocity]
  exact smul_ne_zero (by norm_num) nonzero

#print axioms SourceScalarLiveLegendre.reader_pairing
#print axioms SourceScalarLiveLegendre.original_momentum
#print axioms SourceScalarLiveLegendre.inverse_velocity
#print axioms SourceScalarLiveLegendre.original_velocity
#print axioms SourceScalarLiveLegendre.Legendre_identity
#print axioms SourceScalarLiveLegendre.kinetic_split
#print axioms SourceScalarLiveLegendre.original_kinetic
#print axioms SourceScalarLiveLegendre.source_Hamiltonian_is_original_Legendre
#print axioms source_lapse_ne_one
#print axioms actual_metric_inverse
#print axioms actual_h_row
#print axioms source_actual_momentum
#print axioms source_actual_velocity
#print axioms source_actual_Hamiltonian
#print axioms shifted_determinant
#print axioms shifted_metric_inverse
#print axioms shifted_h
#print axioms shifted_original_momentum
#print axioms shifted_original_velocity
#print axioms shifted_original_Hamiltonian
#print axioms actual_shift_cancels
#print axioms omitting_shift_changes_velocity
#print axioms omitting_shift_is_wrong

end
end SourceScalarLiveLegendreAudit
