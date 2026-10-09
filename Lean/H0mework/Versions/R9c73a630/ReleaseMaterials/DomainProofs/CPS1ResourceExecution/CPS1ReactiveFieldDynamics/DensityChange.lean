import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.Response

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

namespace CPS1ReactiveFieldDynamics
noncomputable section
open scoped BigOperators Matrix

def sourceCommutator (state : Snapshot) : Matrix (BasisIndex state) (BasisIndex state) ℂ :=
  fullFock state * sourceDensity state - sourceDensity state * fullFock state

set_option backward.isDefEq.respectTransparency.types false in
/-- The literal Cayley response has an exact full-time density difference. -/
theorem response_density_conjugated_difference (state : Snapshot) (time : ℝ) :
    CPS1ElectronicEvolution.denominator (fullFock state) (time / 2) *
      (responseDensity state time - sourceDensity state) *
      (CPS1ElectronicEvolution.denominator (fullFock state) (time / 2)).conjTranspose =
      (-Complex.I * (time : ℂ)) • sourceCommutator state := by
  let generator := CPS1ElectronicEvolution.generator (fullFock state) (time / 2)
  let denominator := CPS1ElectronicEvolution.denominator (fullFock state) (time / 2)
  have denominatorAdjoint : denominator.conjTranspose = 1 - generator := by
    simp only [denominator, CPS1ElectronicEvolution.denominator, Matrix.conjTranspose_add,
      Matrix.conjTranspose_one, CPS1ElectronicEvolution.generator_skew _ (full_fock_hermitian state),
      generator, sub_eq_add_neg]
  have numeratorAdjoint : (1 - generator).conjTranspose = denominator := by
    simp only [generator, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      CPS1ElectronicEvolution.generator_skew _ (full_fock_hermitian state), sub_neg_eq_add]
    rfl
  have equation : denominator * responseCoordinates state time =
      (1 - generator) * coordinates state := response_equation state time
  have evolved : denominator * responseDensity state time * denominator.conjTranspose =
      (1 - generator) * sourceDensity state * denominator := by
    calc
      _ = (denominator * responseCoordinates state time) *
          (denominator * responseCoordinates state time).conjTranspose := by
        simp only [responseDensity, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ((1 - generator) * coordinates state) *
          ((1 - generator) * coordinates state).conjTranspose := by
        exact congrArg (fun matrix : Matrix (BasisIndex state) state.ElectronIndex ℂ =>
          matrix * matrix.conjTranspose) equation
      _ = _ := by
        rw [Matrix.conjTranspose_mul, numeratorAdjoint]
        have product : (1 - generator) * coordinates state * ((coordinates state).conjTranspose * denominator) =
            (1 - generator) * (coordinates state * (coordinates state).conjTranspose) * denominator := by
          simp only [Matrix.mul_assoc]
        simpa only [sourceDensity] using! product
  change denominator * (responseDensity state time - sourceDensity state) * denominator.conjTranspose = _
  calc
    _ = denominator * responseDensity state time * denominator.conjTranspose -
        denominator * sourceDensity state * denominator.conjTranspose := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
    _ = (1 - generator) * sourceDensity state * (1 + generator) -
        (1 + generator) * sourceDensity state * (1 - generator) := by
      rw [evolved, denominatorAdjoint]
      rfl
    _ = (sourceDensity state * generator - generator * sourceDensity state) +
        (sourceDensity state * generator - generator * sourceDensity state) := by
      noncomm_ring
    _ = _ := by
      simp only [generator, CPS1ElectronicEvolution.generator,
        Matrix.mul_smul, Matrix.smul_mul]
      ext first second
      simp only [sourceCommutator, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
        smul_eq_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
      ring

theorem response_density_ne_of_commutator (state : Snapshot) (time : ℝ)
    (timeNonzero : time ≠ 0) (commutatorNonzero : sourceCommutator state ≠ 0) :
    responseDensity state time ≠ sourceDensity state := by
  intro unchanged
  have equation := response_density_conjugated_difference state time
  rw [unchanged, sub_self, Matrix.mul_zero, Matrix.zero_mul] at equation
  have scalarNonzero : -Complex.I * (time : ℂ) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr timeNonzero)
  exact commutatorNonzero ((smul_eq_zero.mp equation.symm).resolve_left scalarNonzero)

set_option backward.isDefEq.respectTransparency.types false in
/-- The same source commutator also generates the full-time stationary branch. -/
theorem response_density_eq_of_commutator_zero (state : Snapshot) (time : ℝ)
    (commutatorZero : sourceCommutator state = 0) :
    responseDensity state time = sourceDensity state := by
  have denominatorUnit := CPS1ElectronicEvolution.denominator_unit
    (fullFock state) (full_fock_hermitian state) (time / 2)
  apply sub_eq_zero.mp
  apply denominatorUnit.mul_left_cancel
  apply denominatorUnit.star.mul_right_cancel
  simpa only [commutatorZero, smul_zero, Matrix.mul_zero, Matrix.zero_mul] using!
    response_density_conjugated_difference state time

end
end CPS1ReactiveFieldDynamics
