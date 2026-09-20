import H0mework.Physics.RadialDynamics.MatterProfile

/-! The independent source dual evolves with the phase and solves the
full-carrier adjoint kinetic jet; it is not replaced by an arbitrary bra. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics

open ProofFreeRicherAnholonomicSource DiracCliffordRepresentation DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineHolonomicField

noncomputable section

private def dualEvaluation (matter : DiracExteriorMatterCarrier) :
    (DiracSpinorIndex → Fin 2 → ℂ) →ₗ[ℂ] ℂ where
  toFun coefficients := ∑ spin, ∑ state, coefficients spin state * sourceColorDoubletDual state (matter spin)
  map_add' := by intros; simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum, mul_add, mul_assoc]

def temporalDual (rate angle : ℝ) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  spinPairDual (Complex.I*(rate : ℂ)*((spinScale : ℂ)*unitPhase angle))
    (-Complex.I*(rate : ℂ)*((spinScale : ℂ)*unitPhase (-angle)))

theorem movingDual_hasDerivAt (angle : ℝ → ℝ) (time rate : ℝ)
    (derivative : HasDerivAt angle rate time) (matter : DiracExteriorMatterCarrier) :
    HasDerivAt (fun t => movingDual (angle t) matter) (temporalDual rate (angle time) matter) time := by
  let linear := (((spinScale : ℂ) • dualEvaluation matter).restrictScalars ℝ).toContinuousLinearMap
  have generated := linear.hasFDerivAt.comp_hasDerivAt time (coefficients_hasDerivAt angle time rate derivative)
  change HasDerivAt (fun t => linear (spinPairCoefficients (unitPhase (angle t)) (unitPhase (-angle t)))) _ time at generated
  have values (t : ℝ) : linear (spinPairCoefficients (unitPhase (angle t)) (unitPhase (-angle t))) =
      movingDual (angle t) matter := by
    change (spinScale : ℂ)*dualEvaluation matter
      (spinPairCoefficients (unitPhase (angle t)) (unitPhase (-angle t))) = _
    simp [dualEvaluation, movingDual, spinPairDual, sourceColorDiracDual,
      spinPairCoefficients, Fin.sum_univ_four, Fin.sum_univ_two]
    ring
  have velocities : linear (spinPairCoefficients
      (Complex.I*(rate : ℂ)*unitPhase (angle time)) (-Complex.I*(rate : ℂ)*unitPhase (-angle time))) =
      temporalDual rate (angle time) matter := by
    change (spinScale : ℂ)*dualEvaluation matter
      (spinPairCoefficients (Complex.I*(rate : ℂ)*unitPhase (angle time))
        (-Complex.I*(rate : ℂ)*unitPhase (-angle time))) = _
    simp [dualEvaluation, temporalDual, spinPairDual, sourceColorDiracDual,
      spinPairCoefficients, Fin.sum_univ_four, Fin.sum_univ_two]
    ring
  simpa only [values, velocities] using generated

def adjointJet (amplitude rate angle : ℝ) (variation : DiracExteriorMatterCarrier) : ℂ :=
  (∑ axis : Fin 3, movingDual angle
    (Complex.I • diracMatrixMatterAction (diracGamma axis.succ)
      (diracMatrixMatterAction (diracSpinConnectionLift (homogeneousConnection spinScale) axis.succ) variation +
        diracExteriorMotherLieAction (p286LieBlockEmbed (amplitude • sourceColorP286Generator axis)) variation))) -
      (lapse : ℂ)⁻¹ * temporalDual rate angle (Complex.I • diracMatrixMatterAction (diracGamma 0) variation)

theorem adjointJet_eq (amplitude rate angle : ℝ) (variation : DiracExteriorMatterCarrier) :
    adjointJet amplitude rate angle variation =
      ((rate : ℂ)/(lapse : ℂ) - 3*((spinScale-amplitude : ℝ) : ℂ)/2) *
        spinPairDual ((spinScale : ℂ)*unitPhase (-angle)) ((spinScale : ℂ)*unitPhase angle) variation := by
  unfold adjointJet movingDual temporalDual
  simp_rw [spinPairDual_spatialKinetic, spinPairDual_temporalKinetic]
  rw [Fin.sum_univ_three]
  ring

theorem responseAdjoint_zero (parameter time : ℝ) (variation : DiracExteriorMatterCarrier) :
    adjointJet (responseProfile parameter time) (deriv (responseAngle parameter) time)
      (responseAngle parameter time) variation = 0 := by
  rw [adjointJet_eq, (responseAngle_hasDerivAt parameter time).deriv]
  have coefficient : (((3*lapse/2*(spinScale-responseProfile parameter time) : ℝ) : ℂ)/(lapse : ℂ)) -
      3*((spinScale-responseProfile parameter time : ℝ) : ℂ)/2 = 0 := by
    push_cast
    field_simp [show (lapse : ℂ) ≠ 0 by exact_mod_cast ne_of_gt lapse_pos]
    ring
  rw [coefficient, zero_mul]

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics
