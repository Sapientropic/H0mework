import H0mework.Physics.QuantumDynamics.Phase
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Physical-time differentiation and a source-calculated local remainder.
The finite evolution remains the exact unitary; its affine expression is a
first jet with the displayed quadratic error and effective range. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.Dynamics

open DiracCliffordRepresentation ProofFreeRicherAnholonomicSource
open StageNineHolonomicField Stage9C.Material.SpinPair Source

noncomputable section

def timeDisplacement (time : ℝ) : BasePoint :=
  time • coordinateDirection 0

@[simp] theorem timeDisplacement_zero (time : ℝ) :
    timeDisplacement time 0 = time := by
  simp [timeDisplacement, coordinateDirection]

def generator (index : Index) : ℂ := (rate index : ℂ) * Complex.I

theorem phaseCoefficient_hasDerivAt (time : ℝ) (index : Index) :
    HasDerivAt (fun t : ℝ => phaseCoefficient (timeDisplacement t) index)
      (phaseCoefficient (timeDisplacement time) index * generator index) time := by
  simpa [phaseCoefficient, phase, generator] using
    (Complex.ofRealCLM.hasDerivAt.mul_const ((rate index : ℂ) * Complex.I)).cexp

theorem vector_time_hasDerivAt (point : BasePoint) (time : ℝ) :
    HasDerivAt (fun t : ℝ => vector (point + timeDisplacement t))
      (fun index => vector (point + timeDisplacement time) index * generator index) time := by
  rw [hasDerivAt_pi]
  intro index
  have factorization :
      (fun t : ℝ => vector (point + timeDisplacement t) index) =
        (fun t : ℝ => phaseCoefficient (timeDisplacement t) index * vector point index) := by
    funext t
    exact (phaseCoefficient_mul_vector point (timeDisplacement t) index).symm
  rw [factorization]
  have coefficient_eq :
      (phaseCoefficient (timeDisplacement time) index * generator index) * vector point index =
        vector (point + timeDisplacement time) index * generator index := by
    rw [← phaseCoefficient_mul_vector]
    ring
  exact coefficient_eq ▸
    (phaseCoefficient_hasDerivAt time index).mul_const (vector point index)

theorem rate_norm (index : Index) : ‖rate index‖ = ‖frequency‖ := by
  unfold rate
  split <;> simp

def phaseResidual (displacement : BasePoint) (index : Index) : ℂ :=
  phaseCoefficient displacement index - 1 - (displacement 0 : ℂ) * generator index

theorem phaseCoefficient_eq_firstJet_add_residual (displacement : BasePoint) (index : Index) :
    phaseCoefficient displacement index =
      1 + (displacement 0 : ℂ) * generator index + phaseResidual displacement index := by
  unfold phaseResidual
  ring

theorem phaseResidual_bound (displacement : BasePoint) (index : Index)
    (effective : ‖displacement 0‖ * ‖frequency‖ ≤ 1) :
    ‖phaseResidual displacement index‖ ≤ (‖displacement 0‖ * ‖frequency‖) ^ 2 := by
  have exponent_norm : ‖(displacement 0 : ℂ) * generator index‖ =
      ‖displacement 0‖ * ‖frequency‖ := by
    simp only [generator, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, rate_norm]
  unfold phaseResidual phaseCoefficient phase
  change ‖Complex.exp ((displacement 0 : ℂ) * generator index) - 1 -
    (displacement 0 : ℂ) * generator index‖ ≤ _
  calc
    _ ≤ ‖(displacement 0 : ℂ) * generator index‖ ^ 2 :=
      Complex.norm_exp_sub_one_sub_id_le (exponent_norm ▸ effective)
    _ = _ := congrArg (fun r : ℝ => r ^ 2) exponent_norm

def vectorResidual (point displacement : BasePoint) (index : Index) : ℂ :=
  phaseResidual displacement index * vector point index

theorem vector_eq_firstJet_add_residual (point displacement : BasePoint) (index : Index) :
    vector (point + displacement) index = vector point index +
      (displacement 0 : ℂ) * (generator index * vector point index) +
        vectorResidual point displacement index := by
  rw [← phaseCoefficient_mul_vector, phaseCoefficient_eq_firstJet_add_residual]
  unfold vectorResidual
  ring

theorem vectorResidual_bound (point displacement : BasePoint) (index : Index)
    (effective : ‖displacement 0‖ * ‖frequency‖ ≤ 1) :
    ‖vectorResidual point displacement index‖ ≤
      (‖displacement 0‖ * ‖frequency‖) ^ 2 * ‖vector point index‖ := by
  rw [vectorResidual, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (phaseResidual_bound displacement index effective) (norm_nonneg _)

end
end SaturationMonoid.PhysicsCore.Stage9DEF.Dynamics
