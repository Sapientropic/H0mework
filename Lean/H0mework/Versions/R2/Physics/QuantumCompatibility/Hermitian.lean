import H0mework.Versions.R2.Physics.QuantumCompatibility.Current
import H0mework.Versions.R2.Physics.QuantumCompatibility.Stress
import H0mework.Versions.R2.Physics.QuantumState.StateSource

/-! Real physical responses are the expectations of self-adjoint operators.
The complete complex dual response remains available before this readout. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility

open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open Stage9C.Material.SpinPair SU7MotherLieAlgebra
open scoped Matrix ComplexOrder

noncomputable section

theorem vectorRead_eq_evaluation (point : BasePoint) (matrix : Matrix8) :
    vectorRead point matrix = State.evaluation point matrix := rfl

theorem evaluation_star (point : BasePoint) (matrix : Matrix8) :
    State.evaluation point (star matrix) = star (State.evaluation point matrix) := by
  rw [State.evaluation_eq_trace, State.evaluation_eq_trace,
    ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    (State.density_posSemidef point).isHermitian.eq, Matrix.trace_mul_comm]
  rfl

def hermitianPart (matrix : Matrix8) : Matrix8 := (1 / 2 : ℂ) • (matrix + star matrix)

theorem hermitianPart_isHermitian (matrix : Matrix8) : (hermitianPart matrix).IsHermitian := by
  change star (hermitianPart matrix) = hermitianPart matrix
  simp [hermitianPart, smul_add, add_comm]

theorem evaluation_hermitianPart (point : BasePoint) (matrix : Matrix8) :
    State.evaluation point (hermitianPart matrix) = (vectorRead point matrix).re := by
  rw [hermitianPart, map_smul, map_add, evaluation_star, vectorRead_eq_evaluation]
  change (1 / 2 : ℂ) * (State.evaluation point matrix + star (State.evaluation point matrix)) = _
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  ring

def physicalCurrent (direction : LorentzianIndex) (data : P286LieBlockData) : Matrix8 :=
  hermitianPart (currentObservable direction data)

def physicalKinetic (internal direction : LorentzianIndex) : Matrix8 :=
  hermitianPart (kineticObservable internal direction)

theorem physicalCurrent_isHermitian (direction : LorentzianIndex) (data : P286LieBlockData) :
    (physicalCurrent direction data).IsHermitian := hermitianPart_isHermitian _

theorem physicalKinetic_isHermitian (internal direction : LorentzianIndex) :
    (physicalKinetic internal direction).IsHermitian := hermitianPart_isHermitian _

theorem physicalCurrent_readout (point : BasePoint) (direction : LorentzianIndex)
    (data : P286LieBlockData) :
    State.evaluation point (physicalCurrent direction data) =
      (vectorRead point (currentObservable direction data)).re :=
  evaluation_hermitianPart point _

theorem physicalKinetic_readout (point : BasePoint) (internal direction : LorentzianIndex) :
    State.evaluation point (physicalKinetic internal direction) =
      (vectorRead point (kineticObservable internal direction)).re :=
  evaluation_hermitianPart point _

theorem physicalCurrent_prediction (point : BasePoint) (direction generator : Fin 3) :
    State.evaluation point (physicalCurrent direction.succ (sourceColorP286Generator generator)) =
      if direction = generator then 1 / 2 else 0 := by
  rw [physicalCurrent_readout, current_source_prediction]
  split_ifs <;> norm_num

end
end SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility
