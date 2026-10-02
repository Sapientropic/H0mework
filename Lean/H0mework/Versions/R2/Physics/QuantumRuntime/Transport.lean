import H0mework.Versions.R2.Physics.QuantumRuntime.NativeField
import H0mework.Versions.R2.Physics.QuantumState.StateCovariance
import H0mework.Versions.R2.Physics.QuantumDynamics.Automorphism

/-! The following native material occurrence consumes the current occupied
field. Physical displacement uses its exact closed action; the controller's
visit index remains a distinct coordinate. The whole density is retained. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.Runtime

open Matrix ProofFreeRicherAnholonomicSource StageNineHolonomicField
open Stage9DEF.State Stage9DEF.Dynamics
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
  LAlanine40K2025.Thermal.Preparation

noncomputable section

def densityAt (index : ℕ) (point : BasePoint) : Observable :=
  normalizedGram (column (fieldAt index point) (0, 0))

theorem densityAt_eq (index : ℕ) (point : BasePoint) : densityAt index point = density point := by
  rw [densityAt, fieldAt_eq_vector]
  rfl

theorem next_field_from_current (index : ℕ) (point displacement : BasePoint) :
    fieldAt (index + 1) (point + displacement) =
      (unitary displacement : Observable) *ᵥ fieldAt index point := by
  rw [fieldAt_eq_vector, fieldAt_eq_vector, unitary_mul_vector]

theorem next_density_from_current (index : ℕ) (point displacement : BasePoint) :
    densityAt (index + 1) (point + displacement) =
      automorphism displacement (densityAt index point) := by
  rw [densityAt_eq, densityAt_eq, density_eq_pureMatrix, density_eq_pureMatrix,
    ← unitary_mul_vector, pureMatrix_mulVec]
  rfl

theorem activated_next_reads_current (point displacement : BasePoint) :
    secondQuantumTick.answer (point + displacement) =
      (unitary displacement : Observable) *ᵥ firstQuantumTick.answer point := by
  rw [secondQuantumTick_answer, firstQuantumTick_answer]
  exact next_field_from_current 3 point displacement

theorem activated_weight_positive (point displacement : BasePoint) (effect : Effect) :
    0 ≤ (vectorEvaluation (secondQuantumTick.answer (point + displacement)) effect.matrix).re := by
  rw [secondQuantumTick_answer, fieldAt_eq_vector]
  exact effectWeight_nonnegative _ effect

theorem activated_weight_normalized (point displacement : BasePoint) (effect : Effect) :
    (vectorEvaluation (secondQuantumTick.answer (point + displacement)) effect.matrix).re +
      (vectorEvaluation (secondQuantumTick.answer (point + displacement))
        effect.complement.matrix).re = 1 := by
  rw [secondQuantumTick_answer, fieldAt_eq_vector]
  exact effectWeight_binary_normalized _ effect

theorem next_density_two_step (index : ℕ) (point first second : BasePoint) :
    densityAt (index + 2) (point + first + second) =
      automorphism second (automorphism first (densityAt index point)) := by
  rw [show index + 2 = (index + 1) + 1 from rfl, next_density_from_current,
    next_density_from_current]

end
end SaturationMonoid.PhysicsCore.Stage9DEF.Runtime
