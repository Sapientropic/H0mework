import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.TensorBudget

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype κ] [DecidableEq κ]

/-- Two normalized positive projections have an ancilla energy error controlled
    by their operator difference, without a factor from the tensor dimension. -/
theorem pure_projection_tensor_error
    (O : Matrix (ι × κ) (ι × κ) ℂ) (rho : Matrix ι ι ℂ)
    (P Q : Matrix κ κ ℂ)
    (hrho : rho.PosSemidef) (hrhoTrace : rho.trace = 1)
    (hP : P.PosSemidef) (hPTrace : P.trace = 1) (hP2 : P * P = P)
    (hQ : Q.PosSemidef) (hQTrace : Q.trace = 1) (hQ2 : Q * Q = Q) :
    |energy O (Matrix.kronecker rho P) -
      energy O (Matrix.kronecker rho Q)| ≤ 2 * ‖O‖ * ‖P - Q‖ := by
  let K : Matrix (ι × κ) (ι × κ) ℂ := Matrix.kronecker 1 (P-Q)
  let A : Matrix (ι × κ) (ι × κ) ℂ := Matrix.kronecker rho P
  let B : Matrix (ι × κ) (ι × κ) ℂ := Matrix.kronecker rho Q
  have projectionSplit : P-Q = P*(P-Q)+(P-Q)*Q := by
    rw [Matrix.mul_sub,Matrix.sub_mul,hP2,hQ2]
    abel
  have tensorSplit : Matrix.kronecker rho (P-Q) = A*K+K*B := by
    dsimp only [A,B,K,Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul]
    simp only [Matrix.mul_one,Matrix.one_mul,← Matrix.kronecker_add]
    exact congrArg (Matrix.kronecker rho) projectionSplit
  have massA : A.trace.re = 1 := by
    dsimp only [A,Matrix.kronecker]
    rw [Matrix.trace_kronecker,hrhoTrace,hPTrace]
    norm_num
  have massB : B.trace.re = 1 := by
    dsimp only [B,Matrix.kronecker]
    rw [Matrix.trace_kronecker,hrhoTrace,hQTrace]
    norm_num
  have boundA := energy_norm_mass (K*O) A (hrho.kronecker hP)
  have boundB := energy_norm_mass (O*K) B (hrho.kronecker hQ)
  rw [massA,mul_one] at boundA
  rw [massB,mul_one] at boundB
  have normK : ‖K‖ ≤ ‖P-Q‖ := by
    have raw := _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer.StrictThermal.kronecker_norm_le
      (1 : Matrix ι ι ℂ) (P-Q)
    have oneNorm : ‖(1 : Matrix ι ι ℂ)‖ = 1 := by
      exact CStarRing.norm_coe_unitary (1 : Matrix.unitaryGroup ι ℂ)
    rw [oneNorm,one_mul] at raw
    exact raw
  have normA : ‖K*O‖ ≤ ‖P-Q‖*‖O‖ :=
    (norm_mul_le K O).trans (mul_le_mul_of_nonneg_right normK (norm_nonneg O))
  have normB : ‖O*K‖ ≤ ‖O‖*‖P-Q‖ :=
    (norm_mul_le O K).trans (mul_le_mul_of_nonneg_left normK (norm_nonneg O))
  have cycle : energy O (A*K) = energy (K*O) A := by
    unfold energy
    rw [← Matrix.mul_assoc,Matrix.trace_mul_comm,← Matrix.mul_assoc]
  have assoc : energy O (K*B) = energy (O*K) B := by
    unfold energy
    rw [← Matrix.mul_assoc]
  rw [energy_tensor_sub_right,tensorSplit]
  have addRead : energy O (A*K+K*B) = energy (K*O) A + energy (O*K) B := by
    have split : energy O (A*K+K*B) = energy O (A*K) + energy O (K*B) := by
      simp only [energy,Matrix.mul_add,Matrix.trace_add,Complex.add_re]
    rw [split,cycle,assoc]
  rw [addRead]
  have triangle := abs_add_le (energy (K*O) A) (energy (O*K) B)
  nlinarith [triangle,boundA,boundB,normA,normB]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
