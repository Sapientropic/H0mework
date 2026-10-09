import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Dynamics.TensorIncidence

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Incidence

open Powered.Dynamics
open scoped Matrix ComplexOrder
noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def regroupUnitary (U : Matrix.unitaryGroup ((ι × κ) × ι) ℂ) :
    Matrix.unitaryGroup ((ι × ι) × κ) ℂ :=
  ⟨(U : Matrix ((ι × κ) × ι) ((ι × κ) × ι) ℂ).submatrix bodyReservoir bodyReservoir, by
    rw [Unitary.mem_iff]
    change _ᴴ * _ = 1 ∧ _ * _ᴴ = 1
    simp only [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    simp only [← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self, Unitary.mul_star_self_of_mem U.property,
      Matrix.submatrix_one_equiv, and_self]⟩

theorem regroup_conjugation (U : Matrix.unitaryGroup ((ι × κ) × ι) ℂ)
    (rho : Matrix ((ι × κ) × ι) ((ι × κ) × ι) ℂ) :
    Quantum.conjugation (regroupUnitary U) (rho.submatrix bodyReservoir bodyReservoir) =
      (Quantum.conjugation U rho).submatrix bodyReservoir bodyReservoir := by
  simp only [Quantum.conjugation_apply, regroupUnitary, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

def localLift (U : Matrix.unitaryGroup (ι × κ) ℂ) (V : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup ((ι × ι) × κ) ℂ := regroupUnitary (Load.Quantum.localUnitary U V)

def bodyLift (U : Matrix.unitaryGroup (ι × κ) ℂ) : Matrix.unitaryGroup ((ι × ι) × κ) ℂ := localLift U 1

theorem bodyLift_received (U : Matrix.unitaryGroup (ι × κ) ℂ)
    (rho : Matrix (ι × κ) (ι × κ) ℂ) (tau : Matrix ι ι ℂ) :
    Quantum.conjugation (bodyLift U) (receivedJoint rho tau) = receivedJoint (Quantum.conjugation U rho) tau := by
  rw [bodyLift, localLift, receivedJoint, regroup_conjugation]
  change (Load.Quantum.localConjugation U 1 (Matrix.kronecker rho tau)).submatrix bodyReservoir bodyReservoir = _
  rw [Load.Quantum.localConjugation_tensor]
  have fixed : Quantum.conjugation (1 : Matrix.unitaryGroup ι ℂ) tau = tau := by
    change Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) 1 tau = tau
    simp
  rw [fixed]
  rfl

theorem localLift_unshuffle (U : Matrix.unitaryGroup (ι × κ) ℂ) (V : Matrix.unitaryGroup ι ℂ)
    (joint : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ) :
    (Quantum.conjugation (localLift U V) joint).submatrix bodyReservoir.symm bodyReservoir.symm =
      Load.Quantum.localConjugation U V (joint.submatrix bodyReservoir.symm bodyReservoir.symm) := by
  let old := joint.submatrix bodyReservoir.symm bodyReservoir.symm
  have restore : old.submatrix bodyReservoir bodyReservoir = joint := by ext i j; rfl
  have equality := regroup_conjugation (Load.Quantum.localUnitary U V) old
  rw [restore] at equality
  change Quantum.conjugation (localLift U V) joint = _ at equality
  rw [equality]
  rfl

theorem localLift_read (U : Matrix.unitaryGroup (ι × κ) ℂ) (V : Matrix.unitaryGroup ι ℂ)
    (joint : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ) :
    bodyRead (Quantum.conjugation (localLift U V) joint) = Quantum.conjugation U (bodyRead joint) := by
  rw [bodyRead, localLift_unshuffle]
  exact Load.Quantum.systemReduce_local_conjugation U V _

theorem bodyLift_read (U : Matrix.unitaryGroup (ι × κ) ℂ)
    (joint : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ) :
    bodyRead (Quantum.conjugation (bodyLift U) joint) = Quantum.conjugation U (bodyRead joint) :=
  localLift_read U 1 joint

omit [DecidableEq ι] [DecidableEq κ] in
theorem donorRead_as_reassociated (joint : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ) :
    Collision.bathReduce (systemReduce joint) =
      controllerReduce (joint.submatrix bodyReservoir.symm bodyReservoir.symm) := by
  ext r s
  change (∑ i : ι, ∑ e : κ, joint ((i, r), e) ((i, s), e)) =
    ∑ ie : ι × κ, joint ((ie.1, r), ie.2) ((ie.1, s), ie.2)
  rw [Fintype.sum_prod_type]

theorem localLift_donor (U : Matrix.unitaryGroup (ι × κ) ℂ) (V : Matrix.unitaryGroup ι ℂ)
    (joint : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ) :
    Collision.bathReduce (systemReduce (Quantum.conjugation (localLift U V) joint)) =
      Quantum.conjugation V (Collision.bathReduce (systemReduce joint)) := by
  rw [donorRead_as_reassociated, localLift_unshuffle, Load.Quantum.controllerReduce_local_conjugation,
    donorRead_as_reassociated]

theorem bodyLift_donor (U : Matrix.unitaryGroup (ι × κ) ℂ)
    (joint : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ) :
    Collision.bathReduce (systemReduce (Quantum.conjugation (bodyLift U) joint)) =
      Collision.bathReduce (systemReduce joint) := by
  rw [bodyLift, localLift_donor]
  change Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) 1 _ = _
  simp

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Incidence
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
