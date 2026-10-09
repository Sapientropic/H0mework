import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply.Coordinates

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
open Collision Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def localMatrix {ι κ : Type*} (A : Matrix (ι × κ) (ι × κ) ℂ) (B : Matrix ι ι ℂ) :
    Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ :=
  (Matrix.kronecker A B).submatrix Incidence.bodyReservoir Incidence.bodyReservoir

theorem local_lift_matrix_covariance {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (W U : Matrix.unitaryGroup (ι × κ) ℂ) (Z V : Matrix.unitaryGroup ι ℂ) :
    Quantum.conjugation (Incidence.localLift W Z) (Incidence.localLift U V : Matrix ((ι × ι) × κ) ((ι × ι) × κ) ℂ)=
      localMatrix (Quantum.conjugation W (U : Matrix (ι × κ) (ι × κ) ℂ)) (Quantum.conjugation Z (V : Matrix ι ι ℂ)) := by
  change Quantum.conjugation (Incidence.regroupUnitary (Load.Quantum.localUnitary W Z))
    ((Matrix.kronecker (U : Matrix (ι × κ) (ι × κ) ℂ) (V : Matrix ι ι ℂ)).submatrix Incidence.bodyReservoir Incidence.bodyReservoir)=_
  rw [Incidence.regroup_conjugation]
  change (Load.Quantum.localConjugation W Z (Matrix.kronecker (U : Matrix (ι × κ) (ι × κ) ℂ) (V : Matrix ι ι ℂ))).submatrix
    Incidence.bodyReservoir Incidence.bodyReservoir=_
  rw [Load.Quantum.localConjugation_tensor]
  rfl

theorem local_matrix_sub {ι κ : Type*} (A C : Matrix (ι × κ) (ι × κ) ℂ) (B D : Matrix ι ι ℂ) :
    localMatrix A B-localMatrix C D=(Matrix.kronecker A B-Matrix.kronecker C D).submatrix
      Incidence.bodyReservoir Incidence.bodyReservoir := rfl

theorem local_matrix_error {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [Nonempty ι] [Nonempty κ] (U : Matrix.unitaryGroup (ι × κ) ℂ) (V : Matrix.unitaryGroup ι ℂ)
    (A : Matrix (ι × κ) (ι × κ) ℂ) (B : Matrix ι ι ℂ) (d e : ℝ)
    (ha : ‖(U : Matrix (ι × κ) (ι × κ) ℂ)-A‖ ≤ d) (hb : ‖(V : Matrix ι ι ℂ)-B‖ ≤ e) :
    ‖localMatrix (U : Matrix (ι × κ) (ι × κ) ℂ) (V : Matrix ι ι ℂ)-localMatrix A B‖ ≤ d+(1+d)*e := by
  rw [local_matrix_sub,Finite.reindex_norm]
  exact Actions.approximated_tensor_error U V A B d e ha hb

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
