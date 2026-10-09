import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply.Donor

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply
open Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem ancilla_readout_sub {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (D : Matrix κ κ ℂ) (positive : D.PosSemidef) (A B : Matrix (ι × κ) (ι × κ) ℂ) :
    Prepared.ancillaReadout D positive (A-B)=Prepared.ancillaReadout D positive A-Prepared.ancillaReadout D positive B := by
  simp only [Prepared.ancillaReadout,Prepared.diagonalReadout,map_sub,Matrix.submatrix_sub,Pi.sub_apply,smul_sub,Finset.sum_sub_distrib]

theorem finite_donor_readout_sub (A B : Current.FullJoint) :
    finiteDonorReadout (A-B)=finiteDonorReadout A-finiteDonorReadout B := by
  unfold finiteDonorReadout
  rw [Matrix.submatrix_sub]
  exact ancilla_readout_sub _ _ _ _

theorem finite_donor_readout_difference (A B : Current.FullJoint) (ha : A.IsHermitian) (hb : B.IsHermitian) :
    ‖finiteDonorReadout A-finiteDonorReadout B‖ ≤ ‖A-B‖ := by
  rw [← finite_donor_readout_sub]
  exact finite_donor_readout_norm _ (ha.sub hb)

theorem raw_pullback_hermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V O : Matrix ι ι ℂ) (hermitian : O.IsHermitian) : (star V*O*V).IsHermitian := by
  have h := Matrix.isHermitian_mul_mul_conjTranspose (star V) hermitian
  simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_conjTranspose] using h

theorem raw_pullback_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (V O : Matrix ι ι ℂ) :
    ‖Quantum.conjugation (star U) O-star V*O*V‖ ≤ (1+‖V‖)*‖O‖*‖(U : Matrix ι ι ℂ)-V‖ := by
  have paid := Input.raw_conjugation_error (star U) (star V) O
  simpa only [star_star,norm_star,Unitary.coe_star,← star_sub] using paid

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
