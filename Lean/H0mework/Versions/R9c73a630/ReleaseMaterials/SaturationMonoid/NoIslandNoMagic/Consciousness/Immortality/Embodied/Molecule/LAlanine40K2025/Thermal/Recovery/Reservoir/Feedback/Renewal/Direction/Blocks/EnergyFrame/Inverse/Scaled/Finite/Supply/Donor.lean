import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions.BodyConsumer

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply
open Collision Propagation.Interface Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem conjugation_undo {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    Quantum.conjugation U (Quantum.conjugation (star U) A)=A := by
  rw [Environment.conjugation_comp]
  simp only [Unitary.mul_star_self,Quantum.conjugation_apply,Submonoid.coe_one,star_one,Matrix.one_mul,Matrix.mul_one]

def sourceFiniteDonor : Matrix PairController PairController ℂ :=
  Quantum.conjugation (star installedPCFrame) Donor.calculatedDonor

theorem finite_donor_positive : sourceFiniteDonor.PosSemidef :=
  Quantum.conjugation_posSemidef (star installedPCFrame) Donor.calculatedDonor (Spectrum.basisPure_positive _)

theorem finite_donor_trace : sourceFiniteDonor.trace=1 :=
  (Quantum.conjugation_trace _ _).trans (Spectrum.basisPure_trace _)

theorem finite_donor_calculated : Quantum.conjugation installedPCFrame sourceFiniteDonor=Donor.calculatedDonor :=
  conjugation_undo installedPCFrame Donor.calculatedDonor

theorem original_finite_donor_error : ‖Source.donor-sourceFiniteDonor‖ ≤ (1/10^9 : ℝ) := by
  have same := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ (Matrix PairController PairController ℂ) installedPCFrame)
    (Source.donor-sourceFiniteDonor)
  change ‖Quantum.conjugation installedPCFrame (Source.donor-sourceFiniteDonor)‖=_ at same
  rw [map_sub,finite_donor_calculated] at same
  rw [← same]
  exact Donor.actual_donor_error

def finiteDonorReadout (O : Current.FullJoint) : LoadedJoint :=
  Prepared.ancillaReadout sourceFiniteDonor finite_donor_positive
    (O.submatrix Incidence.bodyReservoir.symm Incidence.bodyReservoir.symm)

theorem finite_donor_readout_norm (O : Current.FullJoint) (hermitian : O.IsHermitian) :
    ‖finiteDonorReadout O‖ ≤ ‖O‖ := by
  apply (Prepared.ancilla_readout_norm sourceFiniteDonor finite_donor_positive finite_donor_trace _
    (hermitian.submatrix Incidence.bodyReservoir.symm)).trans
  exact (Finite.reindex_norm Incidence.bodyReservoir.symm O).le

theorem finite_donor_readout_hermitian (O : Current.FullJoint) (hermitian : O.IsHermitian) :
    (finiteDonorReadout O).IsHermitian :=
  Prepared.ancilla_readout_hermitian sourceFiniteDonor finite_donor_positive _ (hermitian.submatrix Incidence.bodyReservoir.symm)

theorem finite_donor_readout_energy (O : Current.FullJoint) (rho : LoadedJoint) :
    energy (finiteDonorReadout O) rho=
      energy (O.submatrix Incidence.bodyReservoir.symm Incidence.bodyReservoir.symm) (Matrix.kronecker rho sourceFiniteDonor) :=
  (Prepared.ancilla_readout_energy sourceFiniteDonor finite_donor_positive _ rho).symm

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
