import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply.DonorConsumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.PureProjectionTensor
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.FreeFormula

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply
open Collision Propagation.Interface Propagation.Producer Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem finite_donor_idempotent : sourceFiniteDonor*sourceFiniteDonor = sourceFiniteDonor := by
  have calculated : Donor.calculatedDonor*Donor.calculatedDonor = Donor.calculatedDonor := by
    unfold Donor.calculatedDonor Spectrum.basisPure
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases htop : i = ((Donor.calculatedTop,Donor.calculatedTop),(1 : Fin 2))
      · simp [htop]
      · simp [htop]
    · simp [hij]
  have mapped := map_mul
    (Unitary.conjStarAlgAut ℂ (Matrix PairController PairController ℂ) (star installedPCFrame))
    Donor.calculatedDonor Donor.calculatedDonor
  change Quantum.conjugation (star installedPCFrame)
      (Donor.calculatedDonor*Donor.calculatedDonor) =
      sourceFiniteDonor*sourceFiniteDonor at mapped
  rw [calculated] at mapped
  exact mapped.symm

theorem original_finite_donor_energy_error_sharp (O : Current.FullJoint) :
    |energy (Prepared.donorReadout O) Source.received.joint -
      energy (finiteDonorReadout O) Source.received.joint| ≤
      (2/10^9 : ℝ)*‖O‖ := by
  have original : energy (Prepared.donorReadout O) Source.received.joint =
      energy (O.submatrix Incidence.bodyReservoir.symm Incidence.bodyReservoir.symm)
        (Matrix.kronecker Source.received.joint Source.donor) :=
    (Prepared.ancilla_readout_energy Source.donor Source.donor_positive _ Source.received.joint).symm
  rw [original,finite_donor_readout_energy]
  have paid := Input.pure_projection_tensor_error
    (O.submatrix Incidence.bodyReservoir.symm Incidence.bodyReservoir.symm)
    Source.received.joint Source.donor sourceFiniteDonor
    Source.received.positive Source.received.normalized
    Source.donor_positive Source.donor_trace Inverse.source_donor_idempotent
    finite_donor_positive finite_donor_trace finite_donor_idempotent
  have same : ‖O.submatrix Incidence.bodyReservoir.symm Incidence.bodyReservoir.symm‖ = ‖O‖ :=
    Finite.reindex_norm Incidence.bodyReservoir.symm O
  rw [same] at paid
  have scaled := mul_le_mul_of_nonneg_left original_finite_donor_error
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg O))
  nlinarith [paid,scaled,norm_nonneg O]

theorem source_finite_donor_net_cost_sharp :
    |(Resource.pcEnergyOf (bodyRead SquareRoot.Full.sourceEleven) -
        Resource.pcEnergyOf (bodyRead SquareRoot.Full.sourceNine)) -
      energy finiteLoadedNetObservable Source.received.joint| ≤
      (1/10^9 : ℝ) := by
  rw [Prepared.source_loaded_net_read]
  have bound := original_finite_donor_energy_error_sharp suppliedNetObservable
  exact bound.trans ((mul_le_mul_of_nonneg_left supplied_net_norm
    (show (0 : ℝ) ≤ 2/10^9 by norm_num)).trans (by norm_num))

theorem original_finite_donor_net_error_sharp :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint) -
        Resource.pcEnergyOf (bodyRead Weak.origin.joint)) - finiteDonorNetGain| ≤
      (79/10^7 : ℝ) := by
  have first := abs_sub_le
    (Resource.pcEnergyOf (bodyRead Weak.execution.joint) -
      Resource.pcEnergyOf (bodyRead Weak.origin.joint))
    (Resource.pcEnergyOf (bodyRead SquareRoot.Full.sourceEleven) -
      Resource.pcEnergyOf (bodyRead SquareRoot.Full.sourceNine))
    (energy finiteLoadedNetObservable Source.received.joint)
  have second := abs_sub_le
    (Resource.pcEnergyOf (bodyRead Weak.execution.joint) -
      Resource.pcEnergyOf (bodyRead Weak.origin.joint))
    (energy finiteLoadedNetObservable Source.received.joint) finiteDonorNetGain
  linarith [SquareRoot.Full.source_original_PC_gain_error,
    source_finite_donor_net_cost_sharp,finite_donor_input_net_cost]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
