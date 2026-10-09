import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply.Pulse
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply.Donor
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply.Finite

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply
open Collision Propagation.Interface Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem spectator_shared_frame {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : Matrix.unitaryGroup ι ℂ) : spectatorFrame (κ := κ) (Quantum.localUnitary U U)=
      Incidence.localLift (spectatorFrame U) U := by
  apply Subtype.ext
  ext i j
  simp only [spectatorFrame,Quantum.localUnitary,Incidence.localLift,Incidence.regroupUnitary,
    Load.Quantum.localUnitary,Incidence.bodyReservoir,Matrix.submatrix_apply,Equiv.coe_fn_mk,
    Matrix.kronecker,Matrix.kroneckerMap_apply]
  ring

theorem installed_full_frame_local : installedFullFrame=Incidence.localLift installedLoadFrame installedPCFrame :=
  spectator_shared_frame installedPCFrame

theorem basis_donor_energy {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (O : Matrix (ι × κ) (ι × κ) ℂ) (rho : Matrix ι ι ℂ) (p : κ) :
    energy O (Matrix.kronecker rho (Spectrum.basisPure p))=energy (O.submatrix (fun i => (i,p)) (fun i => (i,p))) rho := by
  have diagonal : Spectrum.basisPure p=Matrix.diagonal (fun a => ((if a=p then 1 else 0 : ℝ) : ℂ)) := by
    ext i j
    simp only [Spectrum.basisPure,Matrix.diagonal_apply]
    split_ifs <;> norm_num
  rw [diagonal,Prepared.diagonal_readout_energy]
  simp [Prepared.diagonalReadout]

def donorIndex : PairController := ((Donor.calculatedTop,Donor.calculatedTop),(1 : Fin 2))
def donorSlice (O : Current.FullJoint) : LoadedJoint :=
  O.submatrix (fun i => ((i.1,donorIndex),i.2)) (fun i => ((i.1,donorIndex),i.2))

theorem calculated_donor_basis : Donor.calculatedDonor=Spectrum.basisPure donorIndex := rfl

theorem donor_slice_grouped (O : Current.FullJoint) :
    (O.submatrix Incidence.bodyReservoir.symm Incidence.bodyReservoir.symm).submatrix
      (fun i => (i,donorIndex)) (fun i => (i,donorIndex))=donorSlice O := rfl

set_option maxRecDepth 4096 in
theorem donor_energy_in_calculated_frame (O : Current.FullJoint) (rho : LoadedJoint) :
    energy (finiteDonorReadout O) rho=energy (donorSlice (Quantum.conjugation installedFullFrame O))
      (Quantum.conjugation installedLoadFrame rho) := by
  have original := finite_donor_readout_energy O rho
  have invariant := Work.Capacity.energy_unitary_conjugation
    (O.submatrix Incidence.bodyReservoir.symm Incidence.bodyReservoir.symm) (Matrix.kronecker rho sourceFiniteDonor)
    (Load.Quantum.localUnitary installedLoadFrame installedPCFrame)
  change energy (Load.Quantum.localConjugation installedLoadFrame installedPCFrame
      (O.submatrix Incidence.bodyReservoir.symm Incidence.bodyReservoir.symm))
    (Load.Quantum.localConjugation installedLoadFrame installedPCFrame (Matrix.kronecker rho sourceFiniteDonor))=_ at invariant
  rw [Load.Quantum.localConjugation_tensor,finite_donor_calculated] at invariant
  have grouped : (Quantum.conjugation installedFullFrame O).submatrix Incidence.bodyReservoir.symm Incidence.bodyReservoir.symm=
      Load.Quantum.localConjugation installedLoadFrame installedPCFrame (O.submatrix Incidence.bodyReservoir.symm Incidence.bodyReservoir.symm) := by
    rw [installed_full_frame_local,Incidence.localLift_unshuffle]
  rw [← grouped] at invariant
  rw [calculated_donor_basis,basis_donor_energy,donor_slice_grouped] at invariant
  exact original.trans invariant.symm

theorem finite_donor_read_as_slice (O : Current.FullJoint) (rho : LoadedJoint) :
    energy (Quantum.conjugation installedLoadFrame (finiteDonorReadout O)) rho=
      energy (donorSlice (Quantum.conjugation installedFullFrame O)) rho := by
  let old := Quantum.conjugation (star installedLoadFrame) rho
  have forward : Quantum.conjugation installedLoadFrame old=rho := conjugation_undo installedLoadFrame rho
  have pair := Work.Capacity.energy_unitary_conjugation (finiteDonorReadout O) old installedLoadFrame
  change energy (Quantum.conjugation installedLoadFrame (finiteDonorReadout O)) (Quantum.conjugation installedLoadFrame old)=_ at pair
  rw [forward] at pair
  have original := donor_energy_in_calculated_frame O old
  rw [forward] at original
  exact pair.trans original

theorem finite_supply_addressed : finiteSupplyNetGain=
    energy (donorSlice (Quantum.conjugation installedFullFrame finiteSuppliedNetObservable)) Actions.finiteReceivedBody :=
  finite_donor_read_as_slice finiteSuppliedNetObservable Actions.finiteReceivedBody

theorem original_addressed_supply_net_error :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))-
      energy (donorSlice (Quantum.conjugation installedFullFrame finiteSuppliedNetObservable)) Actions.finiteReceivedBody| ≤
      (103/10^7 : ℝ) := by
  rw [← finite_supply_addressed]
  exact original_finite_supply_net_error

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
