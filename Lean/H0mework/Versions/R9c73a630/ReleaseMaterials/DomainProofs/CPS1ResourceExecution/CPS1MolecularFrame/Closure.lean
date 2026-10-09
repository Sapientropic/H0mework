import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Good
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Evolution

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1MolecularFrame
noncomputable section
open CPS1ElectronicSource
variable {frame : CPS1Recycling.Frame}

theorem current_fields (stock : Stock frame) (generated : GoodStock stock) (state : Material frame)
    (member : Species.molecular state ∈ stock) :
    Orthonormal ℂ state.currentFields ∧
      CPS1ElectronicEvolution.slaterDual state.currentFields
        (CPS1ElectronicEvolution.slater state.currentFields) = 1 ∧ state.hamiltonian.IsHermitian :=
  ⟨material_fields state (generated.2 state member),material_slater state (generated.2 state member),
    material_hamiltonian_hermitian state⟩

theorem current_charge (stock : Stock frame) (generated : GoodStock stock) (state : Material frame)
    (member : Species.molecular state ∈ stock)
    (chart : Point → SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint) :
    (∫ x, CPS1ElectronicEvolution.Native.charge
      (CPS1ElectronicEvolution.ContinuousCharge.weights state.currentFields x) (chart x)) =
      -(electronCount frame state.reference.geometry.originJoint : ℂ) :=
  material_charge state (generated.2 state member) chart

end
end CPS1MolecularFrame
