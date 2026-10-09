import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Good
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Payment

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Deformation
noncomputable section
open CPS1ElectronicSource
variable {frame : CPS1Recycling.Frame}

theorem current_fields (stock : Stock frame) (generated : GoodStock stock) (state : Material frame)
    (member : Species.deformed state ∈ stock) :
    Orthonormal ℂ state.currentFields ∧
      CPS1ElectronicEvolution.slaterDual state.currentFields (CPS1ElectronicEvolution.slater state.currentFields) = 1 ∧
      (normedPhysicalFock state.reference state.positions state.occupied).IsHermitian :=
  ⟨generated.2 state member,CPS1ElectronicEvolution.slater_normalized _ (generated.2 state member),
    normed_physical_fock_hermitian state.reference state.positions state.occupied⟩

theorem current_charge (stock : Stock frame) (generated : GoodStock stock) (state : Material frame)
    (member : Species.deformed state ∈ stock)
    (chart : Point → SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint) :
    (∫ x, CPS1ElectronicEvolution.Native.charge
      (CPS1ElectronicEvolution.ContinuousCharge.weights state.currentFields x) (chart x)) =
      -(electronCount frame state.reference.geometry.originJoint : ℂ) :=
  CPS1ElectronicEvolution.ContinuousCharge.generated_total _ (generated.2 state member) chart

end
end CPS1Deformation
