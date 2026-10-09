import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Good
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Translation

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Following
noncomputable section
open CPS1ElectronicSource
variable {frame : CPS1Recycling.Frame}

def currentCentre (state : CPS1ElectronicSource.State frame) : Point := fun axis => centre state axis

def currentFields (state : CPS1ElectronicSource.State frame) : ElectronIndex state.geometry → SpinSpace :=
  fun slot => translate (currentCentre state) (CPS1ElectronicEvolution.Consumer.occupiedFields state slot)

def rowVelocity (state : CPS1ElectronicSource.State frame) : Point :=
  fun axis => ((massTotal state)⁻¹ • (state.geometry.nuclei.map (fun node => node.row.momentum)).sum) axis

def currentAction (state : CPS1ElectronicSource.State frame) : SpinSpace →L[ℂ] SpinSpace :=
  movingAction (relativeState state) (currentCentre state) (rowVelocity state)

theorem current_fields (stock : Stock frame) (generated : GoodStock stock)
    (state : CPS1ElectronicSource.State frame) (member : Species.following state ∈ stock) :
    Orthonormal ℂ (currentFields state) ∧
      CPS1ElectronicEvolution.slaterDual (currentFields state)
        (CPS1ElectronicEvolution.slater (currentFields state)) = 1 ∧
      (followingHamiltonian (relativeState state) (rowVelocity state)).IsHermitian := by
  have good := generated.2 state member
  have orthogonal : Orthonormal ℂ (currentFields state) :=
    translate_orthonormal (currentCentre state) _ (CPS1ElectronicEvolution.Consumer.source_fields state good)
  exact ⟨orthogonal,CPS1ElectronicEvolution.slater_normalized _ orthogonal,
    following_hamiltonian_hermitian (relativeState state) (rowVelocity state)⟩

theorem current_charge (stock : Stock frame) (generated : GoodStock stock)
    (state : CPS1ElectronicSource.State frame) (member : Species.following state ∈ stock)
    (chart : Point → SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint) :
    (∫ x, CPS1ElectronicEvolution.Native.charge
      (CPS1ElectronicEvolution.ContinuousCharge.weights (currentFields state) x) (chart x)) =
      -(electronCount frame state.geometry.originJoint : ℂ) :=
  CPS1ElectronicEvolution.ContinuousCharge.generated_total _ (current_fields stock generated state member).1 chart

end
end CPS1Following
