import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.State
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Evolution.Source

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CPS1ElectronicEvolution.Consumer
noncomputable section
open CPS1ElectronicSource
open scoped Matrix InnerProductSpace
variable {frame : CPS1Recycling.Frame}

def occupiedFields (state : State frame) : ElectronIndex state.geometry → SpinSpace :=
  fields (basis state.geometry) state.occupied

def Good (state : State frame) : Prop := state.occupied.conjTranspose * state.occupied = 1

theorem source_capture (geometry : Geometry frame) (state : State frame)
    (actual : State.fromGeometry? geometry = .ok state) : Good state := by
  unfold State.fromGeometry? at actual
  split at actual <;> try contradiction
  split at actual <;> try contradiction
  cases Except.ok.inj actual
  exact Source.source_occupation geometry

theorem actual_pulse (state next : State frame) (time : ℝ)
    (actual : State.pulse? state time = .ok next) (generated : Good state) : Good next := by
  unfold State.pulse? at actual
  split at actual <;> try contradiction
  split at actual <;> try contradiction
  dsimp only at actual
  split at actual <;> try contradiction
  cases Except.ok.inj actual
  exact (occupied_gram state.hamiltonian (source_hamiltonian_hermitian state) (time/2) state.occupied).trans generated

theorem actual_deposit (state next : State frame) (amount : ℝ)
    (actual : State.deposit? state amount = .ok next) (generated : Good state) : Good next := by
  unfold State.deposit? at actual
  split at actual <;> try contradiction
  cases Except.ok.inj actual
  exact generated

theorem source_fields (state : State frame) (generated : Good state) :
    Orthonormal ℂ (occupiedFields state) :=
  occupied_fields _ (Source.basis_orthonormal state.geometry) _ generated

theorem source_slater (state : State frame) (generated : Good state) :
    slaterDual (occupiedFields state) (slater (occupiedFields state)) = 1 :=
  slater_normalized _ (source_fields state generated)

theorem source_charge (state : State frame) (generated : Good state)
    (chart : Point → SaturationMonoid.PhysicsCore.ProofFreeRicherAnholonomicSource.BasePoint) :
    (∫ x, Native.charge (ContinuousCharge.weights (occupiedFields state) x) (chart x)) =
      -(electronCount frame state.geometry.originJoint : ℂ) :=
  ContinuousCharge.generated_total _ (source_fields state generated) chart

theorem actual_fields (state next : State frame) (time : ℝ)
    (actual : State.pulse? state time = .ok next) (generated : Good state) :
    Orthonormal ℂ (occupiedFields next) ∧
      slaterDual (occupiedFields next) (slater (occupiedFields next)) = 1 :=
  ⟨source_fields next (actual_pulse state next time actual generated),
    source_slater next (actual_pulse state next time actual generated)⟩

end
end CPS1ElectronicEvolution.Consumer
