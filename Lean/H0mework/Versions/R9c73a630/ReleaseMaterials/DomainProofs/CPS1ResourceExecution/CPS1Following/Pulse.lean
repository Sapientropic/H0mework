import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Motion
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Force
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Connection

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Following
noncomputable section
open CPS1ElectronicSource
variable {frame : CPS1Recycling.Frame}

def centreVelocity (before after : CPS1ElectronicSource.State frame) (time : ℝ) : Point :=
  fun axis => (centre after axis-centre before axis)/time

/-- The displacement is source generated. The moving-frame connection is
subtracted from the same new-geometry Fock operator before coefficient evolution. -/
def stepHamiltonian (before after : CPS1ElectronicSource.State frame) (time : ℝ) :
    Matrix (SpinIndex after.geometry) (SpinIndex after.geometry) ℂ :=
  followingHamiltonian (relativeState after) (centreVelocity before after time)

def pulse? (state : CPS1ElectronicSource.State frame) (time : ℝ) :
    Except Failure (CPS1ElectronicSource.State frame × ElectronicPulse) := by
  classical
  exact
    if time < 0 then .error (.inherited (.inherited .negativeTime))
    else if state.reserve < 0 then .error (.inherited (.inherited .negativeReserve))
    else match CPS1AtomicDynamics.Body.gather
        (CPS1EnzymeBath.Joint.particles frame state.geometry.originJoint) state.geometry.originJoint.rows with
    | .error failure => .error (.inherited (.inherited (.body failure)))
    | .ok sourceNodes =>
      if sourceNodes ≠ state.geometry.nodes then .error (.inherited .sourceRowsMismatch)
      else if ¬ CPS1AtomicDynamics.Body.ready sourceNodes then .error (.inherited (.inherited (.body .collision)))
      else if massTotal state ≤ 0 then .error .nonpositiveNuclearMass
      else
        let nodes := CPS1QuantumNuclear.nextNodes state (nuclearForce state) time
        if ¬ CPS1AtomicDynamics.Body.ready nodes then .error (.inherited (.inherited (.body .collision)))
        else
          let moved := CPS1QuantumNuclear.movedState state nodes
          let occupied := followingOccupied (relativeState moved) (centreVelocity state moved time) time
          let next : CPS1ElectronicSource.State frame := ⟨moved.geometry,occupied,state.reserve⟩
          let price := energy next-energy state
          if state.reserve < price then .error (.inherited (.inherited .energyShortage))
          else
            let current := CPS1QuantumNuclear.currentPrice next (state.reserve-price)
            .ok (current,⟨time,energy state,energy current,state.reserve,current.reserve⟩)

theorem step_hamiltonian_hermitian (before after : CPS1ElectronicSource.State frame) (time : ℝ) :
    (stepHamiltonian before after time).IsHermitian :=
  following_hamiltonian_hermitian (relativeState after) (centreVelocity before after time)

end
end CPS1Following
