import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1QuantumNuclear.Mechanics
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1QuantumNuclear.Force

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1QuantumNuclear
noncomputable section
open CPS1ElectronicSource
open scoped Matrix

inductive Failure
  | inherited (failure : CPS1ElectronicSource.Failure)
  | sourceRowsMismatch
  deriving DecidableEq

variable {frame : CPS1Recycling.Frame}

def currentPrice (state : CPS1ElectronicSource.State frame) (reserve : ℝ) : CPS1ElectronicSource.State frame :=
  ⟨⟨{state.geometry.originJoint with reserve := reserve},state.geometry.nodes⟩,state.occupied,reserve⟩

theorem currentPrice_energy (state : CPS1ElectronicSource.State frame) (reserve : ℝ) :
    (currentPrice state reserve).energy = state.energy := rfl

/-- Current source rows are checked before force sampling. No caller supplies
coverage or a replacement geometry; the actual electronic reserve owns payment. -/
def pulse? (state : CPS1ElectronicSource.State frame) (time : ℝ) :
    Except Failure (CPS1ElectronicSource.State frame × ElectronicPulse) := by
  classical
  exact
    if time < 0 then .error (.inherited .negativeTime)
    else if state.reserve < 0 then .error (.inherited .negativeReserve)
    else match CPS1AtomicDynamics.Body.gather
        (CPS1EnzymeBath.Joint.particles frame state.geometry.originJoint) state.geometry.originJoint.rows with
    | .error failure => .error (.inherited (.body failure))
    | .ok sourceNodes =>
      if sourceNodes ≠ state.geometry.nodes then .error .sourceRowsMismatch
      else if ¬ CPS1AtomicDynamics.Body.ready sourceNodes then .error (.inherited (.body .collision))
      else
        let nodes := nextNodes state (nuclearForce state) time
        let joint := movedJoint state nodes
        match CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame joint) joint.rows with
        | .error failure => .error (.inherited (.body failure))
        | .ok after =>
          if ¬ CPS1AtomicDynamics.Body.ready after then .error (.inherited (.body .collision))
          else
            let moved : CPS1ElectronicSource.State frame := ⟨⟨joint,after⟩,state.occupied,state.reserve⟩
            let occupied := CPS1ElectronicEvolution.occupiedUpdate moved.hamiltonian (time/2) moved.occupied
            let next : CPS1ElectronicSource.State frame := ⟨moved.geometry,occupied,state.reserve⟩
            let price := next.energy-state.energy
            if state.reserve < price then .error (.inherited .energyShortage)
            else
              let reserve := state.reserve-price
              let current := currentPrice next reserve
              .ok (current,⟨time,state.energy,current.energy,state.reserve,current.reserve⟩)

end
end CPS1QuantumNuclear
