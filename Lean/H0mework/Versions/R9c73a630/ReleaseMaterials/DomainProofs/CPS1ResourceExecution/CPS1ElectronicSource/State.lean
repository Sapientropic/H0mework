import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Symmetries
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Evolution.Source

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1ElectronicSource
noncomputable section
open scoped Matrix

structure State (frame : CPS1Recycling.Frame) where
  geometry : Geometry frame
  occupied : Matrix (SpinIndex geometry) (ElectronIndex geometry) ℂ
  reserve : ℝ

variable {frame : CPS1Recycling.Frame}

def State.density (state : State frame) : Matrix (SpinIndex state.geometry) (SpinIndex state.geometry) ℂ :=
  state.occupied * state.occupied.conjTranspose

def State.hamiltonian (state : State frame) : Matrix (SpinIndex state.geometry) (SpinIndex state.geometry) ℂ :=
  fock state.geometry state.density

def State.energy (state : State frame) : ℝ := totalEnergy state.geometry state.density

def initialDensity (geometry : Geometry frame) : Matrix (SpinIndex geometry) (SpinIndex geometry) ℂ :=
  occupation geometry * (occupation geometry).conjTranspose

def capturePrice (geometry : Geometry frame) : ℝ :=
  totalEnergy geometry (initialDensity geometry)-geometry.classicalEnergy

def State.fromGeometry? (geometry : Geometry frame) : Except Failure (State frame) :=
  if geometry.originJoint.reserve < 0 then .error .negativeReserve
  else if geometry.originJoint.reserve < capturePrice geometry then .error .energyShortage
  else .ok ⟨geometry,occupation geometry,geometry.originJoint.reserve-capturePrice geometry⟩

def State.fromJoint? (frame : CPS1Recycling.Frame) (joint : CPS1EnzymeBath.Joint.State frame) :
    Except Failure (State frame) := do
  let geometry ← Geometry.fromJoint? frame joint
  fromGeometry? geometry

def State.pulse? (state : State frame) (time : ℝ) : Except Failure (State frame) :=
  if time < 0 then .error .negativeTime
  else if state.reserve < 0 then .error .negativeReserve
  else
    let nextOccupied := CPS1ElectronicEvolution.occupiedUpdate state.hamiltonian (time/2) state.occupied
    let nextDensity := nextOccupied * nextOccupied.conjTranspose
    let price := totalEnergy state.geometry nextDensity-state.energy
    if state.reserve < price then .error .energyShortage
    else .ok ⟨state.geometry,nextOccupied,state.reserve-price⟩

def State.deposit? (state : State frame) (amount : ℝ) : Except Failure (State frame) :=
  if amount < 0 then .error .negativeReserve
  else .ok {state with reserve := state.reserve+amount}

theorem state_density_hermitian (state : State frame) : state.density.IsHermitian := by
  unfold State.density
  exact Matrix.isHermitian_mul_conjTranspose_self _

theorem source_hamiltonian_hermitian (state : State frame) : state.hamiltonian.IsHermitian :=
  fock_hermitian state.geometry state.density (state_density_hermitian state)

end
end CPS1ElectronicSource
