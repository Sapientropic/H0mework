import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Integrals
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Initial
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Relocation

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1MolecularFrame
noncomputable section
open CPS1ElectronicSource
open scoped Matrix InnerProductSpace

inductive Failure
  | inherited (failure : CPS1Following.Failure)
  | missingDirections
  deriving DecidableEq

structure Material (frame : CPS1Recycling.Frame) where
  reference : CPS1ElectronicSource.State frame
  occupied : Matrix (MolecularIndex reference) (ElectronIndex reference.geometry) ℂ
  reserve : ℝ

variable {frame : CPS1Recycling.Frame}

def Material.currentJoint (state : Material frame) : CPS1EnzymeBath.Joint.State frame :=
  {state.reference.geometry.originJoint with reserve := state.reserve}

theorem material_current_rows (state : Material frame) :
    state.currentJoint.rows = state.reference.geometry.originJoint.rows := rfl

theorem material_current_particles (state : Material frame) :
    CPS1EnzymeBath.Joint.particles frame state.currentJoint =
      CPS1EnzymeBath.Joint.particles frame state.reference.geometry.originJoint := rfl

theorem material_current_reserve (state : Material frame) : state.currentJoint.reserve = state.reserve := rfl

def Material.density (state : Material frame) : Matrix (MolecularIndex state.reference) (MolecularIndex state.reference) ℂ :=
  state.occupied * state.occupied.conjTranspose

def Material.energy (state : Material frame) : ℝ := totalEnergy state.reference state.density

def Material.hamiltonian (state : Material frame) : Matrix (MolecularIndex state.reference) (MolecularIndex state.reference) ℂ :=
  fock state.reference state.density

def Material.currentFields (state : Material frame) : ElectronIndex state.reference.geometry → SpinSpace :=
  CPS1ElectronicEvolution.fields (FiniteNormed.field (𝕜 := ℂ) (rawField state.reference)) state.occupied

def Good (state : Material frame) : Prop := state.occupied.conjTranspose * state.occupied = 1

def Material.reprice (state : Material frame) (reserve : ℝ) : Material frame :=
  {state with reserve := reserve}

def adopt? (reference : CPS1ElectronicSource.State frame) : Except Failure (Material frame) := by
  classical
  exact
    if reference.reserve < 0 then .error (.inherited (.inherited (.inherited .negativeReserve)))
    else match CPS1AtomicDynamics.Body.gather
        (CPS1EnzymeBath.Joint.particles frame reference.geometry.originJoint) reference.geometry.originJoint.rows with
    | .error failure => .error (.inherited (.inherited (.inherited (.body failure))))
    | .ok nodes =>
      if nodes ≠ reference.geometry.nodes then .error (.inherited (.inherited .sourceRowsMismatch))
      else if ¬ CPS1AtomicDynamics.Body.ready nodes then .error (.inherited (.inherited (.inherited (.body .collision))))
      else if enough : electronCount frame reference.geometry.originJoint ≤ FiniteNormed.rank (𝕜 := ℂ) (rawField reference) then
        let generated : Material frame := ⟨reference,initialOccupation reference enough,reference.reserve⟩
        let price := generated.energy-CPS1Following.energy reference
        if reference.reserve < price then .error (.inherited (.inherited (.inherited .energyShortage)))
        else .ok (generated.reprice (reference.reserve-price))
      else .error .missingDirections

def Material.pulse? (state : Material frame) (time : ℝ) : Except Failure (Material frame) := by
  classical
  exact
    if time < 0 then .error (.inherited (.inherited (.inherited .negativeTime)))
    else if state.reserve < 0 then .error (.inherited (.inherited (.inherited .negativeReserve)))
    else
      let occupied := CPS1ElectronicEvolution.occupiedUpdate state.hamiltonian (time/2) state.occupied
      let generated : Material frame := ⟨state.reference,occupied,state.reserve⟩
      let price := generated.energy-state.energy
      if state.reserve < price then .error (.inherited (.inherited (.inherited .energyShortage)))
      else .ok (generated.reprice (state.reserve-price))

def Material.deposit? (state : Material frame) (amount : ℝ) : Except Failure (Material frame) :=
  if amount < 0 then .error (.inherited (.inherited (.inherited .negativeReserve)))
  else .ok (state.reprice (state.reserve+amount))

theorem material_density_hermitian (state : Material frame) : state.density.IsHermitian :=
  Matrix.isHermitian_mul_conjTranspose_self _

theorem material_hamiltonian_hermitian (state : Material frame) : state.hamiltonian.IsHermitian :=
  fock_hermitian state.reference state.density (material_density_hermitian state)

theorem material_fields (state : Material frame) (generated : Good state) :
    Orthonormal ℂ state.currentFields :=
  CPS1ElectronicEvolution.occupied_fields _ (FiniteNormed.field_orthonormal (rawField state.reference)) _ generated

theorem material_slater (state : Material frame) (generated : Good state) :
    CPS1ElectronicEvolution.slaterDual state.currentFields (CPS1ElectronicEvolution.slater state.currentFields) = 1 :=
  CPS1ElectronicEvolution.slater_normalized _ (material_fields state generated)

end
end CPS1MolecularFrame
