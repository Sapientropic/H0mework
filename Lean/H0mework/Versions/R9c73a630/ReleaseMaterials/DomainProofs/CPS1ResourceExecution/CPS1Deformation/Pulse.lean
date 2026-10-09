import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Mechanics
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Energy

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Deformation
noncomputable section
open CPS1ElectronicSource
open scoped BigOperators Matrix InnerProductSpace Matrix.Norms.Elementwise
variable {frame : CPS1Recycling.Frame}

theorem covariant_energy_line (source : CPS1ElectronicSource.State frame)
    (positions direction : NuclearConfiguration source) (occupied : Occupation source)
    (ready : CPS1AtomicDynamics.Body.ready (nuclearNodesAt source positions)) :
    HasDerivAt (fun time : ℝ => energyAt source (positions+time • direction)
      (occupied+time • occupiedConnectionRate source positions direction occupied))
      (-(∑ nuclear, inner ℝ (euclideanPoint (covariantForce source positions occupied nuclear))
        (euclideanPoint (direction nuclear)))) 0 := by
  have line : HasDerivAt (fun time : ℝ => (positions,occupied)+time •
      (direction,occupiedConnectionRate source positions direction occupied))
      (direction,occupiedConnectionRate source positions direction occupied) 0 := by
    simpa only [one_smul,zero_add,id_eq,Pi.add_apply] using!
      (hasDerivAt_const (0 : ℝ) (positions,occupied)).add
        ((hasDerivAt_id (0 : ℝ)).smul_const (direction,occupiedConnectionRate source positions direction occupied))
  have mother : HasFDerivAt (fun current : EnergyConfiguration source => energyAt source current.1 current.2)
      (energyDifferential source positions occupied)
      ((positions,occupied)+(0 : ℝ) • (direction,occupiedConnectionRate source positions direction occupied)) := by
    simpa only [zero_smul,add_zero] using energy_hasFDerivAt source positions occupied ready
  have actual := mother.comp_hasDerivAt (0 : ℝ) line
  have response : energyDifferential source positions occupied
      (direction,occupiedConnectionRate source positions direction occupied) =
      -(∑ nuclear, inner ℝ (euclideanPoint (covariantForce source positions occupied nuclear))
        (euclideanPoint (direction nuclear))) := covariant_force_work source positions direction occupied
  convert! actual using 1
  exact response.symm

theorem covariant_full_energy_line (source : CPS1ElectronicSource.State frame)
    (positions momenta direction : NuclearConfiguration source) (occupied : Occupation source)
    (ready : CPS1AtomicDynamics.Body.ready (nuclearNodesAt source positions)) :
    HasDerivAt (fun time : ℝ => energyWithMomenta source (positions+time • direction) momenta
      (occupied+time • occupiedConnectionRate source positions direction occupied))
      (-(∑ nuclear, inner ℝ (euclideanPoint (covariantForce source positions occupied nuclear))
        (euclideanPoint (direction nuclear)))) 0 := by
  have line : HasDerivAt (fun time : ℝ => (positions,occupied)+time •
      (direction,occupiedConnectionRate source positions direction occupied))
      (direction,occupiedConnectionRate source positions direction occupied) 0 := by
    simpa only [one_smul,zero_add,id_eq,Pi.add_apply] using!
      (hasDerivAt_const (0 : ℝ) (positions,occupied)).add
        ((hasDerivAt_id (0 : ℝ)).smul_const (direction,occupiedConnectionRate source positions direction occupied))
  have mother : HasFDerivAt (fun current : EnergyConfiguration source => energyWithMomenta source current.1 momenta current.2)
      (energyDifferential source positions occupied)
      ((positions,occupied)+(0 : ℝ) • (direction,occupiedConnectionRate source positions direction occupied)) := by
    simpa only [zero_smul,add_zero] using energy_with_momenta_hasFDerivAt source positions momenta occupied ready
  have actual := mother.comp_hasDerivAt (0 : ℝ) line
  have response : energyDifferential source positions occupied
      (direction,occupiedConnectionRate source positions direction occupied) =
      -(∑ nuclear, inner ℝ (euclideanPoint (covariantForce source positions occupied nuclear))
        (euclideanPoint (direction nuclear))) := covariant_force_work source positions direction occupied
  convert! actual using 1
  exact response.symm

def Material.currentNode (state : Material frame) (node : CPS1AtomicDynamics.Body.Node) :
    CPS1AtomicDynamics.Body.Node :=
  ⟨node.particle,(state.currentRow (node.particle.address,node.row)).2⟩

def Material.currentNodes (state : Material frame) : List CPS1AtomicDynamics.Body.Node :=
  state.reference.geometry.nodes.map state.currentNode

theorem current_nodes_particles (state : Material frame) :
    state.currentNodes.map CPS1AtomicDynamics.Body.Node.particle =
      state.reference.geometry.nodes.map CPS1AtomicDynamics.Body.Node.particle := by
  simp only [Material.currentNodes,List.map_map,Function.comp_def,Material.currentNode]

def fromMolecular (reference : CPS1MolecularFrame.Material frame) (occupied : Occupation reference.reference) :
    Material frame :=
  ⟨reference.reference,sourcePositions reference.reference,sourceMomenta reference.reference,occupied,reference.reserve⟩

def adopt? (reference : CPS1MolecularFrame.Material frame) : Except Failure (Material frame) := by
  classical
  exact
    if reference.reserve < 0 then .error (.inherited (.inherited (.inherited (.inherited .negativeReserve))))
    else match CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame reference.currentJoint)
        reference.currentJoint.rows with
    | .error failure => .error (.inherited (.inherited (.inherited (.inherited (.body failure)))))
    | .ok nodes =>
      if nodes ≠ reference.reference.geometry.nodes then .error (.inherited (.inherited (.inherited .sourceRowsMismatch)))
      else if ¬ CPS1AtomicDynamics.Body.ready nodes then
        .error (.inherited (.inherited (.inherited (.inherited (.body .collision)))))
      else match normalize? reference.reference (sourcePositions reference.reference) reference.occupied with
      | .error failure => .error failure
      | .ok occupied =>
        let generated := fromMolecular reference occupied
        let price := generated.energy-reference.energy
        if reference.reserve < price then .error (.inherited (.inherited (.inherited (.inherited .energyShortage))))
        else .ok (generated.reprice (reference.reserve-price))

def Material.jointForce (state : Material frame) : NuclearConfiguration state.reference :=
  covariantForce state.reference state.positions state.occupied

def Material.movedPositions (state : Material frame) (time : ℝ) : NuclearConfiguration state.reference :=
  kickPositions state.reference state.positions state.momenta state.jointForce time

def Material.movedMomenta (state : Material frame) (time : ℝ) : NuclearConfiguration state.reference :=
  kickMomenta state.reference state.momenta state.jointForce time

def Material.transportedOccupation (state : Material frame) (time : ℝ) : Occupation state.reference :=
  state.occupied + occupiedConnectionRate state.reference state.positions
    (state.movedPositions time-state.positions) state.occupied

def pulseCandidate (state : Material frame) (time : ℝ) (normalized : Occupation state.reference) : Material frame :=
  ⟨state.reference,state.movedPositions time,state.movedMomenta time,
    physicalFockResponse state.reference (state.movedPositions time) normalized time,state.reserve⟩

/-- Complete current rows are checked before the joint energy differential is
sampled. Every emitted coefficient is synthesized into the immutable source basis. -/
def Material.pulse? (state : Material frame) (time : ℝ) : Except Failure (Material frame × ElectronicPulse) := by
  classical
  exact
    if time < 0 then .error (.inherited (.inherited (.inherited (.inherited .negativeTime))))
    else if state.reserve < 0 then .error (.inherited (.inherited (.inherited (.inherited .negativeReserve))))
    else match CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame state.currentJoint)
        state.currentJoint.rows with
    | .error failure => .error (.inherited (.inherited (.inherited (.inherited (.body failure)))))
    | .ok nodes =>
      if nodes ≠ state.currentNodes then .error (.inherited (.inherited (.inherited .sourceRowsMismatch)))
      else if ¬ CPS1AtomicDynamics.Body.ready nodes then
        .error (.inherited (.inherited (.inherited (.inherited (.body .collision)))))
      else if ¬ CPS1AtomicDynamics.Body.ready (nuclearNodesAt state.reference state.positions) then
        .error (.inherited (.inherited (.inherited (.inherited (.body .collision)))))
      else if ¬ ∀ nuclear, 0 < CPS1MolecularFrame.inertia state.reference nuclear then
        .error (.inherited (.inherited .nonpositiveNuclearMass))
      else if ¬ IsUnit (gramAt state.reference state.positions) then .error .singularSourceFrame
      else if ¬ IsUnit (gramAt state.reference (state.movedPositions time)) then .error .singularSourceFrame
      else match normalize? state.reference (state.movedPositions time) (state.transportedOccupation time) with
      | .error failure => .error failure
      | .ok normalized =>
        let generated := pulseCandidate state time normalized
        match CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame generated.currentJoint)
            generated.currentJoint.rows with
        | .error failure => .error (.inherited (.inherited (.inherited (.inherited (.body failure)))))
        | .ok after =>
          if after ≠ generated.currentNodes then .error (.inherited (.inherited (.inherited .sourceRowsMismatch)))
          else if ¬ CPS1AtomicDynamics.Body.ready after then
            .error (.inherited (.inherited (.inherited (.inherited (.body .collision)))))
          else if ¬ CPS1AtomicDynamics.Body.ready (nuclearNodesAt generated.reference generated.positions) then
            .error (.inherited (.inherited (.inherited (.inherited (.body .collision)))))
          else
            let price := generated.energy-state.energy
            if state.reserve < price then .error (.inherited (.inherited (.inherited (.inherited .energyShortage))))
            else
              let current := generated.reprice (state.reserve-price)
              .ok (current,⟨time,state.energy,current.energy,state.reserve,current.reserve⟩)

def Material.deposit? (state : Material frame) (amount : ℝ) : Except Failure (Material frame) :=
  if amount < 0 then .error (.inherited (.inherited (.inherited (.inherited .negativeReserve))))
    else .ok (state.reprice (state.reserve+amount))

end
end CPS1Deformation
