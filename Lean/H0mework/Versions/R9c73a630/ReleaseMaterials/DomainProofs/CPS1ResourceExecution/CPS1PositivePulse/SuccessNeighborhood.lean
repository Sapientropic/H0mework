import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositivePulse.Candidate
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositivePulse.Grounding

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1PositivePulse
noncomputable section
open CPS1Deformation CPS1ElectronicSource
open scoped Topology
variable {frame : CPS1Recycling.Frame}

theorem pairwise_positions_eventually {ι : Type*} (indices : List ι)
    (positions : ℝ → ι → CPS1AtomicDynamics.Body.Point)
    (continuous : ∀ index ∈ indices, ContinuousAt (fun time => positions time index) (0 : ℝ))
    (ready : indices.Pairwise (fun first second => positions 0 first ≠ positions 0 second)) :
    ∀ᶠ time in 𝓝 (0 : ℝ), indices.Pairwise (fun first second => positions time first ≠ positions time second) := by
  classical
  induction indices with
  | nil => exact Filter.Eventually.of_forall fun _ => List.Pairwise.nil
  | cons first rest previous =>
      obtain ⟨apart,remaining⟩ := List.pairwise_cons.mp ready
      have each (second : ι) (member : second ∈ rest.toFinset) :
          ∀ᶠ time in 𝓝 (0 : ℝ), positions time first - positions time second ≠ 0 :=
        ((continuous first List.mem_cons_self).sub
          (continuous second (List.mem_cons_of_mem _ (List.mem_toFinset.mp member)))).eventually_ne
          (sub_ne_zero.mpr (apart second (List.mem_toFinset.mp member)))
      have allApart := (Filter.eventually_all_finset rest.toFinset).mpr each
      have restReady := previous
        (fun index member => continuous index (List.mem_cons_of_mem _ member)) remaining
      filter_upwards [allApart,restReady] with time apartAtTime readyAtTime
      apply List.pairwise_cons.mpr
      exact ⟨fun second member => sub_ne_zero.mp
        (apartAtTime second (List.mem_toFinset.mpr member)),readyAtTime⟩

theorem current_node_position_continuousAt (source : CPS1ElectronicSource.State frame)
    (positions momenta : ℝ → NuclearConfiguration source) (occupied : ℝ → Occupation source) (reserve : ℝ → ℝ)
    (node : CPS1AtomicDynamics.Body.Node) (continuous : ContinuousAt positions (0 : ℝ)) :
    ContinuousAt (fun time =>
      ((⟨source,positions time,momenta time,occupied time,reserve time⟩ : Material frame).currentNode node).row.position)
      (0 : ℝ) := by
  unfold Material.currentNode Material.currentRow Material.nuclearIndex? Material.nuclearRow
  dsimp only
  cases chosen : (List.finRange source.geometry.nuclei.length).find?
      (fun index => CPS1MolecularFrame.address source index = node.particle.address) with
  | none => simp only [chosen]; exact continuousAt_const
  | some index =>
      simp only [chosen]
      exact pointDifferential.continuous.continuousAt.comp
        ((continuous_apply index).continuousAt.comp continuous)

theorem current_ready_eventually (source : CPS1ElectronicSource.State frame)
    (positions momenta : ℝ → NuclearConfiguration source) (occupied : ℝ → Occupation source) (reserve : ℝ → ℝ)
    (continuous : ContinuousAt positions (0 : ℝ))
    (ready : CPS1AtomicDynamics.Body.ready
      (⟨source,positions 0,momenta 0,occupied 0,reserve 0⟩ : Material frame).currentNodes) :
    ∀ᶠ time in 𝓝 (0 : ℝ), CPS1AtomicDynamics.Body.ready
      (⟨source,positions time,momenta time,occupied time,reserve time⟩ : Material frame).currentNodes := by
  have sourceReady : source.geometry.nodes.Pairwise (fun first second =>
      ((⟨source,positions 0,momenta 0,occupied 0,reserve 0⟩ : Material frame).currentNode first).row.position ≠
      ((⟨source,positions 0,momenta 0,occupied 0,reserve 0⟩ : Material frame).currentNode second).row.position) := by
    simpa only [CPS1AtomicDynamics.Body.ready,Material.currentNodes,List.pairwise_map] using ready
  have generated := pairwise_positions_eventually source.geometry.nodes
    (fun time node => ((⟨source,positions time,momenta time,occupied time,reserve time⟩ : Material frame).currentNode node).row.position)
    (fun node _ => current_node_position_continuousAt source positions momenta occupied reserve node continuous) sourceReady
  simpa only [CPS1AtomicDynamics.Body.ready,Material.currentNodes,List.pairwise_map] using generated

theorem nuclear_ready_eventually (source : CPS1ElectronicSource.State frame)
    (positions : ℝ → NuclearConfiguration source) (continuous : ContinuousAt positions (0 : ℝ))
    (ready : CPS1AtomicDynamics.Body.ready (nuclearNodesAt source (positions 0))) :
    ∀ᶠ time in 𝓝 (0 : ℝ), CPS1AtomicDynamics.Body.ready (nuclearNodesAt source (positions time)) := by
  have sourceReady : (List.finRange source.geometry.nuclei.length).Pairwise (fun first second =>
      euclideanPoint (positions 0 first) ≠ euclideanPoint (positions 0 second)) := by
    simpa only [CPS1AtomicDynamics.Body.ready,nuclearNodesAt,List.ofFn_eq_map,List.pairwise_map,nuclearNodeAt] using ready
  have generated := pairwise_positions_eventually (List.finRange source.geometry.nuclei.length)
    (fun time index => euclideanPoint (positions time index))
    (fun index _ => pointDifferential.continuous.continuousAt.comp
      ((continuous_apply index).continuousAt.comp continuous)) sourceReady
  simpa only [CPS1AtomicDynamics.Body.ready,nuclearNodesAt,List.ofFn_eq_map,List.pairwise_map,nuclearNodeAt] using generated

theorem pulse_eventually_success (state : Material frame) (good : Good state)
    (gathered : CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame state.currentJoint)
      state.currentJoint.rows = .ok state.currentNodes)
    (ready : CPS1AtomicDynamics.Body.ready state.currentNodes)
    (nuclearReady : CPS1AtomicDynamics.Body.ready (nuclearNodesAt state.reference state.positions))
    (mass : ∀ nuclear, 0 < CPS1MolecularFrame.inertia state.reference nuclear)
    (unit : IsUnit (gramAt state.reference state.positions)) (budget : 0 < state.reserve) :
    ∀ᶠ time in 𝓝 (0 : ℝ), 0 ≤ time →
      ∃ next : Material frame × ElectronicPulse, state.pulse? time = .ok next := by
  classical
  have positionsContinuous := (moved_positions_continuous state).continuousAt (x := (0 : ℝ))
  have currentUnit : IsUnit (gramAt state.reference (state.movedPositions 0)) := by
    simpa only [Material.movedPositions,kick_positions_zero] using unit
  have unitEventually := basis_unit_eventually state.reference state.movedPositions 0 positionsContinuous currentUnit
  let occupied := fun time : ℝ => (show Occupation state.reference from (continuousPulseCandidate state time).occupied)
  have readyZero : CPS1AtomicDynamics.Body.ready
      (⟨state.reference,state.movedPositions 0,state.movedMomenta 0,occupied 0,state.reserve⟩ : Material frame).currentNodes := by
    change CPS1AtomicDynamics.Body.ready (continuousPulseCandidate state 0).currentNodes
    rw [continuous_pulse_candidate_zero state good unit]
    exact ready
  have readyEventually := current_ready_eventually state.reference state.movedPositions state.movedMomenta
    occupied (fun _ => state.reserve) positionsContinuous readyZero
  have nuclearZero : CPS1AtomicDynamics.Body.ready (nuclearNodesAt state.reference (state.movedPositions 0)) := by
    simpa only [Material.movedPositions,kick_positions_zero] using nuclearReady
  have nuclearEventually := nuclear_ready_eventually state.reference state.movedPositions positionsContinuous nuclearZero
  have gatherAfter (time : ℝ) :
      CPS1AtomicDynamics.Body.gather
        (CPS1EnzymeBath.Joint.particles frame (continuousPulseCandidate state time).currentJoint)
        (continuousPulseCandidate state time).currentJoint.rows =
          .ok (continuousPulseCandidate state time).currentNodes :=
    current_gather_transport state.reference state.positions state.momenta
      (state.movedPositions time) (state.movedMomenta time) state.occupied (occupied time)
      state.reserve state.reserve gathered
  filter_upwards [candidate_normalization_eventually_success state good,unitEventually,
    readyEventually,nuclearEventually,candidate_price_eventually_affordable state good unit nuclearReady budget]
    with time normalized nextUnit nextReady nextNuclear nextPrice
  intro nonnegative
  let candidate := continuousPulseCandidate state time
  let next := candidate.reprice (state.reserve - (candidate.energy-state.energy))
  refine ⟨(next,⟨time,state.energy,next.energy,state.reserve,next.reserve⟩),?_⟩
  unfold Material.pulse?
  rw [if_neg (not_lt.mpr nonnegative),if_neg (not_lt.mpr budget.le),gathered]
  dsimp only
  rw [if_neg (not_ne_iff.mpr rfl),if_neg (not_not.mpr ready),
    if_neg (not_not.mpr nuclearReady),if_neg (not_not.mpr mass),if_neg (not_not.mpr unit),
    if_neg (not_not.mpr nextUnit),normalized]
  dsimp only
  change (match CPS1AtomicDynamics.Body.gather
    (CPS1EnzymeBath.Joint.particles frame candidate.currentJoint) candidate.currentJoint.rows with
    | .error failure => .error (.inherited (.inherited (.inherited (.inherited (.body failure)))))
    | .ok after => if after ≠ candidate.currentNodes then .error (.inherited (.inherited (.inherited .sourceRowsMismatch)))
      else if ¬ CPS1AtomicDynamics.Body.ready after then .error (.inherited (.inherited (.inherited (.inherited (.body .collision)))))
      else if ¬ CPS1AtomicDynamics.Body.ready (nuclearNodesAt candidate.reference candidate.positions) then
        .error (.inherited (.inherited (.inherited (.inherited (.body .collision)))))
      else if state.reserve < candidate.energy-state.energy then
        .error (.inherited (.inherited (.inherited (.inherited .energyShortage))))
      else .ok (next,⟨time,state.energy,next.energy,state.reserve,next.reserve⟩) :
        Except CPS1Deformation.Failure (Material frame × ElectronicPulse)) = _
  rw [gatherAfter time]
  dsimp only
  change CPS1AtomicDynamics.Body.ready (continuousPulseCandidate state time).currentNodes at nextReady
  change CPS1AtomicDynamics.Body.ready (nuclearNodesAt candidate.reference candidate.positions) at nextNuclear
  rw [if_neg (not_ne_iff.mpr rfl),if_neg (not_not.mpr nextReady),if_neg (not_not.mpr nextNuclear),
    if_neg (not_lt.mpr nextPrice.le)]

end
end CPS1PositivePulse
