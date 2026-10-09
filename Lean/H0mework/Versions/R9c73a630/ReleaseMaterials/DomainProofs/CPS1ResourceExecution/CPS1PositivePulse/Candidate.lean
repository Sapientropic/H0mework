import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositivePulse.WholeBasisResponse
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Payment

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1PositivePulse
noncomputable section
open CPS1Deformation CPS1ElectronicSource
open scoped BigOperators Topology Matrix.Norms.Elementwise
variable {frame : CPS1Recycling.Frame}

def continuousPulseCandidate (state : Material frame) (time : ℝ) : Material frame :=
  pulseCandidate state time (normalizedOccupationCandidate state.reference
    (state.movedPositions time) (state.transportedOccupation time))

theorem moved_positions_continuous (state : Material frame) : Continuous state.movedPositions := by
  apply continuous_pi
  intro nuclear
  change Continuous (fun time : ℝ => state.positions nuclear +
    (time / CPS1MolecularFrame.inertia state.reference nuclear) • state.momenta nuclear +
    (time^2 / (2 * CPS1MolecularFrame.inertia state.reference nuclear)) • state.jointForce nuclear)
  exact (continuous_const.add ((continuous_id.div_const _).smul continuous_const)).add
    ((continuous_id.pow 2).div_const _ |>.smul continuous_const)

theorem moved_momenta_continuous (state : Material frame) : Continuous state.movedMomenta :=
  continuous_const.add (continuous_id.smul continuous_const)

theorem transported_occupation_continuous (state : Material frame) :
    Continuous state.transportedOccupation := by
  have directionContinuous : Continuous (fun time : ℝ => state.movedPositions time - state.positions) :=
    (moved_positions_continuous state).sub continuous_const
  have rateContinuous := (occupiedConnectionDifferential state.reference state.positions state.occupied).continuous.comp
    directionContinuous
  exact continuous_const.add rateContinuous

theorem transported_good_at_zero (state : Material frame) (good : Good state) :
    Orthonormal ℂ (occupiedFieldsAt state.reference (state.movedPositions 0) (state.transportedOccupation 0)) := by
  rw [Material.movedPositions,kick_positions_zero,transported_occupation_zero]
  exact good

theorem candidate_normalization_eventually_success (state : Material frame) (good : Good state) :
    ∀ᶠ time in 𝓝 (0 : ℝ), normalize? state.reference
      (state.movedPositions time) (state.transportedOccupation time) =
        .ok (normalizedOccupationCandidate state.reference
          (state.movedPositions time) (state.transportedOccupation time)) :=
  normalize_eventually_success state.reference state.movedPositions state.transportedOccupation 0
    (moved_positions_continuous state).continuousAt (transported_occupation_continuous state).continuousAt
    (transported_good_at_zero state good)

theorem candidate_occupied_continuousAt_zero (state : Material frame) (good : Good state)
    (unit : IsUnit (gramAt state.reference state.positions)) :
    ContinuousAt (fun time => (show Occupation state.reference from
      (continuousPulseCandidate state time).occupied)) (0 : ℝ) := by
  have normalizedContinuous := normalized_occupation_candidate_continuousAt state.reference
    state.movedPositions state.transportedOccupation 0
    (moved_positions_continuous state).continuousAt (transported_occupation_continuous state).continuousAt
    (transported_good_at_zero state good)
  have currentUnit : IsUnit (gramAt state.reference (state.movedPositions 0)) := by
    simpa only [Material.movedPositions,kick_positions_zero] using unit
  exact physical_fock_response_continuousAt state.reference state.movedPositions
    (fun time => normalizedOccupationCandidate state.reference
      (state.movedPositions time) (state.transportedOccupation time)) id 0
    (moved_positions_continuous state).continuousAt normalizedContinuous continuousAt_id currentUnit

theorem continuous_pulse_candidate_zero (state : Material frame) (good : Good state)
    (unit : IsUnit (gramAt state.reference state.positions)) :
    continuousPulseCandidate state 0 = state := by
  have initial := (candidate_normalization_eventually_success state good).self_of_nhds
  have positions : state.movedPositions 0 = state.positions := kick_positions_zero _ _ _ _
  rw [positions,transported_occupation_zero,normalize_good_at_unit _ _ _ unit good] at initial
  have normalized : normalizedOccupationCandidate state.reference
      (state.movedPositions 0) (state.transportedOccupation 0) = state.occupied :=
    by simpa only [positions,transported_occupation_zero] using (Except.ok.inj initial).symm
  unfold continuousPulseCandidate pulseCandidate
  rw [normalized,positions]
  change (⟨state.reference,state.positions,
    kickMomenta state.reference state.momenta state.jointForce 0,
    physicalFockResponse state.reference state.positions state.occupied 0,state.reserve⟩ : Material frame) = state
  rw [kick_momenta_zero,physical_fock_response_coefficients_zero _ _ _ unit]

theorem fixed_source_energy_continuousAt_zero (source : CPS1ElectronicSource.State frame)
    (positions momenta : ℝ → NuclearConfiguration source) (occupied : ℝ → Occupation source)
    (positionsContinuous : ContinuousAt positions (0 : ℝ))
    (momentaContinuous : ContinuousAt momenta (0 : ℝ))
    (occupiedContinuous : ContinuousAt occupied (0 : ℝ))
    (ready : CPS1AtomicDynamics.Body.ready (nuclearNodesAt source (positions 0))) :
    ContinuousAt (fun time => energyWithMomenta source (positions time) (momenta time) (occupied time)) (0 : ℝ) := by
  have nuclearMother : ContinuousAt (fun current : NuclearConfiguration source × NuclearConfiguration source =>
      nuclearEnergyAt source current.1 current.2) (positions 0,momenta 0) :=
    (nuclear_energy_hasFDerivAt source (positions 0) (momenta 0) ready).continuousAt
  have nuclearContinuous : ContinuousAt (fun time : ℝ => nuclearEnergyAt source (positions time) (momenta time)) 0 :=
    nuclearMother.comp' (f := fun time => (positions time,momenta time))
      (positionsContinuous.prodMk momentaContinuous)
  have electronicMother : ContinuousAt (fun current : EnergyConfiguration source =>
      electronicEnergyAt source current.1 current.2) (positions 0,occupied 0) :=
    (electronic_energy_differentiable source (positions 0) (occupied 0)).continuousAt
  have electronicContinuous : ContinuousAt (fun time : ℝ => electronicEnergyAt source (positions time) (occupied time)) 0 :=
    electronicMother.comp' (f := fun time => (positions time,occupied time))
      (positionsContinuous.prodMk occupiedContinuous)
  exact nuclearContinuous.add electronicContinuous

theorem candidate_energy_continuousAt_zero (state : Material frame) (good : Good state)
    (unit : IsUnit (gramAt state.reference state.positions))
    (ready : CPS1AtomicDynamics.Body.ready (nuclearNodesAt state.reference state.positions)) :
    ContinuousAt (fun time => (continuousPulseCandidate state time).energy) (0 : ℝ) := by
  let positions : ℝ → NuclearConfiguration state.reference := state.movedPositions
  let momenta : ℝ → NuclearConfiguration state.reference := state.movedMomenta
  let occupied : ℝ → Occupation state.reference := fun time => (continuousPulseCandidate state time).occupied
  have positionsContinuous : ContinuousAt positions (0 : ℝ) := (moved_positions_continuous state).continuousAt
  have momentaContinuous : ContinuousAt momenta (0 : ℝ) := (moved_momenta_continuous state).continuousAt
  have occupiedContinuous : ContinuousAt occupied (0 : ℝ) := candidate_occupied_continuousAt_zero state good unit
  have nuclearReady : CPS1AtomicDynamics.Body.ready (nuclearNodesAt state.reference (positions 0)) := by
    simpa only [positions,Material.movedPositions,kick_positions_zero] using ready
  have source := fixed_source_energy_continuousAt_zero state.reference positions momenta occupied
    positionsContinuous momentaContinuous occupiedContinuous nuclearReady
  exact source

theorem candidate_price_eventually_affordable (state : Material frame) (good : Good state)
    (unit : IsUnit (gramAt state.reference state.positions))
    (ready : CPS1AtomicDynamics.Body.ready (nuclearNodesAt state.reference state.positions))
    (budget : 0 < state.reserve) :
    ∀ᶠ time in 𝓝 (0 : ℝ),
      (continuousPulseCandidate state time).energy - state.energy < state.reserve := by
  have priceContinuous : ContinuousAt (fun time =>
      (continuousPulseCandidate state time).energy - state.energy) (0 : ℝ) :=
    (candidate_energy_continuousAt_zero state good unit ready).sub continuousAt_const
  have initialPrice : (continuousPulseCandidate state 0).energy - state.energy = 0 := by
    rw [continuous_pulse_candidate_zero state good unit,sub_self]
  exact priceContinuous.eventually_mem (isOpen_Iio.mem_nhds (by
    change (continuousPulseCandidate state 0).energy - state.energy < state.reserve
    rw [initialPrice]
    exact budget))

end
end CPS1PositivePulse
