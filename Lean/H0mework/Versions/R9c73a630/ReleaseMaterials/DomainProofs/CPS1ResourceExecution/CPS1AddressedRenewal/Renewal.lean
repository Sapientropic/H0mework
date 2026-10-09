import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedTransfer.Contract
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositiveContinuation.Renewal

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1AddressedRenewal
noncomputable section
open CPS1Deformation CPS1PositivePulse CPS1AddressedTransfer
open CPS1ElectronicSource (ElectronIndex ElectronicPulse SpinSpace)
open scoped BigOperators Topology
variable {frame : CPS1Recycling.Frame}

def currentFlux (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (occupied : Occupation source) (nuclear : CPS1MolecularFrame.NuclearIndex source) : ℝ :=
  Generic.midpointFlux (siteProjection source positions nuclear) (physicalAction source positions occupied)
    (occupiedFieldsAt source positions occupied) (occupiedFieldsAt source positions occupied)

theorem seed_occupation_zero (state : Material frame) (good : Good state)
    (unit : IsUnit (gramAt state.reference state.positions)) : seedOccupation state 0 = state.occupied := by
  have normalized := (candidate_normalization_eventually_success state good).self_of_nhds
  rw [Material.movedPositions,kick_positions_zero,transported_occupation_zero,
    normalize_good_at_unit _ _ _ unit good] at normalized
  simpa only [seedOccupation,Material.movedPositions,kick_positions_zero,transported_occupation_zero]
    using (Except.ok.inj normalized).symm

theorem response_flux_current (state : Material frame) (good : Good state)
    (unit : IsUnit (gramAt state.reference state.positions))
    (nuclear : CPS1MolecularFrame.NuclearIndex state.reference) :
    responseFlux state nuclear 0 = currentFlux state.reference state.positions state.occupied nuclear := by
  rw [responseFlux,responseAction,seed_occupation_zero state good unit,
    seed_fields_zero state good unit,response_fields_zero state good unit,
    Material.movedPositions,kick_positions_zero]
  rfl

private theorem finite_flux_continuousAt {X E ι : Type*} [TopologicalSpace X] [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (first second : X → ι → E) (current : X)
    (firstContinuous : ∀ slot, ContinuousAt (fun point => first point slot) current)
    (secondContinuous : ∀ slot, ContinuousAt (fun point => second point slot) current) :
    ContinuousAt (fun point => ∑ slot, (inner ℂ (first point slot) (second point slot)).im) current := by
  apply tendsto_finsetSum (Finset.univ : Finset ι)
  intro slot _
  exact Complex.continuous_im.continuousAt.comp
    ((firstContinuous slot).inner (𝕜 := ℂ) (secondContinuous slot))

theorem current_flux_continuousAt {X : Type*} [TopologicalSpace X]
    (source : CPS1ElectronicSource.State frame) (positions : X → NuclearConfiguration source)
    (occupied : X → Occupation source) (current : X)
    (positionsContinuous : ContinuousAt positions current) (occupiedContinuous : ContinuousAt occupied current)
    (unit : IsUnit (gramAt source (positions current))) (nuclear : CPS1MolecularFrame.NuclearIndex source) :
    ContinuousAt (fun point => currentFlux source (positions point) (occupied point) nuclear) current := by
  let midpointFields : X → ElectronIndex source.geometry → SpinSpace :=
    fun point slot => Generic.midpoint (occupiedFieldsAt source (positions point) (occupied point) slot)
      (occupiedFieldsAt source (positions point) (occupied point) slot)
  let actionFields : X → ElectronIndex source.geometry → SpinSpace :=
    fun point slot => physicalAction source (positions point) (occupied point) (midpointFields point slot)
  have midpointContinuous (slot : ElectronIndex source.geometry) :
      ContinuousAt (fun point => midpointFields point slot) current :=
    ((occupied_fields_continuousAt source positions occupied current positionsContinuous occupiedContinuous slot).add
      (occupied_fields_continuousAt source positions occupied current positionsContinuous occupiedContinuous slot)).const_smul (1/2 : ℂ)
  have actionContinuous (slot : ElectronIndex source.geometry) :
      ContinuousAt (fun point => actionFields point slot) current :=
    physical_action_continuousAt_apply source positions occupied (fun point => midpointFields point slot) current
      positionsContinuous occupiedContinuous (midpointContinuous slot) unit
  let projectedMidpoint : X → ElectronIndex source.geometry → SpinSpace :=
    fun point slot => siteProjection source (positions point) nuclear (midpointFields point slot)
  let projectedAction : X → ElectronIndex source.geometry → SpinSpace :=
    fun point slot => siteProjection source (positions point) nuclear (actionFields point slot)
  have firstContinuous (slot : ElectronIndex source.geometry) :
      ContinuousAt (fun point => projectedMidpoint point slot) current :=
    site_projection_continuousAt source positions (fun point => midpointFields point slot) current
      positionsContinuous (midpointContinuous slot) nuclear
  have secondContinuous (slot : ElectronIndex source.geometry) :
      ContinuousAt (fun point => projectedAction point slot) current :=
    site_projection_continuousAt source positions (fun point => actionFields point slot) current
      positionsContinuous (actionContinuous slot) nuclear
  exact finite_flux_continuousAt projectedMidpoint projectedAction current firstContinuous secondContinuous

theorem candidate_good_eventually (state : Material frame) (good : Good state) :
    ∀ᶠ time in 𝓝 (0 : ℝ), Good (continuousPulseCandidate state time) := by
  filter_upwards [candidate_normalization_eventually_success state good] with time normalized
  exact response_after_good state time normalized

theorem candidate_unit_eventually (state : Material frame)
    (unit : IsUnit (gramAt state.reference state.positions)) :
    ∀ᶠ time in 𝓝 (0 : ℝ),
      IsUnit (gramAt (continuousPulseCandidate state time).reference (continuousPulseCandidate state time).positions) := by
  have currentUnit : IsUnit (gramAt state.reference (state.movedPositions 0)) := by
    simpa only [Material.movedPositions,kick_positions_zero] using unit
  exact basis_unit_eventually state.reference state.movedPositions (0 : ℝ)
    (moved_positions_continuous state).continuousAt currentUnit

theorem candidate_flux_continuousAt_zero (state : Material frame) (ready : PulseReady state)
    (nuclear : CPS1MolecularFrame.NuclearIndex state.reference) :
    ContinuousAt (fun time => responseFlux (continuousPulseCandidate state time) nuclear 0) (0 : ℝ) := by
  let occupied : ℝ → Occupation state.reference := fun time => (continuousPulseCandidate state time).occupied
  have occupationContinuous : ContinuousAt occupied (0 : ℝ) := candidate_occupied_continuousAt_zero state ready.good ready.unit
  have currentUnit : IsUnit (gramAt state.reference (state.movedPositions 0)) := by
    simpa only [Material.movedPositions,kick_positions_zero] using ready.unit
  have generated : ContinuousAt
      (fun time => currentFlux state.reference (state.movedPositions time) (occupied time) nuclear) (0 : ℝ) :=
    current_flux_continuousAt state.reference state.movedPositions occupied 0
      (moved_positions_continuous state).continuousAt occupationContinuous currentUnit nuclear
  have same : (fun time => responseFlux (continuousPulseCandidate state time) nuclear 0) =ᶠ[𝓝 (0 : ℝ)]
      (fun time => currentFlux state.reference (state.movedPositions time) (occupied time) nuclear) := by
    filter_upwards [candidate_good_eventually state ready.good,candidate_unit_eventually state ready.unit]
      with time good unit
    exact response_flux_current (continuousPulseCandidate state time) good unit nuclear
  exact generated.congr_of_eventuallyEq same

theorem candidate_flux_zero (state : Material frame) (ready : PulseReady state)
    (nuclear : CPS1MolecularFrame.NuclearIndex state.reference) :
    responseFlux (continuousPulseCandidate state 0) nuclear 0 = responseFlux state nuclear 0 := by
  have occupiedZero : (continuousPulseCandidate state 0).occupied = state.occupied := by
    change physicalFockResponse state.reference (state.movedPositions 0) (seedOccupation state 0) 0 = state.occupied
    rw [Material.movedPositions,kick_positions_zero,seed_occupation_zero state ready.good ready.unit,
      physical_fock_response_coefficients_zero _ _ _ ready.unit]
  have good : Good (continuousPulseCandidate state 0) := (candidate_good_eventually state ready.good).self_of_nhds
  have unit : IsUnit (gramAt (continuousPulseCandidate state 0).reference
      (continuousPulseCandidate state 0).positions) := (candidate_unit_eventually state ready.unit).self_of_nhds
  rw [response_flux_current (continuousPulseCandidate state 0) good unit nuclear]
  change currentFlux state.reference (state.movedPositions 0) (continuousPulseCandidate state 0).occupied nuclear = _
  rw [Material.movedPositions,kick_positions_zero,occupiedZero]
  exact (response_flux_current state ready.good ready.unit nuclear).symm

theorem response_flux_reprice (state : Material frame) (reserve : ℝ)
    (nuclear : CPS1MolecularFrame.NuclearIndex state.reference) (time : ℝ) :
    responseFlux (state.reprice reserve) nuclear time = responseFlux state nuclear time := rfl

theorem candidate_same_site (state : Material frame) (time : ℝ) :
    selectSite? (continuousPulseCandidate state time).reference = selectSite? state.reference := rfl

def renewedMaterial (state : Material frame) (time : ℝ) : Material frame :=
  (continuousPulseCandidate state time).reprice
    (state.reserve-((continuousPulseCandidate state time).energy-state.energy))

theorem renewed_material_actual (state : Material frame) (next : Material frame × ElectronicPulse) (time : ℝ)
    (actual : state.pulse? time = .ok next)
    (normalized : normalize? state.reference (state.movedPositions time) (state.transportedOccupation time) =
      .ok (seedOccupation state time)) : next.1 = renewedMaterial state time :=
  response_seed_actual state next time actual normalized

theorem renewed_material_site (state : Material frame) (time : ℝ) :
    selectSite? (renewedMaterial state time).reference = selectSite? state.reference := rfl

theorem renewed_material_flux (state : Material frame) (time : ℝ)
    (nuclear : CPS1MolecularFrame.NuclearIndex state.reference) :
    responseFlux (renewedMaterial state time) nuclear 0 = responseFlux (continuousPulseCandidate state time) nuclear 0 := rfl

theorem transfer_eventually_renewing (state : Material frame) (ready : PulseReady state)
    (nuclear : CPS1MolecularFrame.NuclearIndex state.reference) (active : responseFlux state nuclear 0 ≠ 0) :
    ∀ᶠ time in 𝓝 (0 : ℝ), 0 < time →
      ∃ pulse : ElectronicPulse,
        state.pulse? time = .ok (renewedMaterial state time,pulse) ∧ PulseReady (renewedMaterial state time) ∧
          normalize? state.reference (state.movedPositions time) (state.transportedOccupation time) =
            .ok (seedOccupation state time) ∧
          0 < responseFlux state nuclear 0 * transferredPopulation state nuclear time ∧
          responseFlux (renewedMaterial state time) nuclear 0 ≠ 0 := by
  have initialActive : responseFlux (continuousPulseCandidate state 0) nuclear 0 ≠ 0 := by
    rw [candidate_flux_zero state ready nuclear]
    exact active
  have remainsActive := (candidate_flux_continuousAt_zero state ready nuclear).eventually_ne initialActive
  filter_upwards [CPS1AddressedTransfer.transfer_eventually_positive state ready nuclear active,remainsActive]
    with time success renewedActive
  intro timePositive
  obtain ⟨next,actual,nextReady,normalized,signedTransfer⟩ := success timePositive
  have same : next.1 = renewedMaterial state time := renewed_material_actual state next time actual normalized
  have pair : next = (renewedMaterial state time,next.2) := by
    exact Prod.ext same rfl
  refine ⟨next.2,?_,same ▸ nextReady,normalized,signedTransfer,?_⟩
  · rw [← pair]
    exact actual
  · rw [renewed_material_flux]
    exact renewedActive

end
end CPS1AddressedRenewal
