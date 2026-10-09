import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositivePulse.Dyadic

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1PositiveContinuation
noncomputable section
open CPS1Deformation CPS1ElectronicSource CPS1PositivePulse
open scoped Topology
variable {frame : CPS1Recycling.Frame}

theorem pulse_ready_of_positive_reserve (state : Material frame) (ready : PulseReady state)
    (next : Material frame × ElectronicPulse) (time : ℝ)
    (actual : state.pulse? time = .ok next) (budget : 0 < next.1.reserve) :
    PulseReady next.1 := by
  obtain ⟨_,_,_,_,gathered,nextReady,nuclearReady,unit⟩ := pulse_grounded state next time actual
  refine ⟨pulse_good state next time actual,gathered,nextReady,nuclearReady,?_,unit,budget⟩
  rw [(pulse_same_source state next time actual).1]
  exact ready.mass

theorem pulse_ready_of_strict_price (state : Material frame) (ready : PulseReady state)
    (next : Material frame × ElectronicPulse) (time : ℝ)
    (actual : state.pulse? time = .ok next)
    (price : next.1.energy-state.energy < state.reserve) : PulseReady next.1 := by
  apply pulse_ready_of_positive_reserve state ready next time actual
  have total := (pulse_paid state next time actual).2.2.2
  linarith

theorem pulse_candidate_energy (state : Material frame) (next : Material frame × ElectronicPulse)
    (time : ℝ) (actual : state.pulse? time = .ok next)
    (normalization : normalize? state.reference (state.movedPositions time) (state.transportedOccupation time) =
      .ok (normalizedOccupationCandidate state.reference (state.movedPositions time)
        (state.transportedOccupation time))) :
    next.1.energy = (continuousPulseCandidate state time).energy := by
  obtain ⟨normalized,normalizedActual,same,_,_,_,_,_,_,_,_,_,_,_⟩ := pulse_outcome state next time actual
  have unchanged : normalized = normalizedOccupationCandidate state.reference
      (state.movedPositions time) (state.transportedOccupation time) :=
    Except.ok.inj (normalizedActual.symm.trans normalization)
  rw [same,material_reprice_energy,unchanged]
  rfl

theorem pulse_eventually_ready (state : Material frame) (ready : PulseReady state) :
    ∀ᶠ time in 𝓝 (0 : ℝ), 0 ≤ time →
      ∃ next : Material frame × ElectronicPulse, state.pulse? time = .ok next ∧ PulseReady next.1 := by
  filter_upwards [pulse_eventually_success state ready.good ready.gathered ready.ready ready.nuclearReady
      ready.mass ready.unit ready.budget,
    candidate_normalization_eventually_success state ready.good,
    candidate_price_eventually_affordable state ready.good ready.unit ready.nuclearReady ready.budget]
    with time success normalized price
  intro nonnegative
  obtain ⟨next,actual⟩ := success nonnegative
  refine ⟨next,actual,pulse_ready_of_strict_price state ready next time actual ?_⟩
  rw [pulse_candidate_energy state next time actual normalized]
  exact price

end
end CPS1PositiveContinuation
