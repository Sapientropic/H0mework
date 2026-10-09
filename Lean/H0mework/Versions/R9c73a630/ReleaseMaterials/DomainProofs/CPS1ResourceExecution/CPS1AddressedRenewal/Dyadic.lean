import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedRenewal.Renewal

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1AddressedRenewal
noncomputable section
open CPS1Deformation CPS1PositivePulse CPS1AddressedTransfer
open CPS1ElectronicSource (ElectronicPulse)
open scoped Topology
variable {frame : CPS1Recycling.Frame}

structure ActiveMaterial (frame : CPS1Recycling.Frame) where
  material : Material frame
  site : Site material.reference
  sourceSite : selectSite? material.reference = some site
  ready : PulseReady material
  active : responseFlux material site.nuclear 0 ≠ 0

def SuccessfulRenewal (state : ActiveMaterial frame) (index : Nat) : Prop :=
  ∃ pulse : ElectronicPulse,
    state.material.pulse? (dyadicTime index) = .ok (renewedMaterial state.material (dyadicTime index),pulse) ∧
      PulseReady (renewedMaterial state.material (dyadicTime index)) ∧
      normalize? state.material.reference (state.material.movedPositions (dyadicTime index))
        (state.material.transportedOccupation (dyadicTime index)) = .ok (seedOccupation state.material (dyadicTime index)) ∧
      0 < responseFlux state.material state.site.nuclear 0 *
        transferredPopulation state.material state.site.nuclear (dyadicTime index) ∧
      responseFlux (renewedMaterial state.material (dyadicTime index)) state.site.nuclear 0 ≠ 0

theorem exists_successful_renewal (state : ActiveMaterial frame) : ∃ index, SuccessfulRenewal state index := by
  have powers : Filter.Tendsto dyadicTime Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
  obtain ⟨index,present⟩ := (powers.eventually
    (transfer_eventually_renewing state.material state.ready state.site.nuclear state.active)).exists
  exact ⟨index,present (dyadic_time_positive index)⟩

def renewingIndex (state : ActiveMaterial frame) : Nat := by
  classical
  exact Nat.find (exists_successful_renewal state)

def renewingTime (state : ActiveMaterial frame) : ℝ := dyadicTime (renewingIndex state)

theorem renewing_index_spec (state : ActiveMaterial frame) : SuccessfulRenewal state (renewingIndex state) := by
  classical
  exact Nat.find_spec (exists_successful_renewal state)

theorem renewing_index_minimal (state : ActiveMaterial frame) (index : Nat)
    (smaller : index < renewingIndex state) : ¬ SuccessfulRenewal state index := by
  classical
  exact Nat.find_min (exists_successful_renewal state) smaller

def renewingResponse (state : ActiveMaterial frame) : Material frame × ElectronicPulse :=
  match actual : state.material.pulse? (renewingTime state) with
  | .ok next => next
  | .error _ => False.elim (by
      obtain ⟨pulse,same,_⟩ := renewing_index_spec state
      change state.material.pulse? (renewingTime state) = .ok (_,pulse) at same
      rw [actual] at same
      cases same)

theorem renewing_response_actual (state : ActiveMaterial frame) :
    state.material.pulse? (renewingTime state) = .ok (renewingResponse state) := by
  unfold renewingResponse
  split
  · assumption
  · obtain ⟨pulse,same,_⟩ := renewing_index_spec state
    change state.material.pulse? (renewingTime state) = .ok (_,pulse) at same
    contradiction

def advance (state : ActiveMaterial frame) : ActiveMaterial frame := by
  refine ⟨renewedMaterial state.material (renewingTime state),state.site,state.sourceSite,?_,?_⟩
  · obtain ⟨_,_,ready,_⟩ := renewing_index_spec state
    exact ready
  · obtain ⟨_,_,_,_,_,active⟩ := renewing_index_spec state
    exact active

theorem advance_actual (state : ActiveMaterial frame) :
    state.material.pulse? (renewingTime state) = .ok ((advance state).material,(renewingResponse state).2) := by
  obtain ⟨pulse,actual,_⟩ := renewing_index_spec state
  have response : (renewedMaterial state.material (renewingTime state),pulse) = renewingResponse state :=
    Except.ok.inj (actual.symm.trans (renewing_response_actual state))
  have samePulse : pulse = (renewingResponse state).2 := congrArg Prod.snd response
  rw [← samePulse]
  exact actual

theorem advance_material (state : ActiveMaterial frame) :
    (advance state).material = renewedMaterial state.material (renewingTime state) := rfl

theorem advance_site (state : ActiveMaterial frame) : (advance state).site = state.site := rfl

theorem advance_source (state : ActiveMaterial frame) : (advance state).material.reference = state.material.reference := rfl

theorem advance_normalized (state : ActiveMaterial frame) :
    normalize? state.material.reference (state.material.movedPositions (renewingTime state))
      (state.material.transportedOccupation (renewingTime state)) = .ok (seedOccupation state.material (renewingTime state)) := by
  obtain ⟨_,_,_,normalized,_⟩ := renewing_index_spec state
  exact normalized

theorem advance_nonzero (state : ActiveMaterial frame) :
    0 < responseFlux state.material state.site.nuclear 0 *
      transferredPopulation state.material state.site.nuclear (renewingTime state) := by
  obtain ⟨_,_,_,_,signedTransfer,_⟩ := renewing_index_spec state
  exact signedTransfer

theorem advance_paid (state : ActiveMaterial frame) :
    0 < renewingTime state ∧ 0 < (advance state).material.reserve ∧
      (advance state).material.energy+(advance state).material.reserve = state.material.energy+state.material.reserve :=
  ⟨dyadic_time_positive _,(advance state).ready.budget,
    (pulse_paid state.material _ _ (advance_actual state)).2.2.2⟩

end
end CPS1AddressedRenewal
