import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedBondRenewal.Renewal

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1AddressedBondRenewal
noncomputable section
open CPS1Deformation CPS1PositivePulse CPS1AddressedBondResponse CPS1AddressedTransfer
open CPS1AddressedRenewal (renewedMaterial)
open CPS1ElectronicSource (ElectronicPulse)
open scoped Topology
variable {frame : CPS1Recycling.Frame}

structure ActiveMaterial (frame : CPS1Recycling.Frame) where
  material : Material frame
  site : BridgeSite material.reference
  sourceSite : selectBridge? material.reference = some site
  ready : PulseReady material
  active : responseFlux material site.phosphate.nuclear 0 ≠ 0
  degree : CPS1AddressedBondResponse.Generic.Degree
  drive : (distancePolynomial material site).leading? = some degree

def SuccessfulRenewal (state : ActiveMaterial frame) (index : Nat) : Prop :=
  RenewingResponse state.material state.site state.degree (dyadicTime index)

theorem exists_successful_renewal (state : ActiveMaterial frame) : ∃ index, SuccessfulRenewal state index := by
  have powers : Filter.Tendsto dyadicTime Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
  obtain ⟨index,present⟩ := (powers.eventually
    (bridge_response_eventually_renewing state.material state.ready state.site state.active state.degree state.drive)).exists
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

def nextDegree (state : ActiveMaterial frame) : CPS1AddressedBondResponse.Generic.Degree :=
  match generated : (distancePolynomial (renewedMaterial state.material (renewingTime state)) state.site).leading? with
  | some degree => degree
  | none => False.elim (by
      obtain ⟨_,_,_,_,_,_,_,_,future⟩ := renewing_index_spec state
      change ∃ degree, (distancePolynomial (renewedMaterial state.material (renewingTime state)) state.site).leading? = some degree at future
      obtain ⟨degree,present⟩ := future
      rw [generated] at present
      cases present)

theorem next_degree_spec (state : ActiveMaterial frame) :
    (distancePolynomial (renewedMaterial state.material (renewingTime state)) state.site).leading? = some (nextDegree state) := by
  unfold nextDegree
  split
  · assumption
  · obtain ⟨_,_,_,_,_,_,_,_,future⟩ := renewing_index_spec state
    obtain ⟨degree,present⟩ := future
    contradiction

def advance (state : ActiveMaterial frame) : ActiveMaterial frame := by
  refine ⟨renewedMaterial state.material (renewingTime state),state.site,state.sourceSite,?_,?_,nextDegree state,next_degree_spec state⟩
  · obtain ⟨_,_,ready,_⟩ := renewing_index_spec state
    exact ready
  · obtain ⟨_,_,_,_,_,active,_⟩ := renewing_index_spec state
    exact active

theorem advance_actual (state : ActiveMaterial frame) :
    state.material.pulse? (renewingTime state) = .ok ((advance state).material,(renewingResponse state).2) := by
  obtain ⟨pulse,actual,_⟩ := renewing_index_spec state
  have response : (renewedMaterial state.material (renewingTime state),pulse) = renewingResponse state :=
    Except.ok.inj (actual.symm.trans (renewing_response_actual state))
  have samePulse : pulse = (renewingResponse state).2 := congrArg Prod.snd response
  rw [← samePulse]
  exact actual

theorem advance_source (state : ActiveMaterial frame) : (advance state).material.reference = state.material.reference := rfl

theorem advance_site (state : ActiveMaterial frame) : (advance state).site = state.site := rfl

theorem advance_normalized (state : ActiveMaterial frame) :
    normalize? state.material.reference (state.material.movedPositions (renewingTime state))
      (state.material.transportedOccupation (renewingTime state)) = .ok (seedOccupation state.material (renewingTime state)) := by
  obtain ⟨_,_,_,normalized,_⟩ := renewing_index_spec state
  exact normalized

theorem advance_signed_electronic (state : ActiveMaterial frame) :
    0 < responseFlux state.material state.site.phosphate.nuclear 0 *
      transferredPopulation state.material state.site.phosphate.nuclear (renewingTime state) := by
  obtain ⟨_,_,_,_,signed,_⟩ := renewing_index_spec state
  exact signed

theorem advance_signed_distance (state : ActiveMaterial frame) :
    0 < (distancePolynomial state.material state.site).coefficient state.degree *
      (squaredDistance (state.material.movedPositions (renewingTime state)) state.site-
        squaredDistance state.material.positions state.site) := by
  obtain ⟨_,_,_,_,_,_,signed,_⟩ := renewing_index_spec state
  exact signed

theorem advance_nonzero_velocity (state : ActiveMaterial frame) :
    relativeVelocity (advance state).material (advance state).site ≠ 0 := by
  obtain ⟨_,_,_,_,_,_,_,velocity,_⟩ := renewing_index_spec state
  exact velocity

theorem advance_paid (state : ActiveMaterial frame) :
    0 < renewingTime state ∧ 0 < (advance state).material.reserve ∧
      (advance state).material.energy+(advance state).material.reserve = state.material.energy+state.material.reserve :=
  ⟨dyadic_time_positive _,(advance state).ready.budget,
    (pulse_paid state.material _ _ (advance_actual state)).2.2.2⟩

end
end CPS1AddressedBondRenewal
