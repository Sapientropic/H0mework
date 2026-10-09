import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedBondRenewal.Geometry

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1AddressedBondRenewal
noncomputable section
open CPS1Deformation CPS1AddressedBondResponse CPS1AddressedTransfer CPS1AddressedRenewal
open scoped Topology
variable {frame : CPS1Recycling.Frame}

theorem renewed_bridge_site (state : Material frame) (time : ℝ) :
    selectBridge? (renewedMaterial state time).reference = selectBridge? state.reference := rfl

def RenewingResponse (state : Material frame) (site : BridgeSite state.reference)
    (degree : CPS1AddressedBondResponse.Generic.Degree) (time : ℝ) : Prop :=
  ∃ pulse : CPS1ElectronicSource.ElectronicPulse,
    state.pulse? time = .ok (renewedMaterial state time,pulse) ∧
      CPS1PositivePulse.PulseReady (renewedMaterial state time) ∧
      normalize? state.reference (state.movedPositions time) (state.transportedOccupation time) =
        .ok (seedOccupation state time) ∧
      0 < responseFlux state site.phosphate.nuclear 0 * transferredPopulation state site.phosphate.nuclear time ∧
      responseFlux (renewedMaterial state time) site.phosphate.nuclear 0 ≠ 0 ∧
      0 < (distancePolynomial state site).coefficient degree *
        (squaredDistance (state.movedPositions time) site-squaredDistance state.positions site) ∧
      relativeVelocity (renewedMaterial state time) site ≠ 0 ∧
      ∃ nextDegree, (distancePolynomial (renewedMaterial state time) site).leading? = some nextDegree

theorem bridge_response_eventually_renewing (state : Material frame)
    (ready : CPS1PositivePulse.PulseReady state) (site : BridgeSite state.reference)
    (active : responseFlux state site.phosphate.nuclear 0 ≠ 0)
    (degree : CPS1AddressedBondResponse.Generic.Degree)
    (generated : (distancePolynomial state site).leading? = some degree) :
    ∀ᶠ time in 𝓝 (0 : ℝ), 0 < time → RenewingResponse state site degree time := by
  filter_upwards [transfer_eventually_renewing state ready site.phosphate.nuclear active,
    distance_eventually_signed state site degree generated,
    renewed_velocity_eventually_nonzero state site degree generated] with time electronic distance velocity
  intro positive
  obtain ⟨pulse,actual,nextReady,normalized,signed,nextActive⟩ := electronic positive
  exact ⟨pulse,actual,nextReady,normalized,signed,nextActive,distance positive,velocity positive,
    velocity_generates_leading (renewedMaterial state time) site (velocity positive)⟩

end
end CPS1AddressedBondRenewal
