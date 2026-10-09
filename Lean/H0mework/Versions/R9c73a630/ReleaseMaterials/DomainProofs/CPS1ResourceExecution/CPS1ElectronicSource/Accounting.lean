import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.State

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1ElectronicSource
noncomputable section
open scoped Matrix
variable {frame : CPS1Recycling.Frame}

theorem capture_price_actual (geometry : Geometry frame) :
    capturePrice geometry =
      electronicEnergy geometry (initialDensity geometry)-geometry.classicalElectronicEnergy :=
  actual_energy_replacement geometry (initialDensity geometry)

theorem capture_paid (geometry : Geometry frame) (next : State frame)
    (actual : State.fromGeometry? geometry = .ok next) :
    next.geometry = geometry ∧ 0 ≤ next.reserve ∧
      next.energy + next.reserve = geometry.classicalEnergy + geometry.originJoint.reserve := by
  classical
  unfold State.fromGeometry? at actual
  by_cases negative : geometry.originJoint.reserve < 0
  · simp only [if_pos negative] at actual
    cases actual
  · by_cases shortage : geometry.originJoint.reserve < capturePrice geometry
    · simp only [if_neg negative,if_pos shortage] at actual
      cases actual
    · simp only [if_neg negative,if_neg shortage,Except.ok.injEq] at actual
      subst next
      refine ⟨rfl,sub_nonneg.mpr (not_lt.mp shortage),?_⟩
      change totalEnergy geometry (initialDensity geometry) +
        (geometry.originJoint.reserve-capturePrice geometry) =
          geometry.classicalEnergy+geometry.originJoint.reserve
      unfold capturePrice
      ring

theorem pulse_paid (state : State frame) (time : ℝ) (next : State frame)
    (actual : State.pulse? state time = .ok next) :
    next.geometry = state.geometry ∧ 0 ≤ next.reserve ∧
      next.energy + next.reserve = state.energy + state.reserve := by
  classical
  let nextOccupied : Matrix (SpinIndex state.geometry) (ElectronIndex state.geometry) ℂ :=
    CPS1ElectronicEvolution.occupiedUpdate state.hamiltonian (time/2) state.occupied
  let nextDensity : Matrix (SpinIndex state.geometry) (SpinIndex state.geometry) ℂ :=
    nextOccupied * nextOccupied.conjTranspose
  let price : ℝ := totalEnergy state.geometry nextDensity-state.energy
  change ((if time < 0 then .error .negativeTime
    else if state.reserve < 0 then .error .negativeReserve
    else if state.reserve < price then .error .energyShortage
    else .ok ⟨state.geometry,nextOccupied,state.reserve-price⟩) : Except Failure (State frame)) = .ok next at actual
  by_cases negativeTime : time < 0
  · simp only [if_pos negativeTime] at actual
    cases actual
  · by_cases negativeReserve : state.reserve < 0
    · simp only [if_neg negativeTime,if_pos negativeReserve] at actual
      cases actual
    · by_cases shortage : state.reserve < price
      · simp only [if_neg negativeTime,if_neg negativeReserve,if_pos shortage] at actual
        cases actual
      · simp only [if_neg negativeTime,if_neg negativeReserve,if_neg shortage,Except.ok.injEq] at actual
        subst next
        refine ⟨rfl,sub_nonneg.mpr (not_lt.mp shortage),?_⟩
        change totalEnergy state.geometry nextDensity + (state.reserve-price) = state.energy+state.reserve
        dsimp only [price]
        ring

theorem deposit_paid (state : State frame) (amount : ℝ) (next : State frame)
    (actual : State.deposit? state amount = .ok next) :
    next.energy = state.energy ∧ next.reserve = state.reserve+amount := by
  classical
  unfold State.deposit? at actual
  by_cases negative : amount < 0
  · simp only [if_pos negative] at actual
    cases actual
  · simp only [if_neg negative,Except.ok.injEq] at actual
    subst next
    exact ⟨rfl,rfl⟩

end
end CPS1ElectronicSource
