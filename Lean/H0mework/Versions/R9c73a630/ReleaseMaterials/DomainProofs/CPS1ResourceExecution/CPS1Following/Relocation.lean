import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Geometry

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Following
noncomputable section
open CPS1ElectronicSource
variable {frame : CPS1Recycling.Frame}

inductive Failure
  | inherited (failure : CPS1QuantumNuclear.Failure)
  | nonpositiveNuclearMass
  deriving DecidableEq

structure RelocationReceipt where
  beforeEnergy : ℝ
  afterEnergy : ℝ
  beforeReserve : ℝ
  afterReserve : ℝ

/-- This changes the field occurrence, so its full energy difference is paid
before the new carrier can enter the following-field inventory. -/
def relocate? (state : CPS1ElectronicSource.State frame) :
    Except Failure (CPS1ElectronicSource.State frame × RelocationReceipt) := by
  classical
  exact
    if state.reserve < 0 then .error (.inherited (.inherited .negativeReserve))
    else match CPS1AtomicDynamics.Body.gather
        (CPS1EnzymeBath.Joint.particles frame state.geometry.originJoint) state.geometry.originJoint.rows with
    | .error failure => .error (.inherited (.inherited (.body failure)))
    | .ok nodes =>
      if nodes ≠ state.geometry.nodes then .error (.inherited .sourceRowsMismatch)
      else if ¬ CPS1AtomicDynamics.Body.ready nodes then .error (.inherited (.inherited (.body .collision)))
      else if massTotal state ≤ 0 then .error .nonpositiveNuclearMass
      else
        let price := energy state-state.energy
        if state.reserve < price then .error (.inherited (.inherited .energyShortage))
        else
          let next := CPS1QuantumNuclear.currentPrice state (state.reserve-price)
          .ok (next,⟨state.energy,energy next,state.reserve,next.reserve⟩)

theorem relocate_grounded (state : CPS1ElectronicSource.State frame)
    (next : CPS1ElectronicSource.State frame × RelocationReceipt) (actual : relocate? state = .ok next) :
    CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame state.geometry.originJoint)
      state.geometry.originJoint.rows = .ok state.geometry.nodes ∧
      CPS1AtomicDynamics.Body.ready state.geometry.nodes ∧ 0 < massTotal state := by
  classical
  unfold relocate? at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  rename_i nodes gathered
  split at actual <;> try cases actual
  try dsimp only at actual
  rename_i matched
  split at actual <;> try cases actual
  try dsimp only at actual
  rename_i ready
  split at actual <;> try cases actual
  try dsimp only at actual
  rename_i positive
  have same : nodes = state.geometry.nodes := not_ne_iff.mp matched
  exact ⟨by simpa only [same] using gathered,by simpa only [same] using not_not.mp ready,not_le.mp positive⟩

theorem relocate_whole (state : CPS1ElectronicSource.State frame)
    (next : CPS1ElectronicSource.State frame × RelocationReceipt) (actual : relocate? state = .ok next) :
    next.1.geometry.nodes = state.geometry.nodes ∧
      next.1.geometry.originJoint.originBody = state.geometry.originJoint.originBody ∧
      next.1.geometry.originJoint.components = state.geometry.originJoint.components ∧
      next.1.geometry.originJoint.rows = state.geometry.originJoint.rows ∧
      HEq next.1.occupied state.occupied ∧ next.1.geometry.originJoint.reserve = next.1.reserve := by
  classical
  unfold relocate? at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  exact ⟨rfl,rfl,rfl,rfl,HEq.rfl,rfl⟩

theorem relocate_paid (state : CPS1ElectronicSource.State frame)
    (next : CPS1ElectronicSource.State frame × RelocationReceipt) (actual : relocate? state = .ok next) :
    0 ≤ next.1.reserve ∧ energy next.1+next.1.reserve = state.energy+state.reserve := by
  classical
  unfold relocate? at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  rename_i affordable
  constructor
  · exact sub_nonneg.mpr (not_lt.mp affordable)
  · rw [energy_currentPrice]
    change energy state+(state.reserve-(energy state-state.energy)) = state.energy+state.reserve
    ring

theorem relocate_good (state : CPS1ElectronicSource.State frame)
    (next : CPS1ElectronicSource.State frame × RelocationReceipt) (actual : relocate? state = .ok next)
    (good : CPS1ElectronicEvolution.Consumer.Good state) : CPS1ElectronicEvolution.Consumer.Good next.1 := by
  classical
  unfold relocate? at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  exact good

def deposit? (state : CPS1ElectronicSource.State frame) (amount : ℝ) :
    Except Failure (CPS1ElectronicSource.State frame) := by
  classical
  exact if amount < 0 then .error (.inherited (.inherited .negativeReserve))
    else .ok (CPS1QuantumNuclear.currentPrice state (state.reserve+amount))

theorem deposit_paid (state : CPS1ElectronicSource.State frame) (amount : ℝ)
    (next : CPS1ElectronicSource.State frame) (actual : deposit? state amount = .ok next) :
    0 ≤ amount ∧ energy next+next.reserve = energy state+state.reserve+amount ∧
      next.geometry.originJoint.reserve = next.reserve := by
  unfold deposit? at actual
  split at actual
  · cases actual
  · rename_i positive
    cases Except.ok.inj actual
    refine ⟨not_lt.mp positive,?_,rfl⟩
    rw [energy_currentPrice]
    change energy state+(state.reserve+amount) = energy state+state.reserve+amount
    ring

theorem deposit_good (state : CPS1ElectronicSource.State frame) (amount : ℝ)
    (next : CPS1ElectronicSource.State frame) (actual : deposit? state amount = .ok next)
    (good : CPS1ElectronicEvolution.Consumer.Good state) : CPS1ElectronicEvolution.Consumer.Good next := by
  unfold deposit? at actual
  split at actual
  · cases actual
  · cases Except.ok.inj actual
    exact good

end
end CPS1Following
