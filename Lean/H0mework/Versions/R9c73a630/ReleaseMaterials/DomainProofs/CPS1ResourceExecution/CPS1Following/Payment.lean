import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Pulse

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Following
noncomputable section
open CPS1ElectronicSource
variable {frame : CPS1Recycling.Frame}

theorem pulse_paid (state : CPS1ElectronicSource.State frame) (time : ℝ)
    (next : CPS1ElectronicSource.State frame × ElectronicPulse) (actual : pulse? state time = .ok next) :
    0 ≤ next.1.reserve ∧ energy next.1+next.1.reserve = energy state+state.reserve := by
  classical
  unfold pulse? at actual
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
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  rename_i affordable
  constructor
  · exact sub_nonneg.mpr (not_lt.mp affordable)
  · rw [energy_currentPrice]
    change _+(state.reserve-(_-energy state)) = energy state+state.reserve
    ring

theorem pulse_source (state : CPS1ElectronicSource.State frame) (time : ℝ)
    (next : CPS1ElectronicSource.State frame × ElectronicPulse) (actual : pulse? state time = .ok next) :
    next.1.geometry.originJoint.originBody = state.geometry.originJoint.originBody ∧
      next.1.geometry.originJoint.components = state.geometry.originJoint.components ∧
      next.1.geometry.originJoint.nextOccurrence = state.geometry.originJoint.nextOccurrence ∧
      CPS1EnzymeBath.Joint.particles frame next.1.geometry.originJoint =
        CPS1EnzymeBath.Joint.particles frame state.geometry.originJoint ∧
      CPS1EnzymeBath.Joint.atoms frame next.1.geometry.originJoint =
        CPS1EnzymeBath.Joint.atoms frame state.geometry.originJoint ∧
      CPS1EnzymeBath.Joint.bonds frame next.1.geometry.originJoint =
        CPS1EnzymeBath.Joint.bonds frame state.geometry.originJoint ∧
      CPS1EnzymeBath.Joint.charge frame next.1.geometry.originJoint =
        CPS1EnzymeBath.Joint.charge frame state.geometry.originJoint ∧
      next.1.geometry.originJoint.reserve = next.1.reserve := by
  classical
  unfold pulse? at actual
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
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem pulse_good (state : CPS1ElectronicSource.State frame) (time : ℝ)
    (next : CPS1ElectronicSource.State frame × ElectronicPulse) (actual : pulse? state time = .ok next)
    (good : CPS1ElectronicEvolution.Consumer.Good state) : CPS1ElectronicEvolution.Consumer.Good next.1 := by
  classical
  unfold pulse? at actual
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
  split at actual <;> try cases actual
  try dsimp only at actual
  split at actual <;> try cases actual
  try dsimp only at actual
  exact (following_occupation_gram _ _ _).trans good

theorem pulse_grounded (state : CPS1ElectronicSource.State frame) (time : ℝ)
    (next : CPS1ElectronicSource.State frame × ElectronicPulse) (actual : pulse? state time = .ok next) :
    CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame state.geometry.originJoint)
      state.geometry.originJoint.rows = .ok state.geometry.nodes ∧
      CPS1AtomicDynamics.Body.ready state.geometry.nodes ∧ 0 < massTotal state := by
  classical
  unfold pulse? at actual
  split at actual <;> try cases actual
  split at actual <;> try cases actual
  split at actual <;> try cases actual
  rename_i nodes gathered
  split at actual <;> try cases actual
  rename_i matched
  split at actual <;> try cases actual
  rename_i ready
  split at actual <;> try cases actual
  rename_i positive
  have same : nodes = state.geometry.nodes := not_ne_iff.mp matched
  exact ⟨by simpa only [same] using gathered,by simpa only [same] using not_not.mp ready,not_le.mp positive⟩

end
end CPS1Following
