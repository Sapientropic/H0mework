import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.State

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1MolecularFrame
noncomputable section
open CPS1ElectronicSource
open scoped Matrix InnerProductSpace
variable {frame : CPS1Recycling.Frame}

theorem reprice_energy (state : Material frame) (reserve : ℝ) :
    (state.reprice reserve).energy = state.energy := rfl

theorem reprice_reserve (state : Material frame) (reserve : ℝ) :
    (state.reprice reserve).reserve = reserve := rfl

theorem reprice_good (state : Material frame) (reserve : ℝ) (generated : Good state) :
    Good (state.reprice reserve) := generated

theorem reprice_source (state : Material frame) (reserve : ℝ) :
    (state.reprice reserve).reference.geometry.nodes = state.reference.geometry.nodes ∧
    (state.reprice reserve).currentJoint.originBody = state.currentJoint.originBody ∧
    (state.reprice reserve).currentJoint.components = state.currentJoint.components ∧
    (state.reprice reserve).currentJoint.nextOccurrence = state.currentJoint.nextOccurrence ∧
    (state.reprice reserve).currentJoint.reserve = (state.reprice reserve).reserve :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem adopt_outcome (reference : CPS1ElectronicSource.State frame) (next : Material frame)
    (actual : adopt? reference = .ok next) :
    ∃ enough : electronCount frame reference.geometry.originJoint ≤ FiniteNormed.rank (𝕜 := ℂ) (rawField reference),
      let generated : Material frame := ⟨reference,initialOccupation reference enough,reference.reserve⟩
      next = generated.reprice (reference.reserve-(generated.energy-CPS1Following.energy reference)) ∧
      0 ≤ reference.reserve ∧ generated.energy-CPS1Following.energy reference ≤ reference.reserve ∧
      CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame reference.geometry.originJoint)
        reference.geometry.originJoint.rows = .ok reference.geometry.nodes ∧
      CPS1AtomicDynamics.Body.ready reference.geometry.nodes := by
  classical
  unfold adopt? at actual
  split at actual <;> try contradiction
  try dsimp only at actual
  split at actual <;> try contradiction
  try dsimp only at actual
  rename_i nodes gathered
  split at actual <;> try contradiction
  try dsimp only at actual
  rename_i matched
  split at actual <;> try contradiction
  try dsimp only at actual
  rename_i ready
  split at actual <;> try contradiction
  try dsimp only at actual
  rename_i enough
  split at actual <;> try contradiction
  rename_i affordable
  refine ⟨enough,(Except.ok.inj actual).symm,?_,le_of_not_gt affordable,?_,?_⟩
  · exact le_of_not_gt ‹¬ reference.reserve < 0›
  · exact gathered.trans (congrArg Except.ok (not_ne_iff.mp matched))
  · simpa only [not_ne_iff.mp matched] using (not_not.mp ready)

theorem adopt_good (reference : CPS1ElectronicSource.State frame) (next : Material frame)
    (actual : adopt? reference = .ok next) : Good next := by
  obtain ⟨enough,same,_,_,_,_⟩ := adopt_outcome reference next actual
  rw [same]
  exact reprice_good _ _ (initial_occupation_gram reference enough)

theorem adopt_paid (reference : CPS1ElectronicSource.State frame) (next : Material frame)
    (actual : adopt? reference = .ok next) :
    0 ≤ reference.reserve ∧ 0 ≤ next.reserve ∧
      next.energy + next.reserve = CPS1Following.energy reference + reference.reserve := by
  obtain ⟨enough,same,nonnegative,affordable,_,_⟩ := adopt_outcome reference next actual
  rw [same,reprice_energy,reprice_reserve]
  exact ⟨nonnegative,sub_nonneg.mpr affordable,by ring⟩

theorem adopt_grounded (reference : CPS1ElectronicSource.State frame) (next : Material frame)
    (actual : adopt? reference = .ok next) :
    CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame reference.geometry.originJoint)
      reference.geometry.originJoint.rows = .ok reference.geometry.nodes ∧
    CPS1AtomicDynamics.Body.ready reference.geometry.nodes ∧
    electronCount frame reference.geometry.originJoint ≤ FiniteNormed.rank (𝕜 := ℂ) (rawField reference) := by
  obtain ⟨enough,_,_,_,gathered,ready⟩ := adopt_outcome reference next actual
  exact ⟨gathered,ready,enough⟩

theorem adopted_source (reference : CPS1ElectronicSource.State frame) (next : Material frame)
    (actual : adopt? reference = .ok next) :
    next.reference.geometry.nodes = reference.geometry.nodes ∧
    next.currentJoint.originBody = reference.geometry.originJoint.originBody ∧
    next.currentJoint.components = reference.geometry.originJoint.components ∧
    next.currentJoint.nextOccurrence = reference.geometry.originJoint.nextOccurrence ∧
    next.currentJoint.reserve = next.reserve := by
  obtain ⟨_,same,_,_,_,_⟩ := adopt_outcome reference next actual
  rw [same]
  exact reprice_source _ _

theorem pulse_outcome (state next : Material frame) (time : ℝ) (actual : state.pulse? time = .ok next) :
    let generated : Material frame :=
      ⟨state.reference,CPS1ElectronicEvolution.occupiedUpdate state.hamiltonian (time/2) state.occupied,state.reserve⟩
    next = generated.reprice (state.reserve-(generated.energy-state.energy)) ∧
      0 ≤ time ∧ 0 ≤ state.reserve ∧ generated.energy-state.energy ≤ state.reserve := by
  unfold Material.pulse? at actual
  split at actual <;> try contradiction
  split at actual <;> try contradiction
  dsimp only at actual
  split at actual <;> try contradiction
  exact ⟨(Except.ok.inj actual).symm,le_of_not_gt ‹¬ time < 0›,
    le_of_not_gt ‹¬ state.reserve < 0›,le_of_not_gt ‹¬ state.reserve < _›⟩

theorem pulse_good (state next : Material frame) (time : ℝ)
    (actual : state.pulse? time = .ok next) (generated : Good state) : Good next := by
  obtain ⟨same,_,_,_⟩ := pulse_outcome state next time actual
  rw [same]
  apply reprice_good
  exact (CPS1ElectronicEvolution.occupied_gram state.hamiltonian
    (material_hamiltonian_hermitian state) (time/2) state.occupied).trans generated

theorem pulse_paid (state next : Material frame) (time : ℝ) (actual : state.pulse? time = .ok next) :
    0 ≤ state.reserve ∧ 0 ≤ next.reserve ∧ next.energy + next.reserve = state.energy + state.reserve := by
  obtain ⟨same,_,nonnegative,affordable⟩ := pulse_outcome state next time actual
  rw [same,reprice_energy,reprice_reserve]
  exact ⟨nonnegative,sub_nonneg.mpr affordable,by ring⟩

theorem pulse_source (state next : Material frame) (time : ℝ) (actual : state.pulse? time = .ok next) :
    next.reference.geometry.nodes = state.reference.geometry.nodes ∧
    next.currentJoint.originBody = state.currentJoint.originBody ∧
    next.currentJoint.components = state.currentJoint.components ∧
    next.currentJoint.nextOccurrence = state.currentJoint.nextOccurrence ∧
    next.currentJoint.reserve = next.reserve := by
  obtain ⟨same,_,_,_⟩ := pulse_outcome state next time actual
  rw [same]
  exact reprice_source _ _

theorem deposit_good (state next : Material frame) (amount : ℝ)
    (actual : state.deposit? amount = .ok next) (generated : Good state) : Good next := by
  unfold Material.deposit? at actual
  split at actual <;> try contradiction
  cases Except.ok.inj actual
  exact reprice_good _ _ generated

end
end CPS1MolecularFrame
