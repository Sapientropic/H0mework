import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Material

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CPS1EnzymeBath.Joint
noncomputable section
open CPS1AtomicDynamics

theorem returned_energy (frame : CPS1Recycling.Frame) (state next : State frame)
    (dt : ℝ) (pulse : Body.Pulse) (paid : pulse? frame state dt = .ok (next,pulse)) :
    next.originBody = state.originBody ∧ next.components = state.components ∧
    next.nextOccurrence = state.nextOccurrence ∧
    pulse.after = pulse.before.map (fun node => Body.kick node pulse.before dt) ∧
    pulse.difference = Body.energy pulse.after-Body.energy pulse.before ∧
    pulse.returned = next.reserve ∧ 0 ≤ next.reserve ∧
    Body.energy pulse.after+next.reserve = Body.energy pulse.before+state.reserve ∧
    (pulse.after.map Body.Node.particle = pulse.before.map Body.Node.particle) ∧
    (∀ node ∈ pulse.before, 0 < node.row.inertia) := by
  unfold pulse? at paid
  split at paid <;> try contradiction
  split at paid <;> try contradiction
  split at paid <;> try contradiction
  rename_i nodes gathered
  split at paid <;> try contradiction
  dsimp only at paid
  split at paid <;> try contradiction
  split at paid <;> try contradiction
  have same := Except.ok.inj paid
  cases same
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_,Body.pulse_energy nodes dt state.reserve,?_,?_⟩
  · dsimp only
    rename_i enough
    exact sub_nonneg.mpr (le_of_not_gt enough)
  · simp only [List.map_map,Function.comp_def]
    exact List.map_congr_left (fun node _ => (Body.kick_source node nodes dt).1)
  · intro node member
    exact (Body.gather_source _ _ _ gathered).2 node member |>.1


theorem joint_field (frame : CPS1Recycling.Frame) (state next : State frame)
    (dt : ℝ) (pulse : Body.Pulse) (paid : pulse? frame state dt = .ok (next,pulse)) :
    ∀ direction : Charged.Address → Coulomb.Point,
      HasDerivAt (fun time => Body.potential (pulse.before.map (Field.perturb direction time)))
        (-(pulse.before.map (fun node => inner ℝ (Body.force node pulse.before)
          (direction node.particle.address))).sum) 0 := by
  unfold pulse? at paid
  split at paid <;> try contradiction
  split at paid <;> try contradiction
  split at paid <;> try contradiction
  rename_i nodes gathered
  split at paid <;> try contradiction
  rename_i ready
  dsimp only at paid
  split at paid <;> try contradiction
  split at paid <;> try contradiction
  have same := Except.ok.inj paid
  cases same
  have source := (Body.gather_source _ _ _ gathered).1
  have addresses := congrArg (List.map Charged.Particle.address) source
  have unique : ((particles frame state).map Charged.Particle.address).Nodup := particle_unique frame state
  rw [← addresses] at unique
  intro direction
  apply Field.potential_line_derivative nodes
  · simpa only [List.map_map,Function.comp_def] using unique
  · exact not_not.mp ready

end
end CPS1EnzymeBath.Joint
