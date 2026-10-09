import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Body
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Unique

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CPS1AtomicDynamics.Body
noncomputable section

theorem gather_cons (particle : Charged.Particle) (rest : List Charged.Particle)
    (rows : List (Charged.Address × Row)) :
    gather (particle :: rest) rows =
      match row? rows particle.address with
      | none => .error (.missingRow particle.address)
      | some row => if row.inertia ≤ 0 then .error (.nonpositiveInertia particle.address)
        else match gather rest rows with
        | .error failure => .error failure
        | .ok remainder => .ok (⟨particle,row⟩ :: remainder) := rfl

theorem gather_source (particles : List Charged.Particle) (rows : List (Charged.Address × Row))
    (nodes : List Node) (paid : gather particles rows = .ok nodes) :
    nodes.map Node.particle = particles ∧
      (∀ node ∈ nodes, 0 < node.row.inertia ∧ row? rows node.particle.address = some node.row) := by
  induction particles generalizing nodes with
  | nil =>
    simp only [gather,Except.ok.injEq] at paid
    subst nodes
    exact ⟨rfl,by simp⟩
  | cons particle rest ih =>
    cases known : row? rows particle.address with
    | none => simp [gather_cons,known] at paid
    | some row =>
      by_cases bad : row.inertia ≤ 0
      · simp [gather_cons,known,bad] at paid
      · cases remainder : gather rest rows with
        | error failure => simp [gather_cons,known,bad,remainder] at paid
        | ok tail =>
          have same : Node.mk particle row :: tail = nodes := by
            simpa only [gather_cons,known,if_neg bad,remainder,Except.ok.injEq] using paid
          subst nodes
          have generated := ih tail remainder
          refine ⟨by simp only [List.map_cons,generated.1],?_⟩
          intro node member
          rcases List.mem_cons.mp member with first | remaining
          · subst node
            exact ⟨lt_of_not_ge bad,known⟩
          · exact generated.2 node remaining

theorem gather_unique (frame : CPS1Recycling.Frame) (state : State frame) (nodes : List Node)
    (paid : gather (particles frame state) state.rows = .ok nodes) :
    (nodes.map (fun node => node.particle.address)).Nodup := by
  have source := (gather_source _ _ _ paid).1
  have addresses := congrArg (List.map Charged.Particle.address) source
  have unique : ((particles frame state).map Charged.Particle.address).Nodup :=
    Charged.particles_unique (graph frame state)
  rw [← addresses] at unique
  simpa only [List.map_map,Function.comp_def] using unique

theorem returned_energy (frame : CPS1Recycling.Frame) (state next : State frame)
    (dt : ℝ) (pulse : Pulse) (paid : pulse? frame state dt = .ok (next,pulse)) :
    next.source = state.source ∧
    pulse.after = pulse.before.map (fun node => kick node pulse.before dt) ∧
    pulse.difference = energy pulse.after-energy pulse.before ∧
    pulse.returned = next.reserve ∧ 0 ≤ next.reserve ∧
    energy pulse.after+next.reserve = energy pulse.before+state.reserve ∧
    (pulse.after.map Node.particle = pulse.before.map Node.particle) ∧
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
  refine ⟨rfl,rfl,rfl,rfl,?_,pulse_energy nodes dt state.reserve,?_,?_⟩
  · dsimp only
    rename_i enough
    exact sub_nonneg.mpr (le_of_not_gt enough)
  · simp only [List.map_map,Function.comp_def]
    exact List.map_congr_left (fun node _ => (kick_source node nodes dt).1)
  · intro node member
    exact (gather_source _ _ _ gathered).2 node member |>.1

end
end CPS1AtomicDynamics.Body
