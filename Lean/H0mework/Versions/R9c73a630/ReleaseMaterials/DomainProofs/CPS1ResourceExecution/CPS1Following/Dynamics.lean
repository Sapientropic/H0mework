import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Payment

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Following
noncomputable section
open CPS1ElectronicSource
open scoped BigOperators InnerProductSpace
variable {frame : CPS1Recycling.Frame}

theorem pulse_node_rows (state : CPS1ElectronicSource.State frame) (time : ℝ)
    (next : CPS1ElectronicSource.State frame × ElectronicPulse) (actual : pulse? state time = .ok next) :
    next.1.geometry.nodes = CPS1QuantumNuclear.nextNodes state (nuclearForce state) time ∧
      next.1.geometry.originJoint.rows =
        (CPS1QuantumNuclear.nextNodes state (nuclearForce state) time).map
          (fun node => (node.particle.address,node.row)) := by
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
  exact ⟨rfl,rfl⟩

theorem pulse_gather (state : CPS1ElectronicSource.State frame) (time : ℝ)
    (next : CPS1ElectronicSource.State frame × ElectronicPulse) (actual : pulse? state time = .ok next) :
    CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame next.1.geometry.originJoint)
      next.1.geometry.originJoint.rows = .ok next.1.geometry.nodes := by
  have generated := pulse_node_rows state time next actual
  have grounded := pulse_grounded state time next actual
  have source := pulse_source state time next actual
  rw [generated.1,generated.2,source.2.2.2.1]
  exact moved_gather state (nuclearForce state) time grounded.1

theorem pulse_row_momentum (state : CPS1ElectronicSource.State frame) (time : ℝ)
    (next : CPS1ElectronicSource.State frame × ElectronicPulse) (actual : pulse? state time = .ok next) :
    (next.1.geometry.nodes.map (fun node => node.row.momentum)).sum =
      (state.geometry.nodes.map (fun node => node.row.momentum)).sum := by
  rw [(pulse_node_rows state time next actual).1]
  exact whole_row_momentum state time (pulse_grounded state time next actual).2.2

private theorem gathered_nuclear_unique (state : CPS1ElectronicSource.State frame)
    (gathered : CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame state.geometry.originJoint)
      state.geometry.originJoint.rows = .ok state.geometry.nodes) :
    (state.geometry.nuclei.map (fun node => node.particle.address)).Nodup := by
  have source := CPS1AtomicDynamics.Body.gather_source _ _ _ gathered
  have unique := CPS1AtomicDynamics.Charged.particles_unique
    (CPS1EnzymeBath.Joint.descriptorGraph frame state.geometry.originJoint)
  have addresses := congrArg (List.map CPS1AtomicDynamics.Charged.Particle.address) source.1
  change ((CPS1EnzymeBath.Joint.particles frame state.geometry.originJoint).map
    CPS1AtomicDynamics.Charged.Particle.address).Nodup at unique
  rw [← addresses] at unique
  have original : (state.geometry.nodes.map (fun node => node.particle.address)).Nodup := by
    simpa only [List.map_map,Function.comp_def] using unique
  exact List.pairwise_map.mpr (List.Pairwise.filter isNucleus (List.pairwise_map.mp original))

theorem pulse_lab_energy_line (state : CPS1ElectronicSource.State frame) (time : ℝ)
    (next : CPS1ElectronicSource.State frame × ElectronicPulse) (actual : pulse? state time = .ok next)
    (direction : CPS1AtomicDynamics.Charged.Address → BodyPoint) :
    HasDerivAt (fun parameter : ℝ => energy (labLine state direction parameter))
      (-(state.geometry.nuclei.map (fun node => inner ℝ (nuclearForce state node)
        (direction node.particle.address))).sum) 0 := by
  have grounded := pulse_grounded state time next actual
  exact following_lab_energy_line state (gathered_nuclear_unique state grounded.1)
    (List.Pairwise.filter isNucleus grounded.2.1) direction

theorem pulse_nuclei (state : CPS1ElectronicSource.State frame) (time : ℝ)
    (next : CPS1ElectronicSource.State frame × ElectronicPulse) (actual : pulse? state time = .ok next) :
    next.1.geometry.nuclei = state.geometry.nuclei.map (fun node =>
      CPS1QuantumNuclear.moveNucleus node (nuclearForce state node) time) := by
  change next.1.geometry.nodes.filter isNucleus = _
  rw [(pulse_node_rows state time next actual).1]
  exact moved_nuclei state (nuclearForce state) time

theorem pulse_mass (state : CPS1ElectronicSource.State frame) (time : ℝ)
    (next : CPS1ElectronicSource.State frame × ElectronicPulse) (actual : pulse? state time = .ok next) :
    massTotal next.1 = massTotal state := by
  unfold massTotal
  rw [pulse_nuclei state time next actual]
  simp only [List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro node _
  exact (CPS1QuantumNuclear.nuclear_whole node (nuclearForce state node) time).2

private theorem momentum_scale_sum {A : Type} (items : List A) (value : A → BodyPoint) (scalar : ℝ) :
    (items.map (fun item => scalar • value item)).sum = scalar • (items.map value).sum := by
  induction items with
  | nil => simp only [List.map_nil,List.sum_nil,smul_zero]
  | cons item rest ih => simp only [List.map_cons,List.sum_cons,ih,smul_add]

theorem pulse_centre (state : CPS1ElectronicSource.State frame) (time : ℝ)
    (next : CPS1ElectronicSource.State frame × ElectronicPulse) (actual : pulse? state time = .ok next) :
    centre next.1 = centre state+time • ((massTotal state)⁻¹ •
      (state.geometry.nuclei.map (fun node => node.row.momentum)).sum) := by
  have grounded := pulse_grounded state time next actual
  have source := CPS1AtomicDynamics.Body.gather_source _ _ _ grounded.1
  have motion : (state.geometry.nuclei.map (fun node =>
      (CPS1QuantumNuclear.moveNucleus node (nuclearForce state node) time).row.inertia •
        (CPS1QuantumNuclear.moveNucleus node (nuclearForce state node) time).row.position)) =
      state.geometry.nuclei.map (fun node => node.row.inertia • node.row.position+
        time • node.row.momentum+(time^2/2) • nuclearForce state node) := by
    apply List.map_congr_left
    intro node member
    have nucleus := (List.mem_filter.mp member).2
    have positive := (source.2 node (List.mem_filter.mp member).1).1
    have drift : node.row.inertia*(time/node.row.inertia) = time := by
      field_simp [ne_of_gt positive]
    have acceleration : node.row.inertia*(time^2/(2*node.row.inertia)) = time^2/2 := by
      field_simp [ne_of_gt positive]
    simp only [CPS1QuantumNuclear.moveNucleus,nucleus,if_true,CPS1QuantumNuclear.kickWith,
      smul_add,smul_smul,drift,acceleration]
  unfold centre
  rw [pulse_mass state time next actual,pulse_nuclei state time next actual]
  simp only [List.map_map,Function.comp_def]
  rw [motion,List.sum_map_add,List.sum_map_add,momentum_scale_sum,momentum_scale_sum,
    total_nuclear_force_zero state grounded.2.2,smul_zero,add_zero,smul_add,smul_comm]

theorem pulse_centre_velocity (state : CPS1ElectronicSource.State frame) (time : ℝ)
    (next : CPS1ElectronicSource.State frame × ElectronicPulse) (actual : pulse? state time = .ok next)
    (nonzero : time ≠ 0) :
    centreVelocity state next.1 time = fun axis =>
      ((massTotal state)⁻¹ • (state.geometry.nuclei.map (fun node => node.row.momentum)).sum) axis := by
  funext axis
  unfold centreVelocity
  rw [pulse_centre state time next actual]
  change ((centre state axis+time*((massTotal state)⁻¹ •
    (state.geometry.nuclei.map (fun node => node.row.momentum)).sum) axis)-centre state axis)/time = _
  field_simp [nonzero]
  ring

end
end CPS1Following
