import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Closure
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.NoGuard
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Field

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CPS1AtomicDynamics
noncomputable section

private theorem sum_scaled {A : Type} (nodes : List A) (field : A → Coulomb.Point) (dt : ℝ) :
    (nodes.map (fun node => dt • field node)).sum = dt • (nodes.map field).sum := by
  induction nodes with
  | nil => simp only [List.map_nil,List.sum_nil,smul_zero]
  | cons node rest ih => simp only [List.map_cons,List.sum_cons,ih,smul_add]

theorem joint_momentum (nodes : List Body.Node) (dt : ℝ) :
    ((nodes.map (fun node => Body.kick node nodes dt)).map (fun node => node.row.momentum)).sum =
      (nodes.map (fun node => node.row.momentum)).sum := by
  simp only [List.map_map,Function.comp_def,Body.kick]
  rw [List.sum_map_add,sum_scaled,Field.total_force_zero,smul_zero,add_zero]

theorem actual_field (frame : CPS1Recycling.Frame) (state next : Body.State frame)
    (dt : ℝ) (pulse : Body.Pulse) (paid : Body.pulse? frame state dt = .ok (next,pulse)) :
    ∀ direction : Charged.Address → Coulomb.Point,
      HasDerivAt (fun time => Body.potential (pulse.before.map (Field.perturb direction time)))
        (-(pulse.before.map (fun node => inner ℝ (Body.force node pulse.before)
          (direction node.particle.address))).sum) 0 := by
  unfold Body.pulse? at paid
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
  intro direction
  exact Field.potential_line_derivative nodes (Body.gather_unique frame state nodes gathered)
    (not_not.mp ready) direction

structure DynamicsContract : Prop where
  actualSource : type_of% Actual.actual_start
  sourceCharge : type_of% Charged.generated_charge
  sourceAddresses : type_of% Charged.particles_unique
  coulombForce : type_of% actual_field
  wholeCarrier : type_of% Body.pulse_whole_carrier
  jointMomentum : type_of% joint_momentum
  sourceWork : type_of% Body.kick_work
  energyPayment : type_of% Body.returned_energy
  actualInventory : type_of% actual_pulse
  inventoryBalance : type_of% full_inventory
  cut : type_of% source_cut
  guardCut : type_of% Source.guard_cut
  noGuard : type_of% Source.advance_no_guard
  continuationSource : type_of% Source.continuation_source

theorem sourceGeneratedDynamics : DynamicsContract :=
  ⟨Actual.actual_start,Charged.generated_charge,Charged.particles_unique,actual_field,
    Body.pulse_whole_carrier,joint_momentum,Body.kick_work,Body.returned_energy,
    actual_pulse,full_inventory,source_cut,Source.guard_cut,Source.advance_no_guard,
    Source.continuation_source⟩

end
end CPS1AtomicDynamics
