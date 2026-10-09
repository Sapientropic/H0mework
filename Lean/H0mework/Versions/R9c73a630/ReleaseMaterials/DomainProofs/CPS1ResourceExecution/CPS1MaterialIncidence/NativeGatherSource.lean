import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualRootPaidDisposition

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeGatherConsumers
noncomputable section
open CPS1AtomicDynamics CPS1AtomicSource CPS1SameEventFunction CPS1PhosphorylExchange CPS1BiologicalUpdate CPS1LiveEditing
open NativePaidEvent NativePaidPositive NativeAmmoniaDynamics NativeCarbamoyl

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}

theorem native_pose_gather (state : PostState current) :
    Body.gather (commonParticles before.packet.source raw.fuel)
      (state.pose.map (fun node => (node.particle.address,node.row))) = .ok state.pose := by
  have particles := state.particles.trans (current_particles_source source current)
  have addresses := congrArg (List.map Charged.Particle.address) particles
  simp only [List.map_map,Function.comp_def] at addresses
  have unique : (state.pose.map (fun node => node.particle.address)).Nodup := by
    rw [addresses]
    exact common_addresses_unique _ _
  exact Body.gather_exact _ _ particles _ (Body.row_at_source _ unique) state.inertia

def particleMass (node : Body.Node) := (node.particle,node.row.inertia)

theorem current_particle_mass :
    current.nodes.map particleMass = source.nodes.map particleMass := by
  rw [current.nodesActual,List.map_map]
  apply List.map_congr_left
  intro node _held
  cases address : node.particle.address <;>
    simp only [Function.comp_def,CPS1PhosphorylExchange.sourceKick,address,particleMass]

theorem initial_particle_mass (origin : AmmoniaSource source current) :
    (initialState origin).pose.map particleMass = source.nodes.map particleMass := by
  have actual := congrArg Prod.fst origin.material.whole
  change origin.material.event.after.whole.1 = current at actual
  change origin.material.event.after.whole.1.nodes.map particleMass = _
  rw [actual]
  exact current_particle_mass

theorem end_particle_mass (state : PostState current) :
    (endPose state).map particleMass = state.pose.map particleMass := by
  rw [endPose,List.map_map]
  apply List.map_congr_left
  intro node _held
  cases address : node.particle.address <;>
    simp only [Function.comp_def,fullKick,address,particleMass]

theorem dynamics_particle_mass (dynamics : SourceGeneratedDynamics source current) :
    dynamics.result.next.pose.map particleMass = source.nodes.map particleMass := by
  have initial := initial_particle_mass dynamics.origin
  cases result : dynamics.result with
  | positive event => exact (end_particle_mass _).trans initial
  | wrongDirection event failed => exact (end_particle_mass _).trans initial
  | nondifferentiable failed => exact initial
  | collision smooth failed => exact initial
  | energyShortage smooth ready failed => exact initial

theorem paid_particle_mass (paid : SourceGeneratedPaidReturn source current) :
    paid.physical.pose.map particleMass = source.nodes.map particleMass := by
  rw [paid.physicalActual]
  exact dynamics_particle_mass paid.parent.products.dynamics

theorem paid_uniform_electrons (paid : SourceGeneratedPaidReturn source current)
    (node : Body.Node) (held : node ∈ paid.physical.pose) :
    match node.particle.address with
    | .nucleus _ => True
    | .electron .. => node.row.inertia = source.electronInertia := by
  have original : particleMass node ∈ source.nodes.map particleMass :=
    paid_particle_mass paid ▸ List.mem_map_of_mem held
  obtain ⟨old,oldHeld,identity⟩ := List.mem_map.mp original
  have particle := congrArg Prod.fst identity
  have mass := congrArg Prod.snd identity
  change old.particle = node.particle at particle
  change old.row.inertia = node.row.inertia at mass
  have uniform := source.uniformElectrons old oldHeld
  rw [particle,mass] at uniform
  exact uniform

theorem cp_ordinals (products : SourceGeneratedCarbamoyl source current) :
    ((cpSourceAtoms products.serial).map (fun atom => cpIndex atom.origin)).Perm (List.range 10) := by
  change ([6,8,9,4,2,0,3,5,7,1] : List Nat).Perm (List.range 10)
  decide +kernel

variable {origin : CPS1ReactiveNuclear.SourceCursor frame} {water : Nat} {material : List RawSupply}
  {path : CPS1Recycling.SplitSite} {events : List CPS1Recycling.RawEvent}
  {feed : List CPS1Recycling.RawMaterial} {physical : PhysicalRaw} {depth : Nat}

theorem actual_chain_owner
    (whole : CPS1LiveEditing.WholeRun origin water material path events feed physical depth)
    (supply : ContinuationRaw)
    (profile : supply.recycling = [] ∧ supply.recycleFeed = [] ∧ supply.physical = noPhysicalSupply)
    (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
    (repaired : repairWhole whole supply = .repaired receipt)
    (original : Classical.Source receipt.nextBody.current.2) :
    original.owned = initialOwner receipt.nextBody.current.1 := by
  obtain ⟨_tail,_head,_pending,_cut,unique,live⟩ :=
    repaired_source_ready_of_profile whole supply profile receipt repaired
  have generated : Classical.ownedChain receipt.nextBody.current.2 =
      some (initialOwner receipt.nextBody.current.1) := by
    unfold Classical.ownedChain
    rw [live,List.filterMap_map]
    change (receipt.nextBody.current.2.native.current.old.current.stock.filterMap Classical.ownedDeformed?).head? = _
    rw [unique]
    rfl
  exact Option.some.inj (original.ownership.symm.trans generated)

end
end CPS1MaterialIncidence.NativeGatherConsumers
