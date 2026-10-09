import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualAmmoniaDynamics

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeResumableProbe
noncomputable section
open CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange
open NativeAmmoniaDynamics

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}

inductive NativePhysicalResult (state : PostState current)
  | paid (event : PaidStep state)
  | nondifferentiable (failed : ¬ FullSmooth state)
  | collision (smooth : FullSmooth state) (failed : ¬ Body.ready (endPose state))
  | energyShortage (smooth : FullSmooth state) (ready : Body.ready (endPose state))
      (failed : ¬ energyPrice state ≤ state.reserve)

def advanceNative (state : PostState current) : NativePhysicalResult state := by
  classical
  exact if smooth : FullSmooth state then
    if ready : Body.ready (endPose state) then
      if budget : energyPrice state ≤ state.reserve then .paid ⟨smooth,ready,budget⟩
      else .energyShortage smooth ready budget
    else .collision smooth ready
  else .nondifferentiable smooth

def NativePhysicalResult.next {state : PostState current} : NativePhysicalResult state → PostState current
  | .paid event => event.after
  | .nondifferentiable _ | .collision _ _ | .energyShortage _ _ _ => refineState state

theorem advance_native_paid (state : PostState current) (smooth : FullSmooth state)
    (ready : Body.ready (endPose state)) (budget : energyPrice state ≤ state.reserve) :
    advanceNative state = .paid ⟨smooth,ready,budget⟩ := by
  classical
  simp only [advanceNative,dif_pos smooth,dif_pos ready,dif_pos budget]

theorem advance_native_nondifferentiable (state : PostState current) (failed : ¬ FullSmooth state) :
    advanceNative state = .nondifferentiable failed := by
  classical
  simp only [advanceNative,dif_neg failed]

theorem advance_native_collision (state : PostState current) (smooth : FullSmooth state)
    (failed : ¬ Body.ready (endPose state)) : advanceNative state = .collision smooth failed := by
  classical
  simp only [advanceNative,dif_pos smooth,dif_neg failed]

theorem advance_native_energy_shortage (state : PostState current) (smooth : FullSmooth state)
    (ready : Body.ready (endPose state)) (failed : ¬ energyPrice state ≤ state.reserve) :
    advanceNative state = .energyShortage smooth ready failed := by
  classical
  simp only [advanceNative,dif_pos smooth,dif_pos ready,dif_neg failed]

theorem native_result_account {state : PostState current} (result : NativePhysicalResult state) :
    result.next.energy + result.next.reserve = state.energy + state.reserve := by
  cases result with
  | paid event => exact paid_account event
  | nondifferentiable _ => rfl
  | collision _ _ => rfl
  | energyShortage _ _ _ => rfl

theorem native_result_fields {state : PostState current} (result : NativePhysicalResult state) :
    CPS1ElectronicEvolution.fields (rawField current) result.next.rawC =
      CPS1ElectronicEvolution.fields (basis current) result.next.occupied := post_fields result.next

theorem native_result_ne {state : PostState current} (result : NativePhysicalResult state) :
    Matrix.trace (result.next.occupied * result.next.occupied.conjTranspose) =
      (electronCount source.nodes : ℂ) := post_electron_number result.next

theorem native_result_particles {state : PostState current} (result : NativePhysicalResult state) :
    result.next.pose.map Body.Node.particle = state.pose.map Body.Node.particle :=
  result.next.particles.trans state.particles.symm

def NativePhysicalUpdate {state : PostState current} (result : NativePhysicalResult state) : Prop :=
  match result with
  | .paid event =>
    result.next = event.after ∧ result.next.index = 0 ∧
      result.next.elapsed = state.elapsed + state.time ∧ result.next.pose = endPose state ∧
      result.next.occupied = endCoordinates state ∧ result.next.reserve = state.reserve - energyPrice state ∧
      result.next.rawC = state.rawC + sourceCoefficient current * (result.next.occupied - state.occupied) ∧
      state.elapsed < result.next.elapsed
  | .nondifferentiable _ | .collision _ _ | .energyShortage _ _ _ =>
    result.next = refineState state ∧ result.next.index = state.index + 1 ∧
      result.next.elapsed = state.elapsed ∧ result.next.pose = state.pose ∧
      result.next.occupied = state.occupied ∧ result.next.rawC = state.rawC ∧
      result.next.energy = state.energy ∧ result.next.reserve = state.reserve ∧ result.next.time = state.time / 2

theorem native_result_update {state : PostState current} (result : NativePhysicalResult state) :
    NativePhysicalUpdate result := by
  cases result with
  | paid event => exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,paid_fullC_increment event,paid_clock event⟩
  | nondifferentiable _ => exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,refinement_time state⟩
  | collision _ _ => exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,refinement_time state⟩
  | energyShortage _ _ _ => exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,refinement_time state⟩

theorem native_result_progress {state : PostState current} (result : NativePhysicalResult state) :
    state.elapsed < result.next.elapsed ∨
      (result.next = refineState state ∧ result.next.index = state.index + 1 ∧
        result.next.elapsed = state.elapsed ∧ result.next.pose = state.pose ∧
        result.next.occupied = state.occupied ∧ result.next.rawC = state.rawC ∧
        result.next.reserve = state.reserve ∧ result.next.time = state.time / 2) := by
  cases result with
  | paid event => exact Or.inl (paid_clock event)
  | nondifferentiable _ => exact Or.inr ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,refinement_time state⟩
  | collision _ _ => exact Or.inr ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,refinement_time state⟩
  | energyShortage _ _ _ => exact Or.inr ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,refinement_time state⟩

private theorem pose_addresses_unique (state : PostState current) :
    (state.pose.map (fun node => node.particle.address)).Nodup := by
  have particles := state.particles.trans (current_particles_source source current)
  have addresses := congrArg (List.map Charged.Particle.address) particles
  simp only [List.map_map,Function.comp_def] at addresses
  rw [addresses]
  exact common_addresses_unique _ _

private theorem pose_slot_bound (state : PostState current) (node : Body.Node) (held : node ∈ state.pose) :
    node.particle.address.slot < source.atoms.length := by
  have particles := state.particles.trans (current_particles_source source current)
  have present : node.particle ∈ commonParticles before.packet.source raw.fuel :=
    particles ▸ List.mem_map_of_mem held
  obtain ⟨row,indexed,member⟩ := List.mem_flatMap.mp present
  rw [Charged.atom_particle_slot (row.1.descriptor,row.2) node.particle member,source.atomSource]
  simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx indexed

private theorem nucleus_complete (state : PostState current) (node : Body.Node)
    (held : node ∈ nucleusNodes state.pose) : ∃ index : AtomSector source, postNucleus state index = node := by
  have member := (List.mem_filter.mp held).1
  let index : AtomSector source := ⟨node.particle.address.slot,pose_slot_bound state node member⟩
  have address : node.particle.address = .nucleus index.val := by
    have nuclear := (List.mem_filter.mp held).2
    cases actual : node.particle.address with
    | nucleus slot =>
      change Charged.Address.nucleus slot = .nucleus node.particle.address.slot
      rw [actual]
      rfl
    | electron slot orbital => simp only [actual,Bool.false_eq_true] at nuclear
  refine ⟨index,?_⟩
  exact List.inj_on_of_nodup_map (pose_addresses_unique state)
    (post_nucleus_actual state index).1 member ((post_nucleus_actual state index).2.trans address.symm)

/-- Nuclear rows and raw field directions share the original source identities
while the resumable pose and full occupation remain separate state fields. -/
structure NativeOriginFace (state : PostState current) where
  nucleus : AtomSector source → Body.Node
  nucleusActual : ∀ index, nucleus index ∈ state.pose ∧
    (nucleus index).particle.address = .nucleus index.val
  nuclearComplete : ∀ node ∈ nucleusNodes state.pose, ∃ index, nucleus index = node
  nuclearInjective : Function.Injective nucleus
  nuclearOrigin : AtomSector source → AtomOrigin cursor
  originActual : nuclearOrigin = originAt source
  originUnique : Function.Injective nuclearOrigin
  primitiveOrigin : RawIndex current → FieldOrigin cursor source.nodes
  primitiveActual : primitiveOrigin = rawOrigin current
  fieldsActual : CPS1ElectronicEvolution.fields (rawField current) state.rawC =
    CPS1ElectronicEvolution.fields (basis current) state.occupied

def native_origin_face (state : PostState current) : NativeOriginFace state := by
  refine ⟨postNucleus state,post_nucleus_actual state,nucleus_complete state,?_,
    originAt source,rfl,source_origin_injective source,rawOrigin current,rfl,post_fields state⟩
  intro first second same
  apply Fin.ext
  have addresses := congrArg (fun node : Body.Node => node.particle.address) same
  rw [(post_nucleus_actual state first).2,(post_nucleus_actual state second).2] at addresses
  exact Charged.Address.nucleus.inj addresses

end
end CPS1MaterialIncidence.NativeResumableProbe
