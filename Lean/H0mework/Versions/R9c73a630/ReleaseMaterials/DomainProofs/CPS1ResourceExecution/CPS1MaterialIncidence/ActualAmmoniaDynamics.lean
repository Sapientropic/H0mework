import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualFirstProducts
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualAmmoniaSubstitution
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NumberAction
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PhosphorylExchange.Positive
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.Budget

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeAmmoniaDynamics
noncomputable section
open CPS1AtomicSource CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange
open NativeProducts
open scoped BigOperators InnerProductSpace Matrix Topology

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}

def carbonDescriptor : Graph.Atom := bicarbonateGraph.atoms.get ⟨0,by decide⟩
def nitrogenDescriptor : Graph.Atom := ammoniaGraph.atoms.get ⟨0,by decide⟩

structure AmmoniaSource (source : Common before step raw) (current : NativeCurrent source) where
  material : NativeSubstitution.NativeAmmoniaSubstitution source current
  carbon : AtomSector source
  leaving : AtomSector source
  attacking : AtomSector source
  carbonOrigin : sectorOrigin current carbon = .fuel material.products.bicarbonate .bicarbonate carbonDescriptor
  leavingOrigin : sectorOrigin current leaving = .fuel material.products.bicarbonate .bicarbonate attackingDescriptor
  attackingOrigin : sectorOrigin current attacking = .prior (.ammonia before.packet.source.ammonia.slot nitrogenDescriptor)

private theorem sector_for_origin (source : Common before step raw) (current : NativeCurrent source)
    (origin : AtomOrigin cursor) (held : origin ∈ vertices source) :
    ∃ index : AtomSector source, sectorOrigin current index = origin := by
  obtain ⟨atom,atomHeld,same⟩ := List.mem_map.mp held
  obtain ⟨slot,found⟩ := List.getElem?_of_mem atomHeld
  let index : AtomSector source := ⟨slot,(List.getElem?_eq_some_iff.mp found).1⟩
  refine ⟨index,?_⟩
  change (source.atoms.get index).origin = origin
  have actual : source.atoms.get index = atom := (List.getElem?_eq_some_iff.mp found).2
  rw [actual]
  exact same

private theorem source_fuel_occurrence (source : Common before step raw)
    (occurrence : Nat) (kind : FuelKind) (payload : Graph.Atom)
    (held : AtomOrigin.fuel occurrence kind payload ∈ vertices source) :
    (kind,occurrence) ∈ raw.fuel.zipIdx := by
  obtain ⟨atom,atomHeld,origin⟩ := List.mem_map.mp held
  rw [source.atomSource] at atomHeld
  rcases List.mem_append.mp atomHeld with priorHeld | fuelHeld
  · obtain ⟨prior,_,same⟩ := List.mem_map.mp priorHeld
    subst atom
    cases origin
  · obtain ⟨entry,entryHeld,payloadHeld⟩ := List.mem_flatMap.mp fuelHeld
    obtain ⟨original,_,same⟩ := List.mem_map.mp payloadHeld
    subst atom
    have parts := AtomOrigin.fuel.inj origin
    rw [← parts.1,← parts.2.1]
    exact entryHeld

private theorem fuel_atom_held (source : Common before step raw)
    (occurrence : Nat) (kind : FuelKind) (payload : Graph.Atom)
    (indexed : (kind,occurrence) ∈ raw.fuel.zipIdx) (held : payload ∈ (fuelGraph kind).atoms) :
    (⟨.fuel occurrence kind payload,payload⟩ : Atom cursor) ∈ source.atoms := by
  rw [source.atomSource]
  exact List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨(kind,occurrence),indexed,List.mem_map.mpr ⟨payload,held,rfl⟩⟩)

private theorem ammonia_atom_held (source : Common before step raw)
    (payload : Graph.Atom) (held : payload ∈ ammoniaGraph.atoms) :
    (⟨.prior (.ammonia before.packet.source.ammonia.slot payload),payload⟩ : Atom cursor) ∈ source.atoms := by
  rw [source.atomSource]
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨.ammonia before.packet.source.ammonia.slot payload,?_,rfl⟩
  exact List.mem_append_right _ (List.mem_map.mpr ⟨payload,held,rfl⟩)

theorem ammonia_source_nonempty (source : Common before step raw) (current : NativeCurrent source) :
    Nonempty (AmmoniaSource source current) := by
  obtain ⟨material⟩ := NativeSubstitution.native_incidence_ammonia_substitution source current
  have oxygenHeld := (source_token_vertices source current material.trace.selection.bond material.trace.selection.bondActual).2.2.2.2
  rw [material.products.token] at oxygenHeld
  have indexed := source_fuel_occurrence source material.products.bicarbonate .bicarbonate attackingDescriptor oxygenHeld
  have carbonPresent : carbonDescriptor ∈ (fuelGraph .bicarbonate).atoms := by decide +kernel
  have nitrogenPresent : nitrogenDescriptor ∈ ammoniaGraph.atoms := by decide +kernel
  have carbonHeld : AtomOrigin.fuel material.products.bicarbonate .bicarbonate carbonDescriptor ∈ vertices source :=
    List.mem_map_of_mem (fuel_atom_held source material.products.bicarbonate .bicarbonate carbonDescriptor indexed carbonPresent)
  have nitrogenHeld : AtomOrigin.prior (.ammonia before.packet.source.ammonia.slot nitrogenDescriptor) ∈ vertices source :=
    List.mem_map_of_mem (ammonia_atom_held source nitrogenDescriptor nitrogenPresent)
  obtain ⟨carbon,cActual⟩ := sector_for_origin source current _ carbonHeld
  obtain ⟨leaving,lActual⟩ := sector_for_origin source current _ oxygenHeld
  obtain ⟨attacking,aActual⟩ := sector_for_origin source current _ nitrogenHeld
  exact ⟨⟨material,carbon,leaving,attacking,cActual,lActual,aActual⟩⟩

theorem current_inertia_positive (source : Common before step raw) (current : NativeCurrent source)
    (node : Body.Node) (held : node ∈ current.nodes) : 0 < node.row.inertia := by
  rw [current.nodesActual] at held
  obtain ⟨original,originalHeld,same⟩ := List.mem_map.mp held
  subst node
  have paid := (common_measured_whole source).2.2 original originalHeld
  cases address : original.particle.address <;> simpa only [CPS1PhosphorylExchange.sourceKick,address] using paid

structure PostState {source : Common before step raw} (current : NativeCurrent source) where
  index : Nat
  elapsed : ℝ
  pose : List Body.Node
  occupied : Matrix (BasisIndex current) (Electron source.nodes) ℂ
  reserve : ℝ
  particles : pose.map Body.Node.particle = current.nodes.map Body.Node.particle
  gram : occupied.conjTranspose * occupied = 1
  ready : Body.ready pose
  inertia : ∀ node ∈ pose, 0 < node.row.inertia
  nonnegative : 0 ≤ reserve

def initialState {source : Common before step raw} {current : NativeCurrent source}
    (origin : AmmoniaSource source current) : PostState current :=
  let physical := origin.material.event.after.whole.1
  ⟨0,raw.time,physical.nodes,coordinates physical,physical.reserve,rfl,coordinates_gram physical,physical.ready,
    current_inertia_positive source physical,physical.positiveReserve⟩

def PostState.rawC {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) : Matrix (RawIndex current) (Electron source.nodes) ℂ :=
  rawIncrement current state.occupied

def PostState.energy {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) : ℝ := rawEnergy current state.pose state.rawC

def PostState.time {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) : ℝ := raw.time*CPS1ReactiveFieldDynamics.dyadicTime state.index

theorem post_time_positive {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) : 0 < state.time :=
  mul_pos current.elapsed (CPS1ReactiveFieldDynamics.dyadic_time_positive _)

theorem initial_fullC {source : Common before step raw} {current : NativeCurrent source}
    (origin : AmmoniaSource source current) :
    (initialState origin).rawC = rawOccupation current := raw_increment_current current

theorem initial_fullE {source : Common before step raw} {current : NativeCurrent source}
    (origin : AmmoniaSource source current) :
    (initialState origin).energy = wholeEnergyAt source.nodes current.nodes source.electronInertia current.occupied := by
  rw [PostState.energy,initial_fullC]
  exact current_energy_restriction current current.nodes

def fullFockAt {source : Common before step raw} (current : NativeCurrent source) (pose : List Body.Node)
    (occupied : Matrix (BasisIndex current) (Electron source.nodes) ℂ) :=
  (sourceCoefficient current).conjTranspose * rawFock current pose (rawIncrement current occupied) * sourceCoefficient current

theorem full_fock_hermitian {source : Common before step raw} (current : NativeCurrent source)
    (pose : List Body.Node) (occupied : Matrix (BasisIndex current) (Electron source.nodes) ℂ) :
    (fullFockAt current pose occupied).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_mul _ (raw_fock_hermitian current pose _)

theorem full_energy_fock_line {source : Common before step raw} (current : NativeCurrent source)
    (pose : List Body.Node) (occupied direction : Matrix (RawIndex current) (Electron source.nodes) ℂ) :
    HasDerivAt (fun time : ℝ => rawEnergy current pose (occupied+time • direction))
      (2*(Matrix.trace (occupied.conjTranspose*rawFock current pose occupied*direction)).re) 0 := by
  have generated := CPS1Deformation.FiniteVariation.occupied_energy_line
    (rawCore current pose) (rawTwoBody current) (raw_two_body_swap current) occupied direction
    (raw_fock_hermitian current pose occupied)
  have full := generated.const_add (Body.energy (nucleusNodes pose))
  simpa only [rawEnergy,rawDensity,rawFock,CPS1Deformation.FiniteVariation.densityEnergy,
    CPS1Deformation.FiniteVariation.interaction,CPS1Deformation.FiniteVariation.fock,
    add_assoc,add_comm,add_left_comm] using! full

def halfCoordinates {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) : Matrix (BasisIndex current) (Electron source.nodes) ℂ :=
  CPS1ElectronicEvolution.occupiedUpdate (fullFockAt current state.pose state.occupied) (state.time/2) state.occupied

def fullForce {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) (node : Body.Node) : Body.Point :=
  match node.particle.address with
  | .electron .. => 0
  | .nucleus _ => WithLp.toLp 2 (fun axis => -deriv (fun amount =>
      rawEnergy current (displaced state.pose node.particle.address axis amount)
        (rawIncrement current (halfCoordinates state))) 0)

def fullKick {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) (node : Body.Node) : Body.Node :=
  match node.particle.address with
  | .electron .. => node
  | .nucleus _ =>
    {node with row := {node.row with
      position := node.row.position+(state.time/node.row.inertia) • node.row.momentum+
        (state.time^2/(2*node.row.inertia)) • fullForce state node
      momentum := node.row.momentum+state.time • fullForce state node}}

def endPose {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) : List Body.Node := state.pose.map (fullKick state)

def endCoordinates {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) : Matrix (BasisIndex current) (Electron source.nodes) ℂ :=
  CPS1ElectronicEvolution.occupiedUpdate (fullFockAt current (endPose state) (halfCoordinates state))
    (state.time/2) (halfCoordinates state)

def energyPrice {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) : ℝ :=
  rawEnergy current (endPose state) (rawIncrement current (endCoordinates state))-state.energy

def FullSmooth {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) : Prop :=
  ∀ node ∈ nucleusNodes state.pose, ∀ axis : Fin 3, DifferentiableAt ℝ
    (fun amount => rawEnergy current (displaced state.pose node.particle.address axis amount)
      (rawIncrement current (halfCoordinates state))) 0

theorem half_gram {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) : (halfCoordinates state).conjTranspose*halfCoordinates state = 1 :=
  (CPS1ElectronicEvolution.occupied_gram _ (full_fock_hermitian current state.pose state.occupied) _ _).trans state.gram

theorem end_gram {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) : (endCoordinates state).conjTranspose*endCoordinates state = 1 :=
  (CPS1ElectronicEvolution.occupied_gram _ (full_fock_hermitian current _ _) _ _).trans (half_gram state)

theorem half_cayley {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) :
    CPS1ElectronicEvolution.denominator (fullFockAt current state.pose state.occupied) (state.time/2)*halfCoordinates state =
      (1-CPS1ElectronicEvolution.generator (fullFockAt current state.pose state.occupied) (state.time/2))*state.occupied := by
  rw [halfCoordinates,CPS1ElectronicEvolution.occupiedUpdate,← Matrix.mul_assoc,
    CPS1ElectronicEvolution.actual_equation _ (full_fock_hermitian current _ _)]

theorem end_cayley {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) :
    CPS1ElectronicEvolution.denominator (fullFockAt current (endPose state) (halfCoordinates state)) (state.time/2)*endCoordinates state =
      (1-CPS1ElectronicEvolution.generator (fullFockAt current (endPose state) (halfCoordinates state)) (state.time/2))*halfCoordinates state := by
  rw [endCoordinates,CPS1ElectronicEvolution.occupiedUpdate,← Matrix.mul_assoc,
    CPS1ElectronicEvolution.actual_equation _ (full_fock_hermitian current _ _)]

theorem end_particles {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) : (endPose state).map Body.Node.particle = current.nodes.map Body.Node.particle := by
  rw [endPose,List.map_map]
  calc
    _ = state.pose.map Body.Node.particle := by
      apply List.map_congr_left
      intro node _
      cases address : node.particle.address <;> simp only [Function.comp_def,fullKick,address]
    _ = _ := state.particles

theorem end_inertia {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) (node : Body.Node) (held : node ∈ endPose state) : 0 < node.row.inertia := by
  obtain ⟨original,originalHeld,same⟩ := List.mem_map.mp held
  subst node
  have paid := state.inertia original originalHeld
  cases address : original.particle.address <;> simpa only [fullKick,address] using paid

theorem full_force_component {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) (node : Body.Node) (held : node ∈ nucleusNodes state.pose) (axis : Fin 3) :
    fullForce state node axis = -deriv (fun amount => rawEnergy current
      (displaced state.pose node.particle.address axis amount) (rawIncrement current (halfCoordinates state))) 0 := by
  have nuclear := (List.mem_filter.mp held).2
  cases address : node.particle.address with
  | electron slot orbital => simp only [address,Bool.false_eq_true] at nuclear
  | nucleus slot => simp only [fullForce,address,WithLp.ofLp_toLp]

theorem full_force_derivative {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) (smooth : FullSmooth state) (node : Body.Node)
    (held : node ∈ nucleusNodes state.pose) (axis : Fin 3) :
    HasDerivAt (fun amount => rawEnergy current (displaced state.pose node.particle.address axis amount)
      (rawIncrement current (halfCoordinates state))) (-fullForce state node axis) 0 := by
  rw [full_force_component state node held axis,neg_neg]
  exact (smooth node held axis).hasDerivAt

theorem post_nucleus_generated {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) (index : AtomSector source) :
    ∃ node ∈ state.pose, node.particle.address = .nucleus index.val := by
  obtain ⟨original,held,address⟩ := current_nucleus_generated current index
  have present : original.particle ∈ state.pose.map Body.Node.particle := by
    rw [state.particles]
    exact List.mem_map_of_mem held
  obtain ⟨node,nodeHeld,same⟩ := List.mem_map.mp present
  exact ⟨node,nodeHeld,(congrArg Charged.Particle.address same).trans address⟩

def postNucleus {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) (index : AtomSector source) : Body.Node :=
  Classical.choose (post_nucleus_generated state index)

theorem post_nucleus_actual {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) (index : AtomSector source) :
    postNucleus state index ∈ state.pose ∧ (postNucleus state index).particle.address = .nucleus index.val :=
  Classical.choose_spec (post_nucleus_generated state index)

def fullDensityKernel {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) (first second : Body.Point) : ℂ :=
  ∑ spin : Bool, ∑ i : RawIndex current, ∑ j : RawIndex current,
    star (rawValue current i 0 spin (fun axis => first axis))*rawDensity current state.rawC i j*
      rawValue current j 0 spin (fun axis => second axis)

theorem initial_density_exact {source : Common before step raw} {current : NativeCurrent source}
    (origin : AmmoniaSource source current) (first second : Body.Point) :
    fullDensityKernel (initialState origin) first second = densityKernelAt source.nodes current.occupied first second := by
  simp only [fullDensityKernel,initial_fullC,Fintype.sum_sum_type,raw_density_old,
    raw_density_local_left,raw_density_local_right,mul_zero,zero_mul,Finset.sum_const_zero,add_zero]
  unfold densityKernelAt densityKernel
  apply Finset.sum_congr rfl
  intro spin _
  cases spin <;> simp [Fintype.sum_prod_type,rawValue]

def bondRead {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) (first second : AtomSector source) : ℝ :=
  Complex.normSq (fullDensityKernel state (postNucleus state first).row.position (postNucleus state second).row.position)

theorem initial_bond_exact {source : Common before step raw} {current : NativeCurrent source}
    (origin : AmmoniaSource source current) (first second : AtomSector source) :
    bondRead (initialState origin) first second = bondWeight source.nodes current.occupied
      (postNucleus (initialState origin) first).row.position (postNucleus (initialState origin) second).row.position := by
  rw [bondRead,initial_density_exact]
  rfl

def StrictExchange {source : Common before step raw} {current : NativeCurrent source}
    (origin : AmmoniaSource source current) (old next : PostState current) : Prop :=
  bondRead next origin.carbon origin.leaving < bondRead old origin.carbon origin.leaving ∧
    bondRead old origin.carbon origin.attacking < bondRead next origin.carbon origin.attacking

structure PaidStep {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) : Type where
  smooth : FullSmooth state
  ready : Body.ready (endPose state)
  budget : energyPrice state ≤ state.reserve

def PaidStep.after {source : Common before step raw} {current : NativeCurrent source}
    {state : PostState current} (event : PaidStep state) : PostState current :=
  ⟨0,state.elapsed+state.time,endPose state,endCoordinates state,state.reserve-energyPrice state,
    end_particles state,end_gram state,event.ready,end_inertia state,sub_nonneg.mpr event.budget⟩

theorem paid_account {source : Common before step raw} {current : NativeCurrent source}
    {state : PostState current} (event : PaidStep state) :
    event.after.energy+event.after.reserve = state.energy+state.reserve := by
  change rawEnergy current (endPose state) (rawIncrement current (endCoordinates state))+
    (state.reserve-energyPrice state) = state.energy+state.reserve
  unfold energyPrice
  ring

theorem paid_clock {source : Common before step raw} {current : NativeCurrent source}
    {state : PostState current} (event : PaidStep state) : state.elapsed < event.after.elapsed := by
  change state.elapsed < state.elapsed+state.time
  exact lt_add_of_pos_right _ (post_time_positive state)

theorem paid_fullC_increment {source : Common before step raw} {current : NativeCurrent source}
    {state : PostState current} (event : PaidStep state) :
    event.after.rawC = state.rawC+sourceCoefficient current*(event.after.occupied-state.occupied) := by
  change rawIncrement current (endCoordinates state) = rawIncrement current state.occupied+
    sourceCoefficient current*(endCoordinates state-state.occupied)
  simp only [rawIncrement,Matrix.mul_sub]
  abel

theorem post_fields {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) : CPS1ElectronicEvolution.fields (rawField current) state.rawC =
      CPS1ElectronicEvolution.fields (basis current) state.occupied := raw_increment_fields current state.occupied

theorem post_electron_number {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) : Matrix.trace (state.occupied*state.occupied.conjTranspose) =
      (electronCount source.nodes : ℂ) := by
  rw [Matrix.trace_mul_comm,state.gram]
  simp only [Matrix.trace_one,Fintype.card_fin,Electron]

def refineState {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) : PostState current := {state with index := state.index+1}

theorem refinement_time {source : Common before step raw} {current : NativeCurrent source}
    (state : PostState current) : (refineState state).time = state.time/2 := by
  change raw.time*CPS1ReactiveFieldDynamics.dyadicTime (state.index+1) =
    (raw.time*CPS1ReactiveFieldDynamics.dyadicTime state.index)/2
  rw [CPS1ReactiveFieldDynamics.dyadicTime,pow_succ]
  unfold CPS1ReactiveFieldDynamics.dyadicTime
  ring

structure Positive {source : Common before step raw} {current : NativeCurrent source}
    (origin : AmmoniaSource source current) (state : PostState current) where
  event : PaidStep state
  strict : StrictExchange origin state event.after

inductive Disposition {source : Common before step raw} {current : NativeCurrent source}
    (origin : AmmoniaSource source current) (state : PostState current)
  | positive (event : Positive origin state)
  | wrongDirection (event : PaidStep state) (failed : ¬ StrictExchange origin state event.after)
  | nondifferentiable (failed : ¬ FullSmooth state)
  | collision (smooth : FullSmooth state) (failed : ¬ Body.ready (endPose state))
  | energyShortage (smooth : FullSmooth state) (ready : Body.ready (endPose state))
      (failed : ¬ energyPrice state ≤ state.reserve)

def advance {source : Common before step raw} {current : NativeCurrent source}
    (origin : AmmoniaSource source current) (state : PostState current) : Disposition origin state := by
  classical
  exact if smooth : FullSmooth state then
    if ready : Body.ready (endPose state) then
      if budget : energyPrice state ≤ state.reserve then
        let event : PaidStep state := ⟨smooth,ready,budget⟩
        if strict : StrictExchange origin state event.after then .positive ⟨event,strict⟩
        else .wrongDirection event strict
      else .energyShortage smooth ready budget
    else .collision smooth ready
  else .nondifferentiable smooth

def Disposition.next {source : Common before step raw} {current : NativeCurrent source}
    {origin : AmmoniaSource source current} {state : PostState current} : Disposition origin state → PostState current
  | .positive event => event.event.after
  | .wrongDirection event _ => event.after
  | .nondifferentiable _ | .collision _ _ | .energyShortage _ _ _ => refineState state

theorem disposition_account {source : Common before step raw} {current : NativeCurrent source}
    {origin : AmmoniaSource source current} {state : PostState current} (result : Disposition origin state) :
    result.next.energy+result.next.reserve = state.energy+state.reserve := by
  cases result with
  | positive event => exact paid_account event.event
  | wrongDirection event _ => exact paid_account event
  | nondifferentiable _ => rfl
  | collision _ _ => rfl
  | energyShortage _ _ _ => rfl

theorem disposition_progress {source : Common before step raw} {current : NativeCurrent source}
    {origin : AmmoniaSource source current} {state : PostState current} (result : Disposition origin state) :
    state.elapsed < result.next.elapsed ∨
      (result.next.elapsed = state.elapsed ∧ result.next.index = state.index+1 ∧
        result.next.pose = state.pose ∧ result.next.rawC = state.rawC ∧ result.next.reserve = state.reserve) := by
  cases result with
  | positive event => exact Or.inl (paid_clock event.event)
  | wrongDirection event _ => exact Or.inl (paid_clock event)
  | nondifferentiable _ => exact Or.inr ⟨rfl,rfl,rfl,rfl,rfl⟩
  | collision _ _ => exact Or.inr ⟨rfl,rfl,rfl,rfl,rfl⟩
  | energyShortage _ _ _ => exact Or.inr ⟨rfl,rfl,rfl,rfl,rfl⟩

structure SourceGeneratedDynamics (source : Common before step raw) (current : NativeCurrent source) where
  origin : AmmoniaSource source current
  result : Disposition origin (initialState origin)
  actual : result = advance origin (initialState origin)

theorem source_generated_ammonia_dynamics (source : Common before step raw) (current : NativeCurrent source) :
    Nonempty (SourceGeneratedDynamics source current) := by
  obtain ⟨origin⟩ := ammonia_source_nonempty source current
  exact ⟨⟨origin,advance origin (initialState origin),rfl⟩⟩

theorem positive_independent_readout {source : Common before step raw} {current : NativeCurrent source}
    {origin : AmmoniaSource source current} {state : PostState current} (event : Positive origin state) :
    bondRead event.event.after origin.carbon origin.leaving < bondRead state origin.carbon origin.leaving ∧
      bondRead state origin.carbon origin.attacking < bondRead event.event.after origin.carbon origin.attacking :=
  event.strict

end
end CPS1MaterialIncidence.NativeAmmoniaDynamics
