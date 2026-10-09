import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PhosphorylExchange.Electronic
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.ClassicalRead
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1QuantumNuclear.Derivatives

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1PhosphorylExchange
noncomputable section
open CPS1AtomicDynamics CPS1AtomicSource CPS1SameEventFunction CPS1BiologicalUpdate
open Filter
open scoped BigOperators InnerProductSpace Matrix
open scoped Topology

structure Channel where
  atpOccurrence : Nat
  phosphorus : Charged.Address
  leavingOxygen : Charged.Address
  attackingOxygen : Charged.Address
  deriving DecidableEq

private def atomSlot? {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (occurrence : Nat) (kind : FuelKind) (name : String) : Option Nat :=
  ((atoms.zipIdx).find? (fun entry => match entry.1.origin with
    | .fuel slot source atom => slot == occurrence && source == kind && atom.address.atom == name
    | _ => false)).map Prod.snd

private def firstFuel? (fuel : List FuelKind) (kind : FuelKind) : Option Nat :=
  (fuel.zipIdx.find? (fun entry => entry.1 == kind)).map Prod.snd

def channel? {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (fuel : List FuelKind) : Option Channel := do
  let atp ← firstFuel? fuel .atp
  let bct ← firstFuel? fuel .bicarbonate
  let p ← atomSlot? atoms atp .atp "28"
  let leave ← atomSlot? atoms atp .atp "25"
  let attack ← atomSlot? atoms bct .bicarbonate "O2"
  pure ⟨atp,.nucleus p,.nucleus leave,.nucleus attack⟩

def nodeAt? (nodes : List Body.Node) (address : Charged.Address) : Option Body.Node :=
  nodes.find? (fun node => node.particle.address == address)

private def squareDistance (first second : Body.Point) : ℝ :=
  ∑ axis : Fin 3, (first axis-second axis)^2

def coordinate? (nodes : List Body.Node) (channel : Channel) : Option ℝ := do
  let p ← nodeAt? nodes channel.phosphorus
  let leave ← nodeAt? nodes channel.leavingOxygen
  let attack ← nodeAt? nodes channel.attackingOxygen
  pure (squareDistance p.row.position leave.row.position-squareDistance p.row.position attack.row.position)

def coordinateDirection (nodes : List Body.Node) (channel : Channel) (node : Body.Node) : Body.Point :=
  match nodeAt? nodes channel.phosphorus,nodeAt? nodes channel.leavingOxygen,nodeAt? nodes channel.attackingOxygen with
  | some p,some leave,some attack =>
    if node.particle.address = channel.phosphorus then 2 • (attack.row.position-leave.row.position)
    else if node.particle.address = channel.leavingOxygen then (-2 : ℝ) • (p.row.position-leave.row.position)
    else if node.particle.address = channel.attackingOxygen then 2 • (p.row.position-attack.row.position)
    else 0
  | _,_,_ => 0

def axisDirection (address : Charged.Address) (axis : Fin 3) : Charged.Address → Body.Point :=
  fun selected => if selected = address then WithLp.toLp 2 (Pi.single axis 1) else 0

def displaced (pose : List Body.Node) (address : Charged.Address) (axis : Fin 3) (amount : ℝ) : List Body.Node :=
  pose.map (Field.perturb (axisDirection address axis) amount)

-- This is the full energy derivative on the admitted source, including every
-- nucleus and the internally generated occupied field. Electron rows are not
-- a second classical electron dynamics once the occupied field is captured.
def energyForce (source pose : List Body.Node) (mass : ℝ) (occupied : Coefficients source)
    (node : Body.Node) : Body.Point :=
  match node.particle.address with
  | .electron .. => 0
  | .nucleus _ => WithLp.toLp 2 (fun axis => -deriv
      (fun amount => wholeEnergyAt source (displaced pose node.particle.address axis amount) mass occupied) 0)

def energySmooth (source pose : List Body.Node) (mass : ℝ) (occupied : Coefficients source) : Prop :=
  ∀ node ∈ nucleusNodes pose, ∀ axis : Fin 3,
    DifferentiableAt ℝ
      (fun amount => wholeEnergyAt source (displaced pose node.particle.address axis amount) mass occupied) 0

private theorem list_sum_differentiable {K : Type} [NormedAddCommGroup K] [NormedSpace ℝ K]
    {I : Type} (items : List I) (f : I → ℝ → K)
    (paid : ∀ item ∈ items, DifferentiableAt ℝ (f item) 0) :
    DifferentiableAt ℝ (fun time => (items.map (fun item => f item time)).sum) 0 := by
  induction items with
  | nil => exact differentiableAt_const 0
  | cons item rest ih =>
    simpa only [List.map_cons,List.sum_cons] using!
      (paid item List.mem_cons_self).add (ih (fun other held => paid other (List.mem_cons_of_mem _ held)))

theorem nucleus_nodes_displaced (pose : List Body.Node) (address : Charged.Address) (axis : Fin 3) (amount : ℝ) :
    nucleusNodes (displaced pose address axis amount) =
      (nucleusNodes pose).map (Field.perturb (axisDirection address axis) amount) := by
  induction pose with
  | nil => rfl
  | cons node rest ih =>
    change ((Field.perturb (axisDirection address axis) amount node :: displaced rest address axis amount).filter _) = _
    cases selected : node.particle.address <;>
      simp only [nucleusNodes,List.filter_cons,Field.perturb,selected,if_true,Bool.false_eq_true,if_false,List.map_cons]
    all_goals first | exact ih | exact congrArg _ ih

private theorem perturbed_potential_differentiable (nodes : List Body.Node) (ready : Body.ready nodes)
    (direction : Charged.Address → Body.Point) :
    DifferentiableAt ℝ (fun time => Body.potential (nodes.map (Field.perturb direction time))) 0 := by
  induction nodes with
  | nil => exact differentiableAt_const 0
  | cons first rest ih =>
    have separated := List.pairwise_cons.mp ready
    have pairs := list_sum_differentiable rest
      (fun second time => Coulomb.pairEnergy (first.particle.charge : ℝ) (second.particle.charge : ℝ)
        (Field.perturb direction time first).row.position (Field.perturb direction time second).row.position)
      (fun second held => (Field.pair_line_derivative first second direction (separated.1 second held)).differentiableAt)
    simpa only [List.map_cons,Field.potential_cons,List.map_map,Function.comp_def,Field.perturb] using!
      pairs.add (ih separated.2)

private theorem perturbed_energy_differentiable (nodes : List Body.Node) (ready : Body.ready nodes)
    (direction : Charged.Address → Body.Point) :
    DifferentiableAt ℝ (fun time => Body.energy (nodes.map (Field.perturb direction time))) 0 := by
  have kinetic : ∀ time, Body.kinetic (nodes.map (Field.perturb direction time)) = Body.kinetic nodes := by
    intro time
    simp only [Body.kinetic,List.map_map,Function.comp_def,Field.perturb]
  have potential := perturbed_potential_differentiable nodes ready direction
  simpa only [Body.energy,kinetic] using! (differentiableAt_const (Body.kinetic nodes)).add potential

theorem electronic_trace_displaced_differentiable (source pose : List Body.Node) (mass : ℝ)
    (occupied : Coefficients source) (address : Charged.Address) (axis : Fin 3) :
    DifferentiableAt ℝ
      (fun time => (Matrix.trace (coreAt source (displaced pose address axis time) mass*density occupied)).re) 0 := by
  have attractionSmooth (i j : Spatial source) : DifferentiableAt ℝ
      (fun time => attractionAt source (displaced pose address axis time) i j) 0 := by
    simp only [attractionAt,nucleus_nodes_displaced,List.map_map,Function.comp_def]
    apply list_sum_differentiable
    intro old _
    have kernel := CPS1QuantumNuclear.normalized_nuclear_line 0 (electronCount source+1) i j
      (fun index => old.row.position index)
      (fun index => axisDirection address axis old.particle.address index)
    simpa only [Field.perturb,PiLp.add_apply,PiLp.smul_apply,Pi.add_apply,Pi.smul_apply] using!
      kernel.differentiableAt.const_mul (-(old.particle.charge : ℂ))
  have coreSmooth (i j : Spin source) : DifferentiableAt ℝ
      (fun time => coreAt source (displaced pose address axis time) mass i j) 0 := by
    by_cases spin : i.2 = j.2
    · simp only [coreAt,if_pos spin]
      exact (differentiableAt_const _).add (attractionSmooth i.1 j.1)
    · simp only [coreAt,if_neg spin]
      exact differentiableAt_const 0
  have electronic : DifferentiableAt ℝ
      (fun time => (Matrix.trace (coreAt source (displaced pose address axis time) mass*density occupied)).re) 0 := by
    apply Complex.reCLM.differentiableAt.comp 0
    unfold Matrix.trace Matrix.diag
    apply DifferentiableAt.fun_sum
    intro i _
    simp only [Matrix.mul_apply]
    apply DifferentiableAt.fun_sum
    intro j _
    exact (coreSmooth i j).mul_const _
  exact electronic

theorem energy_smooth_of_ready (source pose : List Body.Node) (mass : ℝ) (occupied : Coefficients source)
    (ready : Body.ready pose) : energySmooth source pose mass occupied := by
  intro node _ axis
  have nuclearReady : Body.ready (nucleusNodes pose) := ready.filter _
  have nuclear := perturbed_energy_differentiable (nucleusNodes pose) nuclearReady
    (axisDirection node.particle.address axis)
  have electronic := electronic_trace_displaced_differentiable source pose mass occupied node.particle.address axis
  simpa only [wholeEnergyAt,nucleus_nodes_displaced] using!
    (nuclear.add electronic).add (differentiableAt_const _)

private theorem sum_no_address (nodes : List Body.Node) (address : Charged.Address) (f : Body.Node → ℝ)
    (absent : address ∉ nodes.map (fun node => node.particle.address)) :
    (nodes.map (fun node => if node.particle.address = address then f node else 0)).sum = 0 := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
    have separated : node.particle.address ≠ address := fun equal => absent (by simp [equal])
    have remaining : address ∉ rest.map (fun node => node.particle.address) :=
      fun held => absent (List.mem_cons_of_mem _ held)
    simp only [List.map_cons,List.sum_cons,if_neg separated,zero_add,ih remaining]

private theorem sum_at_address (nodes : List Body.Node) (unique : (nodes.map (fun node => node.particle.address)).Nodup)
    (target : Body.Node) (held : target ∈ nodes) (f : Body.Node → ℝ) :
    (nodes.map (fun node => if node.particle.address = target.particle.address then f node else 0)).sum = f target := by
  induction nodes with
  | nil => cases held
  | cons node rest ih =>
    have partition := List.nodup_cons.mp unique
    rcases List.mem_cons.mp held with same | remaining
    · subst target
      simp only [List.map_cons,List.sum_cons,ite_true,sum_no_address rest _ _ partition.1,add_zero]
    · have separated : node.particle.address ≠ target.particle.address :=
        fun equal => partition.1 (List.mem_map.mpr ⟨target,remaining,equal.symm⟩)
      simp only [List.map_cons,List.sum_cons,if_neg separated,zero_add]
      exact ih partition.2 remaining

theorem nuclear_energy_axis (pose : List Body.Node)
    (unique : ((nucleusNodes pose).map (fun node => node.particle.address)).Nodup)
    (ready : Body.ready (nucleusNodes pose)) (node : Body.Node) (held : node ∈ nucleusNodes pose) (axis : Fin 3) :
    HasDerivAt (fun time => Body.energy (nucleusNodes (displaced pose node.particle.address axis time)))
      (-(Body.force node (nucleusNodes pose) axis)) 0 := by
  have projected : ((nucleusNodes pose).map (fun other => inner ℝ (Body.force other (nucleusNodes pose))
      (axisDirection node.particle.address axis other.particle.address))).sum =
      Body.force node (nucleusNodes pose) axis := by
    have each (other : Body.Node) : inner ℝ (Body.force other (nucleusNodes pose))
        (axisDirection node.particle.address axis other.particle.address) =
        if other.particle.address = node.particle.address then Body.force other (nucleusNodes pose) axis else 0 := by
      by_cases same : other.particle.address = node.particle.address
      · simp [axisDirection,same,PiLp.inner_apply]
      · simp only [axisDirection,if_neg same,inner_zero_right]
    simp only [each]
    exact sum_at_address _ unique node held _
  have potential := Field.potential_line_derivative (nucleusNodes pose) unique ready (axisDirection node.particle.address axis)
  rw [projected] at potential
  have kinetic : ∀ time, Body.kinetic ((nucleusNodes pose).map (Field.perturb (axisDirection node.particle.address axis) time)) =
      Body.kinetic (nucleusNodes pose) := by
    intro time
    simp only [Body.kinetic,List.map_map,Function.comp_def,Field.perturb]
  simpa only [Body.energy,nucleus_nodes_displaced,kinetic,zero_add] using!
    (hasDerivAt_const (0 : ℝ) (Body.kinetic (nucleusNodes pose))).add potential

def electronicPoseEnergy (source pose : List Body.Node) (mass : ℝ) (occupied : Coefficients source) : ℝ :=
  (Matrix.trace (coreAt source pose mass*density occupied)).re+
    (1/2)*(∑ i, ∑ j, ∑ k, ∑ l, density occupied k i*density occupied l j*
      (twoBody source i j k l-twoBody source i j l k)).re

theorem energy_force_partition (source pose : List Body.Node) (mass : ℝ) (occupied : Coefficients source)
    (unique : ((nucleusNodes pose).map (fun node => node.particle.address)).Nodup)
    (ready : Body.ready (nucleusNodes pose)) (node : Body.Node) (held : node ∈ nucleusNodes pose) (axis : Fin 3) :
    energyForce source pose mass occupied node axis = Body.force node (nucleusNodes pose) axis-
      deriv (fun time => electronicPoseEnergy source (displaced pose node.particle.address axis time) mass occupied) 0 := by
  have nuclear := nuclear_energy_axis pose unique ready node held axis
  have electronic := electronic_trace_displaced_differentiable source pose mass occupied node.particle.address axis
  have smooth : DifferentiableAt ℝ
      (fun time => electronicPoseEnergy source (displaced pose node.particle.address axis time) mass occupied) 0 := by
    simpa only [electronicPoseEnergy] using! electronic.add (differentiableAt_const _)
  have energySplit : (fun time => wholeEnergyAt source (displaced pose node.particle.address axis time) mass occupied) =
      (fun time => Body.energy (nucleusNodes (displaced pose node.particle.address axis time))+
        electronicPoseEnergy source (displaced pose node.particle.address axis time) mass occupied) := by
    funext time
    unfold wholeEnergyAt electronicPoseEnergy
    ring
  have isNucleus := (List.mem_filter.mp held).2
  cases selected : node.particle.address with
  | electron slot orbital => simp [selected] at isNucleus
  | nucleus slot =>
    simp only [energyForce,selected,WithLp.ofLp_toLp]
    rw [selected] at nuclear smooth energySplit
    have actual : deriv (fun time => Body.energy (nucleusNodes (displaced pose (.nucleus slot) axis time))+
        electronicPoseEnergy source (displaced pose (.nucleus slot) axis time) mass occupied) 0 =
        -(Body.force node (nucleusNodes pose) axis)+
          deriv (fun time => electronicPoseEnergy source (displaced pose (.nucleus slot) axis time) mass occupied) 0 := by
      simpa only [Pi.add_apply] using! (nuclear.add smooth.hasDerivAt).deriv
    rw [energySplit,actual]
    ring

theorem common_energy_force {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : Raw} (source : Common before step raw)
    (occupied : Coefficients source.nodes) (node : Body.Node) (held : node ∈ nucleusNodes source.nodes) (axis : Fin 3) :
    energyForce source.nodes source.nodes source.electronInertia occupied node axis =
      Body.force node (nucleusNodes source.nodes) axis-
        deriv (fun time => electronicPoseEnergy source.nodes (displaced source.nodes node.particle.address axis time)
          source.electronInertia occupied) 0 := by
  have unique : ((nucleusNodes source.nodes).map (fun node => node.particle.address)).Nodup :=
    List.pairwise_map.mpr ((List.pairwise_map.mp (common_measured_whole source).2.1).filter _)
  exact energy_force_partition source.nodes source.nodes source.electronInertia occupied unique
    (source.ready.filter _) node held axis

def originAt? {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (address : Charged.Address) : Option (AtomOrigin cursor) :=
  (atoms[address.slot]?).map Atom.origin

def isChainNode {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (node : Body.Node) : Bool :=
  (originAt? atoms node.particle.address).any (fun origin => match origin with
    | .prior (.chain _) => true | _ => false)

def withoutChain {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (pose : List Body.Node) : List Body.Node :=
  pose.filter (fun node => !(isChainNode atoms node))

def chainNuclei {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (pose : List Body.Node) : List Body.Node :=
  (nucleusNodes pose).filter (isChainNode atoms)

theorem nuclei_without_chain {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (pose : List Body.Node) :
    nucleusNodes (withoutChain atoms pose) = (nucleusNodes pose).filter (fun node => !(isChainNode atoms node)) := by
  unfold nucleusNodes withoutChain
  rw [List.filter_comm]

theorem without_chain_displaced {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (pose : List Body.Node) (address : Charged.Address) (axis : Fin 3) (time : ℝ) :
    withoutChain atoms (displaced pose address axis time) = displaced (withoutChain atoms pose) address axis time := by
  unfold withoutChain displaced
  rw [List.filter_map]
  rfl

theorem chain_nuclei_displaced {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (pose : List Body.Node) (target : Body.Node)
    (outside : isChainNode atoms target = false) (axis : Fin 3) (time : ℝ) :
    chainNuclei atoms (displaced pose target.particle.address axis time) = chainNuclei atoms pose := by
  unfold chainNuclei
  rw [nucleus_nodes_displaced,List.filter_map]
  change ((nucleusNodes pose).filter (isChainNode atoms)).map (Field.perturb (axisDirection target.particle.address axis) time) = _
  calc
    _ = ((nucleusNodes pose).filter (isChainNode atoms)).map id := by
      apply List.map_congr_left
      intro node held
      have role := (List.mem_filter.mp held).2
      have different : node.particle.address ≠ target.particle.address := by
        intro same
        have sameRole : isChainNode atoms node = isChainNode atoms target := by
          unfold isChainNode originAt?
          rw [same]
        rw [sameRole,outside] at role
        cases role
      simp only [Field.perturb,axisDirection,if_neg different,smul_zero,add_zero,id_eq]
    _ = _ := List.map_id _

theorem attraction_chain_partition {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (source pose : List Body.Node) (i j : Spatial source) :
    attractionAt source pose i j = attractionAt source (withoutChain atoms pose) i j+
      attractionAt source (chainNuclei atoms pose) i j := by
  rw [attractionAt,attractionAt,nuclei_without_chain]
  have nuclearChain : nucleusNodes (chainNuclei atoms pose) = chainNuclei atoms pose := by
    unfold chainNuclei nucleusNodes
    simp only [List.filter_filter]
    congr 1
    funext node
    cases node.particle.address <;> simp
  rw [attractionAt,nuclearChain]
  symm
  have partition := List.sum_map_filter_add_sum_map_filter_not
    (fun node : Body.Node => isChainNode atoms node = true)
    (fun node : Body.Node => -(node.particle.charge : ℂ)*
      CPS1ElectronicSource.nuclearIntegral 0 (electronCount source+1) i j (fun axis => node.row.position axis))
    (nucleusNodes pose)
  simpa [chainNuclei,Bool.decide_coe,Bool.decide_eq_false,add_comm] using partition

def chainElectronicMatrix {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (source pose : List Body.Node) : Matrix (Spin source) (Spin source) ℂ :=
  fun i j => if i.2 = j.2 then attractionAt source (chainNuclei atoms pose) i.1 j.1 else 0

theorem core_chain_partition {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (source pose : List Body.Node) (mass : ℝ) :
    coreAt source pose mass = coreAt source (withoutChain atoms pose) mass+chainElectronicMatrix atoms source pose := by
  ext i j
  by_cases spin : i.2 = j.2
  · simp only [coreAt,chainElectronicMatrix,Matrix.add_apply,if_pos spin]
    rw [attraction_chain_partition atoms source pose i.1 j.1]
    ring
  · simp only [coreAt,chainElectronicMatrix,Matrix.add_apply,if_neg spin,zero_add]

theorem electronic_chain_partition {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (source pose : List Body.Node) (mass : ℝ) (occupied : Coefficients source) :
    electronicPoseEnergy source pose mass occupied = electronicPoseEnergy source (withoutChain atoms pose) mass occupied+
      (Matrix.trace (chainElectronicMatrix atoms source pose*density occupied)).re := by
  unfold electronicPoseEnergy
  rw [core_chain_partition atoms source pose mass,Matrix.add_mul,Matrix.trace_add,Complex.add_re]
  ring

theorem electronic_chain_derivative {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (source pose : List Body.Node) (mass : ℝ) (occupied : Coefficients source)
    (target : Body.Node) (outside : isChainNode atoms target = false) (axis : Fin 3) :
    deriv (fun time => electronicPoseEnergy source (displaced pose target.particle.address axis time) mass occupied) 0 =
      deriv (fun time => electronicPoseEnergy source (displaced (withoutChain atoms pose) target.particle.address axis time) mass occupied) 0 := by
  have splitting : (fun time => electronicPoseEnergy source (displaced pose target.particle.address axis time) mass occupied) =
      (fun time => electronicPoseEnergy source (displaced (withoutChain atoms pose) target.particle.address axis time) mass occupied+
        (Matrix.trace (chainElectronicMatrix atoms source pose*density occupied)).re) := by
    funext time
    rw [electronic_chain_partition atoms source _ mass occupied,without_chain_displaced]
    have chainFixed : chainElectronicMatrix atoms source (displaced pose target.particle.address axis time) =
        chainElectronicMatrix atoms source pose := by
      unfold chainElectronicMatrix
      rw [chain_nuclei_displaced atoms pose target outside axis time]
    rw [chainFixed]
  have smooth := electronic_trace_displaced_differentiable source (withoutChain atoms pose) mass occupied target.particle.address axis
  have complete : DifferentiableAt ℝ
      (fun time => electronicPoseEnergy source (displaced (withoutChain atoms pose) target.particle.address axis time) mass occupied) 0 := by
    simpa only [electronicPoseEnergy] using! smooth.add (differentiableAt_const _)
  rw [splitting]
  simpa only [Pi.add_apply] using! (complete.hasDerivAt.add_const
    (Matrix.trace (chainElectronicMatrix atoms source pose*density occupied)).re).deriv

theorem nuclear_chain_partition {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (pose : List Body.Node) (node : Body.Node) :
    Body.force node (nucleusNodes pose) = Body.force node (nucleusNodes (withoutChain atoms pose))+
      Body.force node (chainNuclei atoms pose) := by
  rw [nuclei_without_chain]
  unfold chainNuclei Body.force
  symm
  have partition := List.sum_map_filter_add_sum_map_filter_not
    (fun other : Body.Node => isChainNode atoms other = true)
    (fun other : Body.Node => if other.particle.address = node.particle.address then 0 else
      Coulomb.pairForce (node.particle.charge : ℝ) (other.particle.charge : ℝ) node.row.position other.row.position)
    (nucleusNodes pose)
  simpa [Bool.decide_coe,Bool.decide_eq_false,add_comm] using partition

-- This is a restriction of the same complete energy variation. The occupied
-- field is held at the same generated stage in both restrictions.
theorem energy_force_chain {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (source pose : List Body.Node) (mass : ℝ) (occupied : Coefficients source)
    (unique : ((nucleusNodes pose).map (fun node => node.particle.address)).Nodup)
    (ready : Body.ready (nucleusNodes pose)) (node : Body.Node) (held : node ∈ nucleusNodes pose)
    (outside : isChainNode atoms node = false) :
    energyForce source pose mass occupied node-energyForce source (withoutChain atoms pose) mass occupied node =
      Body.force node (chainNuclei atoms pose) := by
  have filteredUnique : ((nucleusNodes (withoutChain atoms pose)).map (fun node => node.particle.address)).Nodup := by
    rw [nuclei_without_chain]
    exact List.pairwise_map.mpr ((List.pairwise_map.mp unique).filter _)
  have filteredReady : Body.ready (nucleusNodes (withoutChain atoms pose)) := by
    rw [nuclei_without_chain]
    exact ready.filter _
  have filteredHeld : node ∈ nucleusNodes (withoutChain atoms pose) := by
    rw [nuclei_without_chain]
    exact List.mem_filter.mpr ⟨held,by simp [outside]⟩
  ext axis
  simp only [PiLp.sub_apply]
  rw [energy_force_partition source pose mass occupied unique ready node held axis,
    energy_force_partition source (withoutChain atoms pose) mass occupied filteredUnique filteredReady node filteredHeld axis,
    electronic_chain_derivative atoms source pose mass occupied node outside axis,
    nuclear_chain_partition atoms pose node]
  simp only [PiLp.add_apply]
  ring

private theorem atom_slot_outside_chain {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (occurrence : Nat) (kind : FuelKind) (name : String) (slot : Nat)
    (chosen : atomSlot? atoms occurrence kind name = some slot) (node : Body.Node)
    (address : node.particle.address = Charged.Address.nucleus slot) : isChainNode atoms node = false := by
  unfold atomSlot? at chosen
  obtain ⟨⟨atom,index⟩,found,same⟩ := Option.map_eq_some_iff.mp chosen
  dsimp only at same
  subst index
  have measured : atoms[slot]? = some atom := List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  have selected := List.find?_some found
  cases origin : atom.origin with
  | prior old => simp only [origin,Bool.false_eq_true] at selected
  | fuel index source payload => simp [isChainNode,originAt?,address,Charged.Address.slot,measured,origin]

theorem channel_outside_chain {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (fuel : List FuelKind) (channel : Channel)
    (selected : channel? atoms fuel = some channel) (node : Body.Node)
    (address : node.particle.address = channel.phosphorus ∨ node.particle.address = channel.leavingOxygen ∨
      node.particle.address = channel.attackingOxygen) : isChainNode atoms node = false := by
  unfold channel? at selected
  simp only [Bind.bind,Option.bind_eq_some_iff,Pure.pure,Option.some.injEq] at selected
  obtain ⟨atp,_,bct,_,phosphorus,pSelected,leaving,leaveSelected,attacking,attackSelected,same⟩ := selected
  cases same
  rcases address with p | leave | attack
  · exact atom_slot_outside_chain atoms atp .atp "28" phosphorus pSelected node p
  · exact atom_slot_outside_chain atoms atp .atp "25" leaving leaveSelected node leave
  · exact atom_slot_outside_chain atoms bct .bicarbonate "O2" attacking attackSelected node attack

theorem chain_coordinate_zero {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (fuel : List FuelKind) (nodes : List Body.Node) (channel : Channel)
    (selected : channel? atoms fuel = some channel) (node : Body.Node)
    (chain : isChainNode atoms node = true) : coordinateDirection nodes channel node = 0 := by
  have outside (related : node.particle.address = channel.phosphorus ∨ node.particle.address = channel.leavingOxygen ∨
      node.particle.address = channel.attackingOxygen) : False := by
    have other := channel_outside_chain atoms fuel channel selected node related
    rw [chain] at other
    cases other
  have p : node.particle.address ≠ channel.phosphorus := fun same => outside (Or.inl same)
  have leave : node.particle.address ≠ channel.leavingOxygen := fun same => outside (Or.inr (Or.inl same))
  have attack : node.particle.address ≠ channel.attackingOxygen := fun same => outside (Or.inr (Or.inr same))
  cases pFound : nodeAt? nodes channel.phosphorus <;>
    cases leaveFound : nodeAt? nodes channel.leavingOxygen <;>
      cases attackFound : nodeAt? nodes channel.attackingOxygen <;>
        simp only [coordinateDirection,pFound,leaveFound,attackFound,if_neg p,if_neg leave,if_neg attack]

def directionalChainWork {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (nodes : List Body.Node) (mass : ℝ)
    (occupied : Coefficients nodes) (channel : Channel) : ℝ :=
  ((nucleusNodes nodes).map (fun node =>
    inner ℝ (energyForce nodes nodes mass occupied node-
      energyForce nodes (withoutChain atoms nodes) mass occupied node)
      (coordinateDirection nodes channel node))).sum

theorem directional_chain_work_nuclear {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (atoms : List (Atom cursor)) (fuel : List FuelKind) (nodes : List Body.Node) (mass : ℝ)
    (occupied : Coefficients nodes) (channel : Channel) (selected : channel? atoms fuel = some channel)
    (unique : (nodes.map (fun node => node.particle.address)).Nodup) (ready : Body.ready nodes) :
    directionalChainWork atoms nodes mass occupied channel =
      ((nucleusNodes nodes).map (fun node => inner ℝ (Body.force node (chainNuclei atoms nodes))
        (coordinateDirection nodes channel node))).sum := by
  have nuclearUnique : ((nucleusNodes nodes).map (fun node => node.particle.address)).Nodup :=
    List.pairwise_map.mpr ((List.pairwise_map.mp unique).filter _)
  unfold directionalChainWork
  congr 1
  apply List.map_congr_left
  intro node held
  cases role : isChainNode atoms node with
  | false => rw [energy_force_chain atoms nodes nodes mass occupied nuclearUnique (ready.filter _) node held role]
  | true => rw [chain_coordinate_zero atoms fuel nodes channel selected node role]; simp only [inner_zero_right]

theorem common_chain_nucleus_present {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : Raw} (source : Common before step raw) :
    ∃ node ∈ chainNuclei source.atoms source.nodes, True := by
  let original := before.packet.source
  have backbone := Graph.backbone_present (CPS1LocalChemicalExecution.Actual.cps1 frame).word original.chain.bonds
    0 (by simp [CPS1ResourceExecution.Peptide.word]) "N" (Or.inr rfl)
  obtain ⟨atom,held,_⟩ := (Graph.address_present_iff _ _).mp backbone
  have oldHeld : Classical.AtomOrigin.chain atom ∈ original.atoms := by
    unfold Classical.Source.atoms
    exact List.mem_append_left _ (List.mem_map_of_mem held)
  let generated : Atom cursor := ⟨.prior (.chain atom),atom⟩
  have generatedHeld : generated ∈ commonAtoms original raw.fuel := by
    unfold commonAtoms
    exact List.mem_append_left _ (List.mem_map_of_mem oldHeld)
  obtain ⟨slot,selected⟩ := List.getElem?_of_mem generatedHeld
  let particle : Charged.Particle := ⟨.nucleus slot,atom,(Charged.atomicNumber atom.source.element : Int)⟩
  have particleHeld : particle ∈ commonParticles original raw.fuel := by
    unfold commonParticles
    exact List.mem_flatMap.mpr ⟨(generated,slot),List.mk_mem_zipIdx_iff_getElem?.mpr selected,List.mem_cons_self⟩
  rw [← (common_measured_whole source).1] at particleHeld
  obtain ⟨node,nodeHeld,same⟩ := List.mem_map.mp particleHeld
  have address : node.particle.address = Charged.Address.nucleus slot := congrArg Charged.Particle.address same
  have nuclearHeld : node ∈ nucleusNodes source.nodes := List.mem_filter.mpr ⟨nodeHeld,by rw [address]⟩
  have chain : isChainNode source.atoms node = true := by
    dsimp only [original] at selected
    simp only [isChainNode,originAt?,address,Charged.Address.slot,source.atomSource,selected,
      Option.map_some,Option.any_some]
    rfl
  exact ⟨node,List.mem_filter.mpr ⟨nuclearHeld,chain⟩,True.intro⟩

private theorem positive_sum (nodes : List Body.Node)
    (positive : ∀ node ∈ nodes, 0 < (node.particle.charge : ℝ)) (present : ∃ node ∈ nodes, True) :
    0 < (nodes.map (fun node => (node.particle.charge : ℝ))).sum := by
  cases nodes with
  | nil => obtain ⟨node,held,_⟩ := present; cases held
  | cons node rest =>
    have nonnegative : 0 ≤ (rest.map (fun node => (node.particle.charge : ℝ))).sum := by
      apply List.sum_nonneg
      intro value held
      rcases List.mem_map.mp held with ⟨other,member,rfl⟩
      exact (positive other (List.mem_cons_of_mem _ member)).le
    simpa only [List.map_cons,List.sum_cons] using add_pos_of_pos_of_nonneg
      (positive node List.mem_cons_self) nonnegative

theorem common_chain_charge_positive {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : Raw} (source : Common before step raw) :
    0 < ((chainNuclei source.atoms source.nodes).map (fun node => (node.particle.charge : ℝ))).sum := by
  apply positive_sum _ _ (common_chain_nucleus_present source)
  intro node held
  exact common_nucleus_positive source node (List.mem_filter.mp held).1

-- This is the exact normalized 1/r² field of each original chain nucleus.
-- The coordinate family moves only the admitted fresh fuel nuclei.
def scaledDisplacement (old : Body.Point) (x offset parameter : ℝ) : Body.Point :=
  WithLp.toLp 2 ![parameter*(x-old 0),1+parameter*(offset-old 1),-parameter*old 2]

def scaledPairForce (charge : ℝ) (old : Body.Node) (x offset parameter : ℝ) : ℝ :=
  charge*(old.particle.charge : ℝ)*(1+parameter*(offset-old.row.position 1)) /
    ‖scaledDisplacement old.row.position x offset parameter‖^3

theorem scaled_displacement_zero (old : Body.Point) (x offset : ℝ) :
    scaledDisplacement old x offset 0 = WithLp.toLp 2 (Pi.single (1 : Fin 3) (1 : ℝ)) := by
  ext axis
  fin_cases axis <;> norm_num [scaledDisplacement,Pi.single_apply]

theorem scaled_pair_force_continuous (charge : ℝ) (old : Body.Node) (x offset : ℝ) :
    ContinuousAt (scaledPairForce charge old x offset) 0 := by
  have displacement : ContinuousAt (scaledDisplacement old.row.position x offset) 0 := by
    unfold scaledDisplacement
    fun_prop
  have unitNorm : ‖scaledDisplacement old.row.position x offset 0‖ = 1 := by
    rw [scaled_displacement_zero]
    change ‖PiLp.single (β := fun _ : Fin 3 => ℝ) 2 (1 : Fin 3) (1 : ℝ)‖ = 1
    simp
  unfold scaledPairForce
  exact (continuousAt_const.mul
    (continuousAt_const.add (continuousAt_id.mul continuousAt_const))).div (displacement.norm.pow 3)
      (by rw [unitNorm]; norm_num)

theorem scaled_pair_force_zero (charge : ℝ) (old : Body.Node) (x offset : ℝ) :
    scaledPairForce charge old x offset 0 = charge*(old.particle.charge : ℝ) := by
  have unitNorm : ‖scaledDisplacement old.row.position x offset 0‖ = 1 := by
    rw [scaled_displacement_zero]
    change ‖PiLp.single (β := fun _ : Fin 3 => ℝ) 2 (1 : Fin 3) (1 : ℝ)‖ = 1
    simp
  simp only [scaledPairForce,zero_mul,add_zero,mul_one,unitNorm,one_pow,div_one]

theorem scaled_pair_force_actual (charge : ℝ) (old : Body.Node) (x offset parameter : ℝ)
    (positive : 0 < parameter) :
    Coulomb.pairForce charge (old.particle.charge : ℝ) (transversePoint x (1/parameter+offset) 0)
      old.row.position (1 : Fin 3) / parameter^2 = scaledPairForce charge old x offset parameter := by
  have nonzero := ne_of_gt positive
  have scaled : scaledDisplacement old.row.position x offset parameter =
      parameter • (transversePoint x (1/parameter+offset) 0-old.row.position) := by
    ext axis
    fin_cases axis <;> simp [scaledDisplacement,transversePoint]
    all_goals field_simp
    all_goals ring
  have normScaled : ‖scaledDisplacement old.row.position x offset parameter‖ =
      parameter*‖transversePoint x (1/parameter+offset) 0-old.row.position‖ := by
    rw [scaled,norm_smul,Real.norm_eq_abs,abs_of_pos positive]
  simp only [Coulomb.pairForce,PiLp.smul_apply,PiLp.sub_apply,transversePoint,
    Matrix.cons_val_one,Matrix.cons_val_zero,smul_eq_mul,scaledPairForce]
  rw [normScaled]
  unfold transversePoint
  field_simp
  ring

def scaledChainForce (charge : ℝ) (nodes : List Body.Node) (x offset parameter : ℝ) : ℝ :=
  (nodes.map (fun old => scaledPairForce charge old x offset parameter)).sum

private theorem list_sum_continuous {I : Type} (items : List I) (f : I → ℝ → ℝ)
    (paid : ∀ item ∈ items, ContinuousAt (f item) 0) :
    ContinuousAt (fun parameter => (items.map (fun item => f item parameter)).sum) 0 := by
  induction items with
  | nil => exact continuousAt_const
  | cons item rest ih =>
    simpa only [List.map_cons,List.sum_cons] using!
      (paid item List.mem_cons_self).add (ih (fun other held => paid other (List.mem_cons_of_mem _ held)))

theorem scaled_chain_force_continuous (charge : ℝ) (nodes : List Body.Node) (x offset : ℝ) :
    ContinuousAt (scaledChainForce charge nodes x offset) 0 :=
  list_sum_continuous nodes _ (fun node _ => scaled_pair_force_continuous charge node x offset)

theorem scaled_chain_force_zero (charge : ℝ) (nodes : List Body.Node) (x offset : ℝ) :
    scaledChainForce charge nodes x offset 0 = charge*(nodes.map (fun node => (node.particle.charge : ℝ))).sum := by
  unfold scaledChainForce
  simp only [scaled_pair_force_zero]
  induction nodes with
  | nil => simp
  | cons node rest ih => simp only [List.map_cons,List.sum_cons,ih]; ring

def scaledExchangeWork (nodes : List Body.Node) (x parameter : ℝ) : ℝ :=
  2*scaledChainForce 15 nodes x 0 parameter+2*scaledChainForce 8 nodes x 1 parameter-
    4*scaledChainForce 8 nodes x 2 parameter

theorem scaled_exchange_work_continuous (nodes : List Body.Node) (x : ℝ) :
    ContinuousAt (scaledExchangeWork nodes x) 0 := by
  unfold scaledExchangeWork
  exact ((scaled_chain_force_continuous 15 nodes x 0).const_mul 2).add
    ((scaled_chain_force_continuous 8 nodes x 1).const_mul 2) |>.sub
      ((scaled_chain_force_continuous 8 nodes x 2).const_mul 4)

theorem scaled_exchange_work_zero (nodes : List Body.Node) (x : ℝ) :
    scaledExchangeWork nodes x 0 = 14*(nodes.map (fun node => (node.particle.charge : ℝ))).sum := by
  simp only [scaledExchangeWork,scaled_chain_force_zero]
  ring

theorem source_coordinate_work_positive (nodes : List Body.Node) (x : ℝ)
    (charge : 0 < (nodes.map (fun node => (node.particle.charge : ℝ))).sum) :
    ∀ᶠ parameter in 𝓝 (0 : ℝ), 0 < scaledExchangeWork nodes x parameter := by
  apply continuousAt_const.eventually_lt (scaled_exchange_work_continuous nodes x)
  rw [scaled_exchange_work_zero]
  positivity

def verticalChainForce (charge : ℝ) (nodes : List Body.Node) (x offset parameter : ℝ) : ℝ :=
  (nodes.map (fun old => Coulomb.pairForce charge (old.particle.charge : ℝ)
    (transversePoint x (1/parameter+offset) 0) old.row.position (1 : Fin 3))).sum

theorem vertical_chain_force_normalized (charge : ℝ) (nodes : List Body.Node) (x offset parameter : ℝ)
    (positive : 0 < parameter) :
    verticalChainForce charge nodes x offset parameter / parameter^2 = scaledChainForce charge nodes x offset parameter := by
  unfold verticalChainForce scaledChainForce
  induction nodes with
  | nil => simp
  | cons old rest ih =>
    simp only [List.map_cons,List.sum_cons,add_div,scaled_pair_force_actual charge old x offset parameter positive,ih]

def verticalExchangeWork (nodes : List Body.Node) (x parameter : ℝ) : ℝ :=
  2*verticalChainForce 15 nodes x 0 parameter+2*verticalChainForce 8 nodes x 1 parameter-
    4*verticalChainForce 8 nodes x 2 parameter

theorem vertical_exchange_work_normalized (nodes : List Body.Node) (x parameter : ℝ) (positive : 0 < parameter) :
    verticalExchangeWork nodes x parameter / parameter^2 = scaledExchangeWork nodes x parameter := by
  simp only [verticalExchangeWork,scaledExchangeWork,add_div,sub_div,mul_div_assoc,
    vertical_chain_force_normalized _ nodes x _ parameter positive]

theorem finite_source_coordinate_nonempty (nodes : List Body.Node) (x : ℝ)
    (charge : 0 < (nodes.map (fun node => (node.particle.charge : ℝ))).sum) :
    ∃ index : Nat, 0 < verticalExchangeWork nodes x ((1/2 : ℝ)^index) := by
  have powers : Tendsto (fun index : Nat => (1/2 : ℝ)^index) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
  obtain ⟨index,strict⟩ := (powers.eventually (source_coordinate_work_positive nodes x charge)).exists
  have positive : 0 < (1/2 : ℝ)^index := pow_pos (by norm_num) index
  have generated := (div_eq_iff (pow_ne_zero 2 (ne_of_gt positive))).mp
    (vertical_exchange_work_normalized nodes x ((1/2 : ℝ)^index) positive)
  refine ⟨index,?_⟩
  rw [generated]
  exact mul_pos strict (pow_pos positive 2)

theorem common_source_coordinate_nonempty {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : Raw} (source : Common before step raw) (x : ℝ) :
    ∃ index : Nat, 0 < verticalExchangeWork (chainNuclei source.atoms source.nodes) x ((1/2 : ℝ)^index) :=
  finite_source_coordinate_nonempty _ x (common_chain_charge_positive source)

theorem coordinate_work_three (nodes chain : List Body.Node) (channel : Channel) (p leaving attacking : Body.Node)
    (unique : (nodes.map (fun node => node.particle.address)).Nodup)
    (pHeld : p ∈ nucleusNodes nodes) (leaveHeld : leaving ∈ nucleusNodes nodes) (attackHeld : attacking ∈ nucleusNodes nodes)
    (pFound : nodeAt? nodes channel.phosphorus = some p) (leaveFound : nodeAt? nodes channel.leavingOxygen = some leaving)
    (attackFound : nodeAt? nodes channel.attackingOxygen = some attacking)
    (different : channel.phosphorus ≠ channel.leavingOxygen ∧ channel.phosphorus ≠ channel.attackingOxygen ∧
      channel.leavingOxygen ≠ channel.attackingOxygen) :
    ((nucleusNodes nodes).map (fun node => inner ℝ (Body.force node chain) (coordinateDirection nodes channel node))).sum =
      inner ℝ (Body.force p chain) (2 • (attacking.row.position-leaving.row.position))+
      inner ℝ (Body.force leaving chain) ((-2 : ℝ) • (p.row.position-leaving.row.position))+
      inner ℝ (Body.force attacking chain) (2 • (p.row.position-attacking.row.position)) := by
  have address (target : Charged.Address) (node : Body.Node) (selected : nodeAt? nodes target = some node) :
      node.particle.address = target := by
    unfold nodeAt? at selected
    simpa only [beq_iff_eq] using List.find?_some selected
  have pAddress := address _ _ pFound
  have leaveAddress := address _ _ leaveFound
  have attackAddress := address _ _ attackFound
  have nuclearUnique : ((nucleusNodes nodes).map (fun node => node.particle.address)).Nodup :=
    List.pairwise_map.mpr ((List.pairwise_map.mp unique).filter _)
  let first := fun node => inner ℝ (Body.force node chain) (2 • (attacking.row.position-leaving.row.position))
  let second := fun node => inner ℝ (Body.force node chain) ((-2 : ℝ) • (p.row.position-leaving.row.position))
  let third := fun node => inner ℝ (Body.force node chain) (2 • (p.row.position-attacking.row.position))
  have each (node : Body.Node) : inner ℝ (Body.force node chain) (coordinateDirection nodes channel node) =
      (if node.particle.address = channel.phosphorus then first node else 0)+
      (if node.particle.address = channel.leavingOxygen then second node else 0)+
      (if node.particle.address = channel.attackingOxygen then third node else 0) := by
    by_cases atP : node.particle.address = channel.phosphorus
    · have notLeave := fun same : node.particle.address = channel.leavingOxygen => different.1 (atP.symm.trans same)
      have notAttack := fun same : node.particle.address = channel.attackingOxygen => different.2.1 (atP.symm.trans same)
      simp only [coordinateDirection,pFound,leaveFound,attackFound,if_pos atP,if_neg notLeave,if_neg notAttack,add_zero,first]
    · by_cases atLeave : node.particle.address = channel.leavingOxygen
      · have notAttack := fun same : node.particle.address = channel.attackingOxygen => different.2.2 (atLeave.symm.trans same)
        simp only [coordinateDirection,pFound,leaveFound,attackFound,if_neg atP,if_pos atLeave,if_neg notAttack,zero_add,add_zero,second]
      · by_cases atAttack : node.particle.address = channel.attackingOxygen
        · simp only [coordinateDirection,pFound,leaveFound,attackFound,if_neg atP,if_neg atLeave,if_pos atAttack,zero_add,third]
        · simp only [coordinateDirection,pFound,leaveFound,attackFound,if_neg atP,if_neg atLeave,if_neg atAttack,inner_zero_right,zero_add]
  simp only [each,List.sum_map_add]
  rw [← pAddress,← leaveAddress,← attackAddress]
  rw [sum_at_address _ nuclearUnique p pHeld first,sum_at_address _ nuclearUnique leaving leaveHeld second,
    sum_at_address _ nuclearUnique attacking attackHeld third]


end
end CPS1PhosphorylExchange
