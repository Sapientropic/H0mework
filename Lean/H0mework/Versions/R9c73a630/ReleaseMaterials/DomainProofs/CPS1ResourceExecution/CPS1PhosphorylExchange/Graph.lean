import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.Whole
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.State
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Primary

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CPS1PhosphorylExchange
noncomputable section
open CPS1AtomicSource CPS1AtomicDynamics CPS1SameEventFunction

inductive FuelKind | atp | bicarbonate deriving DecidableEq, Repr

def bicarbonateGraph : Graph.Molecule :=
  ⟨[⟨⟨0,"C"⟩,⟨"C",.C,0,false,"N",false,false,false,false⟩⟩,
    ⟨⟨0,"O1"⟩,⟨"O1",.O,0,false,"N",false,false,false,false⟩⟩,
    ⟨⟨0,"O2"⟩,⟨"O2",.O,-1,false,"N",false,false,false,false⟩⟩,
    ⟨⟨0,"O3"⟩,⟨"O3",.O,0,false,"N",false,false,false,false⟩⟩,
    ⟨⟨0,"HO3"⟩,⟨"HO3",.H,0,false,"N",false,false,false,false⟩⟩],
    [⟨⟨0,"C"⟩,⟨0,"O1"⟩,"DOUB",false,"N",.component⟩,
     ⟨⟨0,"C"⟩,⟨0,"O2"⟩,"SING",false,"N",.component⟩,
     ⟨⟨0,"C"⟩,⟨0,"O3"⟩,"SING",false,"N",.component⟩,
     ⟨⟨0,"O3"⟩,⟨0,"HO3"⟩,"SING",false,"N",.component⟩],[]⟩

def atpGraph : Graph.Molecule :=
  ⟨CPS1EnzymeBath.Primary.atp.atoms.map (fun atom =>
    (CPS1EnzymeBath.Joint.bathAtom ⟨0,.atp⟩ atom).descriptor),
   CPS1EnzymeBath.Primary.atp.bonds.map (fun bond =>
     ⟨⟨0,toString bond.left⟩,⟨0,toString bond.right⟩,
       if bond.order = 2 then "DOUB" else "SING",bond.aromatic,bond.stereo,.component⟩),[]⟩

def fuelGraph : FuelKind → Graph.Molecule | .atp => atpGraph | .bicarbonate => bicarbonateGraph

inductive AtomOrigin {frame : CPS1Recycling.Frame}
    (cursor : CPS1ReactiveNuclear.SourceCursor frame)
  | prior (origin : Classical.AtomOrigin cursor)
  | fuel (slot : Nat) (kind : FuelKind) (atom : Graph.Atom)
  deriving DecidableEq

structure Atom {frame : CPS1Recycling.Frame}
    (cursor : CPS1ReactiveNuclear.SourceCursor frame) where
  origin : AtomOrigin cursor
  descriptor : Graph.Atom
  deriving DecidableEq

def commonAtoms {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (fuel : List FuelKind) : List (Atom cursor) :=
  source.atoms.map (fun atom => ⟨.prior atom,atom.descriptor⟩) ++
    fuel.zipIdx.flatMap (fun entry => (fuelGraph entry.1).atoms.map
      (fun atom => ⟨.fuel entry.2 entry.1 atom,atom⟩))

structure SourceBond {frame : CPS1Recycling.Frame}
    (cursor : CPS1ReactiveNuclear.SourceCursor frame) where
  left : AtomOrigin cursor
  right : AtomOrigin cursor
  order : String
  aromatic : Bool
  stereo : String
  deriving DecidableEq

private def graphBonds {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (graph : Graph.Molecule) (origin : Graph.Atom → AtomOrigin cursor) : List (SourceBond cursor) :=
  graph.bonds.filterMap (fun bond => do
    let first ← graph.atoms.find? (fun atom => atom.address == bond.left)
    let second ← graph.atoms.find? (fun atom => atom.address == bond.right)
    pure ⟨origin first,origin second,bond.order,bond.aromatic,bond.stereo⟩)

def commonBonds {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (fuel : List FuelKind) : List (SourceBond cursor) :=
  graphBonds source.graph (fun atom => .prior (.chain atom)) ++
    graphBonds ammoniaGraph (fun atom => .prior (.ammonia source.ammonia.slot atom)) ++
    fuel.zipIdx.flatMap (fun entry => graphBonds (fuelGraph entry.1) (.fuel entry.2 entry.1))

def commonParticles {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (fuel : List FuelKind) : List Charged.Particle :=
  (commonAtoms source fuel).zipIdx.flatMap (fun entry => Charged.atomParticles (entry.1.descriptor,entry.2))

def commonDescriptorGraph {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (fuel : List FuelKind) : Graph.Molecule :=
  ⟨(commonAtoms source fuel).map Atom.descriptor,[],[]⟩

theorem common_particle_readout {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (fuel : List FuelKind) :
    commonParticles source fuel = Charged.particles (commonDescriptorGraph source fuel) := by
  simp only [commonParticles,commonDescriptorGraph,Charged.particles,List.zipIdx_map,List.flatMap_map]
  rfl

theorem common_addresses_unique {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (fuel : List FuelKind) :
    ((commonParticles source fuel).map Charged.Particle.address).Nodup := by
  rw [common_particle_readout]
  exact Charged.particles_unique _

def electronCount (nodes : List Body.Node) : Nat :=
  (nodes.filter (fun node => match node.particle.address with | .electron .. => true | .nucleus _ => false)).length

def nucleusNodes (nodes : List Body.Node) : List Body.Node :=
  nodes.filter (fun node => match node.particle.address with | .nucleus _ => true | .electron .. => false)

structure Raw where
  fuel : List FuelKind
  rows : List (Charged.Address × Body.Row)
  reserve : ℝ
  time : ℝ

inductive Failure
  | priorResponse
  | missingATP
  | missingBicarbonate
  | rows (failure : CPS1SameEventFunction.Classical.AdmissionFailure)
  | gather (failure : Body.Failure)
  | collision
  | unequalElectronInertia
  | negativeReserve
  | captureShortage
  | nonpositiveTime
  | noExchangeCoordinate
  | noPaidChainSlot
  | nondifferentiableEnergy
  | wrongExchangeDirection
  | zeroCoordinateWork
  | unchangedElectronicBond
  | energyShortage
  deriving DecidableEq

structure Common {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time) (raw : Raw) where
  atoms : List (Atom cursor)
  atomSource : atoms = commonAtoms before.packet.source raw.fuel
  bonds : List (SourceBond cursor)
  bondSource : bonds = commonBonds before.packet.source raw.fuel
  atpFuel : 2 ≤ (raw.fuel.filter (· == .atp)).length
  bicarbonateFuel : .bicarbonate ∈ raw.fuel
  nodes : List Body.Node
  measured : Body.gather (commonParticles before.packet.source raw.fuel)
    (step.next.nodes.map (fun node => (node.particle.address,node.row)) ++ raw.rows) = .ok nodes
  electronInertia : ℝ
  uniformElectrons : ∀ node ∈ nodes,
    (match node.particle.address with | .nucleus _ => True | .electron .. => node.row.inertia = electronInertia)
  ready : Body.ready nodes

theorem common_measured_whole {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : Raw} (source : Common before step raw) :
    source.nodes.map Body.Node.particle = commonParticles before.packet.source raw.fuel ∧
    (source.nodes.map (fun node => node.particle.address)).Nodup ∧
    ∀ node ∈ source.nodes, 0 < node.row.inertia := by
  have generated := Body.gather_source _ _ _ source.measured
  refine ⟨generated.1,?_,fun node held => (generated.2 node held).1⟩
  have addresses := congrArg (List.map Charged.Particle.address) generated.1
  simp only [List.map_map,Function.comp_def] at addresses
  rw [addresses]
  exact common_addresses_unique _ _

theorem common_electron_present {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : Raw} (source : Common before step raw) :
    ∃ node ∈ source.nodes, ∃ slot orbital, node.particle.address = Charged.Address.electron slot orbital := by
  let carbon : Graph.Atom := ⟨⟨0,"C"⟩,⟨"C",.C,0,false,"N",false,false,false,false⟩⟩
  have carbonHeld : carbon ∈ (fuelGraph .bicarbonate).atoms := by simp [fuelGraph,bicarbonateGraph,carbon]
  obtain ⟨occurrence,selected⟩ := List.getElem?_of_mem source.bicarbonateFuel
  have indexed : (FuelKind.bicarbonate,occurrence) ∈ raw.fuel.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr selected
  let atom : Atom cursor := ⟨.fuel occurrence .bicarbonate carbon,carbon⟩
  have atomHeld : atom ∈ commonAtoms before.packet.source raw.fuel := by
    unfold commonAtoms
    exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨(.bicarbonate,occurrence),indexed,List.mem_map.mpr ⟨carbon,carbonHeld,rfl⟩⟩)
  obtain ⟨global,found⟩ := List.getElem?_of_mem atomHeld
  let particle : Charged.Particle := ⟨.electron global 0,carbon,-1⟩
  have particleHeld : particle ∈ commonParticles before.packet.source raw.fuel := by
    unfold commonParticles
    refine List.mem_flatMap.mpr ⟨(atom,global),List.mk_mem_zipIdx_iff_getElem?.mpr found,?_⟩
    simp [Charged.atomParticles,Charged.electrons,Charged.atomicNumber,particle,atom,carbon]
  rw [← (common_measured_whole source).1] at particleHeld
  obtain ⟨node,held,same⟩ := List.mem_map.mp particleHeld
  exact ⟨node,held,global,0,congrArg Charged.Particle.address same⟩

theorem common_positive_electrons {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : Raw} (source : Common before step raw) :
    0 < electronCount source.nodes ∧ 0 < source.electronInertia := by
  obtain ⟨node,held,slot,orbital,address⟩ := common_electron_present source
  have electronHeld : node ∈ source.nodes.filter (fun node => match node.particle.address with
      | .electron .. => true | .nucleus _ => false) := List.mem_filter.mpr ⟨held,by rw [address]⟩
  have count : 0 < electronCount source.nodes := List.length_pos_iff_exists_mem.mpr ⟨node,electronHeld⟩
  have inertia := source.uniformElectrons node held
  rw [address] at inertia
  exact ⟨count,inertia ▸ (common_measured_whole source).2.2 node held⟩

theorem common_nucleus_positive {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
    {step : Classical.NativeStep before priorRaw.time} {raw : Raw} (source : Common before step raw)
    (node : Body.Node) (held : node ∈ nucleusNodes source.nodes) : 0 < (node.particle.charge : ℝ) := by
  have fullHeld := (List.mem_filter.mp held).1
  have nuclear := (List.mem_filter.mp held).2
  have generated : node.particle ∈ commonParticles before.packet.source raw.fuel := by
    rw [← (common_measured_whole source).1]
    exact List.mem_map_of_mem fullHeld
  rcases List.mem_flatMap.mp generated with ⟨row,_,particleHeld⟩
  rcases List.mem_cons.mp particleHeld with nucleus | electron
  · have charge := congrArg Charged.Particle.charge nucleus
    rw [charge]
    cases row.1.descriptor.source.element <;> norm_num [Charged.atomicNumber]
  · rcases List.mem_map.mp electron with ⟨orbital,_,same⟩
    have address := congrArg Charged.Particle.address same
    rw [← address] at nuclear
    cases nuclear

private def electronInertia (nodes : List Body.Node) : ℝ :=
  ((nodes.find? (fun node => match node.particle.address with | .electron .. => true | _ => false)).map
    (fun node => node.row.inertia)).getD 1

def admit {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time) (raw : Raw) :
    Except Failure (Common before step raw) := by
  classical
  exact if missingATP : (raw.fuel.filter (· == .atp)).length < 2 then .error .missingATP
    else if missingBicarbonate : .bicarbonate ∉ raw.fuel then .error .missingBicarbonate
    else match Classical.rowCompatible (step.next.nodes.map (fun node => (node.particle.address,node.row))) raw.rows with
    | .error failure => .error (.rows (.rows failure))
    | .ok _ => match found : Body.gather (commonParticles before.packet.source raw.fuel)
        (step.next.nodes.map (fun node => (node.particle.address,node.row)) ++ raw.rows) with
      | .error failure => .error (.gather failure)
      | .ok nodes =>
        if ready : Body.ready nodes then
          let mass := electronInertia nodes
          if equal : ∀ node ∈ nodes, (match node.particle.address with
              | .nucleus _ => True | .electron .. => node.row.inertia = mass) then
            .ok ⟨commonAtoms before.packet.source raw.fuel,rfl,commonBonds before.packet.source raw.fuel,rfl,
              Nat.le_of_not_gt missingATP,not_not.mp missingBicarbonate,nodes,found,mass,equal,ready⟩
          else .error .unequalElectronInertia
        else .error .collision

end
end CPS1PhosphorylExchange
