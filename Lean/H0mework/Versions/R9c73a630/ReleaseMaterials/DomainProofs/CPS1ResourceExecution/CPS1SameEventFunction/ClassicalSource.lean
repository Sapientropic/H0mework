import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.ClassicalOwnership
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Closure
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Unique

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction.Classical
noncomputable section
open CPS1AtomicSource CPS1AtomicDynamics CPS1LocalChemicalExecution
variable {frame : CPS1Recycling.Frame}

-- The classical source is the exact source graph restriction. Template
-- protonation remains explicit; this does not assert a paid atomization run.
inductive AdmissionFailure
  | noPaidAtomicOccurrence
  | source (failure : CPS1SameEventFunction.SourceFailure)
  | rows (failure : Body.Failure)
  deriving DecidableEq

structure Source (cursor : CPS1ReactiveNuclear.SourceCursor frame) where
  owned : OwnedChain frame
  ownership : ownedChain cursor = some owned
  ammonia : AmmoniaAt cursor

def Source.chain {cursor : CPS1ReactiveNuclear.SourceCursor frame} (source : Source cursor) := source.owned.chain

def sourceAt (cursor : CPS1ReactiveNuclear.SourceCursor frame) : Except AdmissionFailure (Source cursor) :=
  match ownership : ownedChain cursor with
  | none => .error .noPaidAtomicOccurrence
  | some owned =>
    match ammoniaAt? cursor with
    | none => .error (.source .noAmmonia)
    | some ammonia => .ok ⟨owned,ownership,ammonia⟩

def Source.graph {cursor : CPS1ReactiveNuclear.SourceCursor frame} (source : Source cursor) :=
  Graph.fromChain frame source.chain

def Source.templateProtonDemand {cursor : CPS1ReactiveNuclear.SourceCursor frame} (_source : Source cursor) :=
  Graph.requiredProtons (Actual.cps1 frame).word

inductive AtomOrigin (cursor : CPS1ReactiveNuclear.SourceCursor frame)
  | chain (source : Graph.Atom)
  | ammonia (material : Fin (LiveStock cursor).length) (source : Graph.Atom)
  deriving DecidableEq

def AtomOrigin.descriptor {cursor : CPS1ReactiveNuclear.SourceCursor frame} : AtomOrigin cursor → Graph.Atom
  | .chain atom | .ammonia _ atom => atom

def AtomOrigin.isAmmonia {cursor : CPS1ReactiveNuclear.SourceCursor frame} : AtomOrigin cursor → Bool
  | .ammonia _ _ => true | _ => false

def Source.atoms {cursor : CPS1ReactiveNuclear.SourceCursor frame} (source : Source cursor) : List (AtomOrigin cursor) :=
  source.graph.atoms.map AtomOrigin.chain ++
    ammoniaGraph.atoms.map (AtomOrigin.ammonia source.ammonia.slot)

structure Particle (cursor : CPS1ReactiveNuclear.SourceCursor frame) where
  origin : AtomOrigin cursor
  readout : Charged.Particle
  deriving DecidableEq

def atomParticles {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (row : AtomOrigin cursor × Nat) : List (Particle cursor) :=
  (Charged.atomParticles (row.1.descriptor,row.2)).map (fun particle => ⟨row.1,particle⟩)

def Source.particles {cursor : CPS1ReactiveNuclear.SourceCursor frame} (source : Source cursor) : List (Particle cursor) :=
  source.atoms.zipIdx.flatMap atomParticles

def Source.descriptorGraph {cursor : CPS1ReactiveNuclear.SourceCursor frame} (source : Source cursor) : Graph.Molecule :=
  ⟨source.atoms.map AtomOrigin.descriptor,[],[]⟩

theorem source_particle_readout {cursor : CPS1ReactiveNuclear.SourceCursor frame} (source : Source cursor) :
    source.particles.map Particle.readout = Charged.particles source.descriptorGraph := by
  simp only [Source.particles,Source.descriptorGraph,atomParticles,List.map_flatMap,List.map_map,
    Function.comp_def,Charged.particles]
  rw [List.zipIdx_map,List.flatMap_map]
  simp only [List.map_id_fun']
  rfl

theorem source_global_addresses_unique {cursor : CPS1ReactiveNuclear.SourceCursor frame} (source : Source cursor) :
    (source.particles.map (fun particle => particle.readout.address)).Nodup := by
  change (source.particles.map (Charged.Particle.address ∘ Particle.readout)).Nodup
  rw [← List.map_map,source_particle_readout]
  exact Charged.particles_unique _

def Source.originAt? {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Source cursor) (address : Charged.Address) : Option (AtomOrigin cursor) :=
  (source.particles.find? (fun particle => particle.readout.address = address)).map Particle.origin

theorem source_origin_generated {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Source cursor) (particle : Particle cursor) (held : particle ∈ source.particles) :
    source.originAt? particle.readout.address = some particle.origin := by
  let predicate := fun candidate : Particle cursor => decide (candidate.readout.address = particle.readout.address)
  have existsFound : (source.particles.find? predicate).isSome :=
    List.find?_isSome.mpr ⟨particle,held,by simp [predicate]⟩
  cases selected : source.particles.find? predicate with
  | none => rw [selected] at existsFound; cases existsFound
  | some found =>
    have foundHeld := List.mem_of_find?_eq_some selected
    have address := of_decide_eq_true (List.find?_some (p := predicate) selected)
    have identity := List.inj_on_of_nodup_map (source_global_addresses_unique source) foundHeld held address
    unfold Source.originAt?
    change (source.particles.find? predicate).map Particle.origin = _
    rw [selected,identity]
    rfl

structure Raw where
  rows : List (Charged.Address × Body.Row)
  reserve : ℝ
  time : ℝ

structure Packet (cursor : CPS1ReactiveNuclear.SourceCursor frame) (raw : Raw) where
  source : Source cursor
  nodes : List Body.Node
  compatible : rowCompatible source.owned.chainRows raw.rows = .ok ()
  actual : Body.gather (source.particles.map Particle.readout) (source.owned.chainRows ++ raw.rows) = .ok nodes

def packet (cursor : CPS1ReactiveNuclear.SourceCursor frame) (raw : Raw) : Except AdmissionFailure (Packet cursor raw) := do
  let source ← sourceAt cursor
  match compatible : rowCompatible source.owned.chainRows raw.rows with
  | .error failure => .error (.rows failure)
  | .ok _ =>
    match actual : Body.gather (source.particles.map Particle.readout) (source.owned.chainRows ++ raw.rows) with
    | .error failure => .error (.rows failure)
    | .ok nodes => .ok ⟨source,nodes,compatible,actual⟩

theorem actual_source_whole {cursor : CPS1ReactiveNuclear.SourceCursor frame} {raw : Raw}
    (packet : Packet cursor raw) :
    packet.nodes.map Body.Node.particle = packet.source.particles.map Particle.readout ∧
    (packet.source.ammonia.material :: packet.source.ammonia.unspent).Perm (LiveStock cursor) ∧
    (packet.nodes.map (fun node => node.particle.address)).Nodup := by
  have source := Body.gather_source _ _ _ packet.actual
  refine ⟨source.1,?_,?_⟩
  · simpa only [AmmoniaAt.material,AmmoniaAt.unspent,List.get_eq_getElem] using
      List.getElem_cons_eraseIdx_perm packet.source.ammonia.slot.isLt
  · have addresses := congrArg (List.map Charged.Particle.address) source.1
    simp only [List.map_map,Function.comp_def] at addresses
    rw [addresses]
    exact source_global_addresses_unique packet.source

end
end CPS1SameEventFunction.Classical
