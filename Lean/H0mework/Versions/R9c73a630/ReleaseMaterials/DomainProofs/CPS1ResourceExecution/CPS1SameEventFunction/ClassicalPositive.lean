import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.ClassicalForce
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.ClassicalContinuation

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction.Classical
noncomputable section
open CPS1AtomicDynamics CPS1AtomicSource
variable {frame : CPS1Recycling.Frame}

def ammoniaNitrogen : Graph.Atom :=
  ⟨⟨0,"N"⟩,⟨"N",.N,0,false,"N",false,false,false,false⟩⟩

def Source.targetParticle {cursor : CPS1ReactiveNuclear.SourceCursor frame} (source : Source cursor) : Particle cursor :=
  ⟨.ammonia source.ammonia.slot ammoniaNitrogen,⟨source.targetAddress,ammoniaNitrogen,7⟩⟩

def Source.targetNode {cursor : CPS1ReactiveNuclear.SourceCursor frame} (source : Source cursor) : Body.Node :=
  ⟨source.targetParticle.readout,⟨0,0,1⟩⟩

theorem target_particle_present {cursor : CPS1ReactiveNuclear.SourceCursor frame} (source : Source cursor) :
    source.targetParticle ∈ source.particles := by
  have atom : (AtomOrigin.ammonia source.ammonia.slot ammoniaNitrogen,source.graph.atoms.length) ∈ source.atoms.zipIdx := by
    rw [List.mk_mem_zipIdx_iff_getElem?]
    simp [Source.atoms,ammoniaGraph,ammoniaNitrogen]
  exact List.mem_flatMap.mpr ⟨_,atom,List.mem_map.mpr ⟨_,List.mem_cons_self,rfl⟩⟩

theorem particle_signed {cursor : CPS1ReactiveNuclear.SourceCursor frame} (source : Source cursor)
    (particle : Particle cursor) (held : particle ∈ source.particles) :
    0 < particle.readout.charge ∨ particle.readout.charge = -1 := by
  rcases List.mem_flatMap.mp held with ⟨row,_,present⟩
  rcases List.mem_map.mp present with ⟨readout,generated,same⟩
  subst particle
  rcases List.mem_cons.mp generated with nucleus | electron
  · cases nucleus
    left
    dsimp only
    cases row.1.descriptor.source.element <;> norm_num [Charged.atomicNumber]
  · rcases List.mem_map.mp electron with ⟨orbital,_,rfl⟩
    exact Or.inr rfl

theorem target_node_present {cursor : CPS1ReactiveNuclear.SourceCursor frame} (source : Source cursor) :
    source.targetNode ∈ source.measurementNodes := by
  have particle : source.targetParticle.readout ∈ source.particles.map Particle.readout :=
    List.mem_map_of_mem (target_particle_present source)
  obtain ⟨ordinal,selected⟩ := List.getElem?_of_mem particle
  have indexed : (source.targetParticle.readout,ordinal) ∈ (source.particles.map Particle.readout).zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr selected
  have node := List.mem_map_of_mem (f := measuredNode source.targetAddress) indexed
  have measured : measuredNode source.targetAddress (source.targetParticle.readout,ordinal) = source.targetNode := by
    simp [Source.targetNode,Source.targetParticle,measuredNode,coordinate,line]
    rfl
  rw [measured] at node
  exact node

theorem measurement_signed {cursor : CPS1ReactiveNuclear.SourceCursor frame} (source : Source cursor)
    (node : Body.Node) (held : node ∈ source.measurementNodes)
    (different : node.particle.address ≠ source.targetAddress) :
    0 < (node.particle.charge : ℝ)*node.row.position (0 : Fin 3) := by
  rcases List.mem_map.mp held with ⟨row,indexed,rfl⟩
  have particle := List.fst_mem_of_mem_zipIdx indexed
  rcases List.mem_map.mp particle with ⟨owned,held,same⟩
  have sign : 0 < row.1.charge ∨ row.1.charge = -1 := by
    rw [← same]
    exact particle_signed source owned held
  change row.1.address ≠ source.targetAddress at different
  have ordinal : 0 < (row.2 : ℝ)+1 := by positivity
  rcases sign with positive | negative
  · have charge : 0 < (row.1.charge : ℝ) := by exact_mod_cast positive
    simp only [measuredNode,coordinate,if_neg different,if_pos positive,line_first]
    exact mul_pos charge ordinal
  · have nonpositive : ¬ 0 < row.1.charge := by rw [negative]; norm_num
    simp only [measuredNode,coordinate,if_neg different,if_neg nonpositive,line_first]
    simpa only [negative,Int.cast_neg,Int.cast_one,neg_mul,one_mul,neg_neg] using ordinal

theorem target_is_ammonia {cursor : CPS1ReactiveNuclear.SourceCursor frame} (source : Source cursor) :
    isAmmoniaNode source source.targetNode = true := by
  unfold isAmmoniaNode
  change (source.originAt? source.targetParticle.readout.address).any AtomOrigin.isAmmonia = true
  rw [source_origin_generated source source.targetParticle (target_particle_present source)]
  rfl

theorem chain_node_present {cursor : CPS1ReactiveNuclear.SourceCursor frame} (source : Source cursor) :
    ∃ node ∈ chainNodes source source.measurementNodes, node.particle.address ≠ source.targetAddress := by
  have backbone := Graph.backbone_present (CPS1LocalChemicalExecution.Actual.cps1 frame).word source.chain.bonds
    0 (by simp [CPS1ResourceExecution.Peptide.word]) "N" (Or.inr rfl)
  obtain ⟨atom,inGraph,_⟩ := (Graph.address_present_iff _ _).mp backbone
  obtain ⟨ordinal,selected⟩ := List.getElem?_of_mem inGraph
  have indexBound : ordinal < source.graph.atoms.length := (List.getElem?_eq_some_iff.mp selected).1
  change source.graph.atoms[ordinal]? = some atom at selected
  have indexed : (AtomOrigin.chain atom,ordinal) ∈ source.atoms.zipIdx := by
    rw [List.mk_mem_zipIdx_iff_getElem?]
    rw [Source.atoms,List.getElem?_append_left (by simpa only [List.length_map] using indexBound),List.getElem?_map,selected]
    rfl
  let particle : Particle cursor := ⟨.chain atom,⟨.nucleus ordinal,atom,(Charged.atomicNumber atom.source.element : Int)⟩⟩
  have paid : particle ∈ source.particles :=
    List.mem_flatMap.mpr ⟨_,indexed,List.mem_map.mpr ⟨_,List.mem_cons_self,rfl⟩⟩
  have readout : particle.readout ∈ source.particles.map Particle.readout := List.mem_map_of_mem paid
  obtain ⟨position,selectedReadout⟩ := List.getElem?_of_mem readout
  let node := measuredNode source.targetAddress (particle.readout,position)
  have held : node ∈ source.measurementNodes :=
    List.mem_map_of_mem (List.mk_mem_zipIdx_iff_getElem?.mpr selectedReadout)
  have origin : isAmmoniaNode source node = false := by
    unfold isAmmoniaNode
    change (source.originAt? particle.readout.address).any AtomOrigin.isAmmonia = false
    rw [source_origin_generated source particle paid]
    rfl
  refine ⟨node,List.mem_filter.mpr ⟨held,by simp [origin]⟩,?_⟩
  change Charged.Address.nucleus ordinal ≠ Charged.Address.nucleus source.graph.atoms.length
  exact fun equal => (Nat.ne_of_lt indexBound) (Charged.Address.nucleus.inj equal)

theorem measured_source_acts {cursor : CPS1ReactiveNuclear.SourceCursor frame} (source : Source cursor) :
    SourceActs source source.measurementNodes := by
  obtain ⟨other,held,different⟩ := chain_node_present source
  have fullHeld : other ∈ source.measurementNodes := (List.mem_filter.mp held).1
  have full : Body.force source.targetNode source.measurementNodes (0 : Fin 3) < 0 :=
    whole_source_force_negative _ _ (by norm_num [Source.targetNode,Source.targetParticle]) rfl
      (measurement_signed source) ⟨other,fullHeld,different⟩
  have chain : Body.force source.targetNode (chainNodes source source.measurementNodes) (0 : Fin 3) < 0 :=
    whole_source_force_negative _ _ (by norm_num [Source.targetNode,Source.targetParticle]) rfl
      (fun node present different => measurement_signed source node (List.mem_filter.mp present).1 different)
      ⟨other,held,different⟩
  refine ⟨source.targetNode,target_node_present source,target_is_ammonia source,?_,?_⟩
  · rw [chain_force_whole]
    intro zero
    have := congrArg (fun point : Body.Point => point (0 : Fin 3)) zero
    simp only [this,PiLp.zero_apply,lt_self_iff_false] at chain
  · intro zero
    have := congrArg (fun point : Body.Point => point (0 : Fin 3)) zero
    simp only [this,PiLp.zero_apply,lt_self_iff_false] at full

end
end CPS1SameEventFunction.Classical
