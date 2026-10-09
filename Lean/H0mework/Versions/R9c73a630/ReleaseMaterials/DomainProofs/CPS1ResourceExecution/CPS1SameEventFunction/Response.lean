import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.Dynamics

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction
noncomputable section
open CPS1AtomicDynamics CPS1ReactiveField.Carried
variable {frame : CPS1Recycling.Frame}

structure ResponseRow where
  source : Charged.Particle
  originalImpulse : Body.Point
  chainImpulse : Body.Point
  actualImpulse : Body.Point

def readResponse {root : CPS1Deformation.Source.Occurrence frame} {state : Snapshot}
    (germ : CPS1ReactiveNuclear.Germ root state) (before after : List Body.Node) (time : ℝ) : List ResponseRow :=
  (before.zip after).map (fun row =>
    ⟨row.1.particle,independentImpulse row.1 row.2 before time,
      independentChainImpulse germ row.1 row.2 before time,row.2.row.momentum-row.1.row.momentum⟩)

private theorem read_generated_response {root : CPS1Deformation.Source.Occurrence frame} {state : Snapshot}
    (germ : CPS1ReactiveNuclear.Germ root state) (nodes selected : List Body.Node) (time : ℝ) :
    ((selected.zip (selected.map (sourceKick state nodes time))).map (fun row =>
      (⟨row.1.particle,independentImpulse row.1 row.2 nodes time,
        independentChainImpulse germ row.1 row.2 nodes time,row.2.row.momentum-row.1.row.momentum⟩ : ResponseRow))) =
      selected.map (fun node =>
        (⟨node.particle,time • externalForce state node,time • chainForce germ node,
          time • sourceForce state nodes node⟩ : ResponseRow)) := by
  induction selected with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.map_cons,List.zip_cons_cons,independent_response_generated,chain_response_generated,
      List.cons.injEq]
    constructor
    · congr 1
      simp only [sourceKick,Coulomb.nextP]
      abel
    · exact ih

theorem actual_independent_response {cursor : CPS1ReactiveNuclear.SourceCursor frame} {raw : Raw}
    (before : Current cursor raw) (time : ℝ) (step : NativeStep before time) :
    readResponse before.packet.source.germ before.nodes step.next.nodes time =
      before.nodes.map (fun node =>
        ⟨node.particle,time • externalForce before.packet.source.active.fields node,
          time • chainForce before.packet.source.germ node,
          time • sourceForce before.packet.source.active.fields before.nodes node⟩) := by
  rw [step.nodes]
  exact read_generated_response before.packet.source.germ before.nodes before.nodes time

theorem independent_response_has_actual_effect {cursor : CPS1ReactiveNuclear.SourceCursor frame} {raw : Raw}
    (before : Current cursor raw) (time : ℝ) (step : NativeStep before time) :
    ∃ row ∈ readResponse before.packet.source.germ before.nodes step.next.nodes time,
      row.chainImpulse ≠ 0 ∧ row.originalImpulse ≠ 0 ∧ row.actualImpulse ≠ 0 := by
  rcases step.acted with ⟨node,held,chain,full,net⟩
  rw [actual_independent_response]
  refine ⟨_,List.mem_map_of_mem held,?_,?_,?_⟩
  · exact smul_ne_zero (ne_of_gt step.elapsed) chain
  · exact smul_ne_zero (ne_of_gt step.elapsed) full
  · exact smul_ne_zero (ne_of_gt step.elapsed) net

theorem actual_source_energy_consumer {cursor : CPS1ReactiveNuclear.SourceCursor frame} {raw : Raw}
    (before : Current cursor raw) (time : ℝ) (step : NativeStep before time)
    (node : Body.Node) (held : node ∈ before.nodes) (axis : Fin 3) :
    HasDerivAt (fun duration : ℝ => externalEnergy before.packet.source.active.fields
      (node.particle.charge : ℝ) ((fun coordinate => node.row.position coordinate)+duration • Pi.single axis 1))
      (-(externalForce before.packet.source.active.fields node axis)) 0 := by
  apply source_energy_direction
  have separated := List.pairwise_append.mp step.currentReady
  intro old member
  exact Ne.symm (separated.2.2 old member node held)

end
end CPS1SameEventFunction
