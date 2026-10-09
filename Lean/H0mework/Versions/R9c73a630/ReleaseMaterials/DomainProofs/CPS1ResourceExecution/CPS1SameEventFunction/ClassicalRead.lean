import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.ClassicalResponded

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction.Classical
noncomputable section
open CPS1AtomicDynamics
variable {frame : CPS1Recycling.Frame}

def actualResponseRow {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Source cursor) (nodes : List Body.Node) (time : ℝ) (node : Body.Node) : ResponseRow cursor :=
  ⟨source.originAt? node.particle.address,node.particle,time • Body.force node nodes,time • chainForce source nodes node⟩

theorem actual_after_read {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Source cursor) (nodes : List Body.Node) (time : ℝ) :
    readResponse source nodes (nodes.map (fun node => Body.kick node nodes time)) time =
      nodes.map (actualResponseRow source nodes time) := by
  unfold readResponse
  have pairs := List.zip_map' (f := id) (g := fun node => Body.kick node nodes time) (l := nodes)
  simp only [List.map_id] at pairs
  rw [pairs,List.map_map]
  apply List.map_congr_left
  intro node _
  dsimp only [Function.comp_def,Prod.map,Prod.fst,Prod.snd,id_eq,actualResponseRow]
  have total : (Body.kick node nodes time).row.momentum-node.row.momentum = time • Body.force node nodes := by
    simp only [Body.kick]
    abel
  rw [total]
  simp only [chainForce,smul_sub]

theorem independent_actual_response {cursor : CPS1ReactiveNuclear.SourceCursor frame} {raw : Raw}
    (before : Current cursor raw) (time : ℝ) (step : NativeStep before time) :
    ∃ row ∈ readResponse before.packet.source before.nodes step.next.nodes time,
      row.origin.any AtomOrigin.isAmmonia = true ∧ row.chain ≠ 0 ∧ row.total ≠ 0 := by
  obtain ⟨node,held,ammonia,chain,total⟩ := step.acted
  rw [step.nodes,actual_after_read]
  refine ⟨actualResponseRow before.packet.source before.nodes time node,List.mem_map_of_mem held,ammonia,?_,?_⟩
  · exact smul_ne_zero (ne_of_gt step.elapsed) chain
  · exact smul_ne_zero (ne_of_gt step.elapsed) total

end
end CPS1SameEventFunction.Classical
