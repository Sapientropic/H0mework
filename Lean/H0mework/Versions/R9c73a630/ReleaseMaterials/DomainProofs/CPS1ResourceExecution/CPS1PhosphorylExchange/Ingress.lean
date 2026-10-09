import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PhosphorylExchange.Native

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1PhosphorylExchange
noncomputable section
open CPS1AtomicDynamics CPS1AtomicSource CPS1SameEventFunction
variable {frame : CPS1Recycling.Frame}

theorem paid_chain_slot_exists {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) :
    ∃ slot, chainSlot? source = some slot ∧
      Classical.ownedLive? ((LiveStock cursor).get slot) = some source.owned := by
  classical
  have owner : source.owned ∈ (LiveStock cursor).filterMap Classical.ownedLive? :=
    List.mem_of_head? source.ownership
  obtain ⟨material,held,paid⟩ := List.mem_filterMap.mp owner
  obtain ⟨slot,actual⟩ := List.mem_iff_get.mp held
  have witness : ∃ slot ∈ List.finRange (LiveStock cursor).length,
      decide (Classical.ownedLive? ((LiveStock cursor).get slot) = some source.owned) = true := by
    refine ⟨slot,List.mem_finRange slot,?_⟩
    simp only [actual,paid,decide_true]
  have nonempty := List.find?_isSome.mpr witness
  cases found : (List.finRange (LiveStock cursor).length).find?
      (fun slot => decide (Classical.ownedLive? ((LiveStock cursor).get slot) = some source.owned)) with
  | none => rw [found] at nonempty; cases nonempty
  | some slot =>
    refine ⟨slot,found,?_⟩
    exact of_decide_eq_true (List.find?_some
      (p := fun index => decide (Classical.ownedLive? ((LiveStock cursor).get index) = some source.owned)) found)

theorem local_ammonia_not_paid_chain (material : CPS1ReactiveField.LiveMaterial frame)
    (decoded : CPS1BiologicalUpdate.liveLocal? material =
      some (CPS1LocalChemicalExecution.molecule frame .ammonia)) :
    Classical.ownedLive? material = none := by
  unfold CPS1BiologicalUpdate.liveLocal? at decoded
  split at decoded
  · rfl
  · rfl
  · cases decoded

theorem paid_chain_slot_distinct {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (slot : Fin (LiveStock cursor).length)
    (paid : Classical.ownedLive? ((LiveStock cursor).get slot) = some source.owned) :
    slot ≠ source.ammonia.slot := by
  intro same
  subst slot
  have absent := local_ammonia_not_paid_chain _ source.ammonia.species
  rw [absent] at paid
  cases paid

theorem actual_responded_before {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {raw : Classical.Raw} (before : Classical.Current cursor raw)
    (step : Classical.NativeStep before raw.time)
    (actual : Classical.fromCursor cursor raw = .responded before step) :
    before.nodes = before.packet.nodes := by
  unfold Classical.fromCursor at actual
  split at actual
  · cases actual
  · dsimp only at actual
    split at actual
    · cases actual
    · cases actual
      rfl

theorem actual_responded_post_source {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {raw : Classical.Raw} (before : Classical.Current cursor raw)
    (step : Classical.NativeStep before raw.time)
    (actual : Classical.fromCursor cursor raw = .responded before step) :
    step.next.nodes.map Body.Node.particle = before.packet.source.particles.map Classical.Particle.readout ∧
      (step.next.nodes.map (fun node => node.particle.address)).Nodup ∧
      ∀ node ∈ step.next.nodes, 0 < node.row.inertia := by
  have start := actual_responded_before before step actual
  have whole := Classical.actual_source_whole before.packet
  have particles := (Classical.next_source_accounted before raw.time step).2.2
  rw [start,whole.1] at particles
  refine ⟨particles,?_,?_⟩
  · have addresses := congrArg (List.map Charged.Particle.address) particles
    simp only [List.map_map,Function.comp_def] at addresses
    rw [addresses]
    exact Classical.source_global_addresses_unique before.packet.source
  · intro node held
    rw [step.nodes] at held
    obtain ⟨prior,priorHeld,same⟩ := List.mem_map.mp held
    subst node
    have inertia := (Body.gather_source _ _ _ before.packet.actual).2 prior
    rw [← start] at inertia
    exact (inertia priorHeld).1

theorem measured_post_unit_inertia {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (empty : source.owned.chainRows = []) (reserve time : ℝ)
    (step : Classical.NativeStep (Classical.measurementCurrent source empty reserve time) time) :
    ∀ node ∈ step.next.nodes, node.row.inertia = 1 := by
  intro node held
  rw [step.nodes] at held
  obtain ⟨prior,priorHeld,same⟩ := List.mem_map.mp held
  subst node
  change prior.row.inertia = 1
  change prior ∈ source.measurementNodes at priorHeld
  obtain ⟨row,_,same⟩ := List.mem_map.mp priorHeld
  subst prior
  rfl

end
end CPS1PhosphorylExchange
