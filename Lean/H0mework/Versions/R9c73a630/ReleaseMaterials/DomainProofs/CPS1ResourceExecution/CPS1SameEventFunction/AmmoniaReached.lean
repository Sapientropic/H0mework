import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.AmmoniaCurrent

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing CPS1BiologicalUpdate
variable {frame : CPS1Recycling.Frame}

theorem old_residual_ammonia (current : CPS1ReactiveField.Occurrence frame) :
    (CPS1ReactiveField.oldResidual current).count (deformedNH3 frame) =
      current.old.current.stock.count (deformedNH3 frame) := by
  unfold CPS1ReactiveField.oldResidual
  split
  · rfl
  · exact List.count_erase_of_ne (by simp [deformedNH3])

theorem reached_live_stock {entry : CPS1ReactiveSourceEntry.Entry frame} {depth : Nat}
    (outcome : BirthRun entry depth) :
    CPS1ReactiveField.liveStock (reachedCursor outcome).native.current =
      CPS1ReactiveField.liveStock (entryCursor entry).native.current := by
  cases outcome with
  | residual cursor failure actual => cases actual; simp only [reachedCursor,entryCursor]
  | fired entered actual run =>
    cases actual
    simpa only [reachedCursor,entryCursor] using physical_run_live_stock entered depth run

theorem ammonia_at_of_live {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (material : CPS1ReactiveField.LiveMaterial frame) (held : material ∈ LiveStock cursor)
    (read : CPS1BiologicalUpdate.liveLocal? material = some (localNH3 frame)) :
    (ammoniaAt? cursor).isSome := by
  obtain ⟨index,bound,atIndex⟩ := List.getElem_of_mem held
  let slot : Fin (LiveStock cursor).length := ⟨index,bound⟩
  have readSlot : CPS1BiologicalUpdate.liveLocal? ((LiveStock cursor).get slot) =
      some (CPS1LocalChemicalExecution.molecule frame .ammonia) := by
    rw [List.get_eq_getElem,atIndex]
    exact read
  have found : ((List.finRange (LiveStock cursor).length).find?
      (fun slot => decide (CPS1BiologicalUpdate.liveLocal? ((LiveStock cursor).get slot) =
        some (CPS1LocalChemicalExecution.molecule frame .ammonia)))).isSome := by
    apply List.find?_isSome.mpr
    exact ⟨slot,List.mem_finRange _,decide_eq_true readSlot⟩
  unfold ammoniaAt?
  split
  · rename_i selected
    rw [selected] at found
    cases found
  · rfl

theorem returned_ammonia {before : CPS1ReactiveNuclear.SourceCursor frame}
    {water : Nat} {raw : List RawSupply} {path : CPS1Recycling.SplitSite} {depth : Nat}
    (event : NativeBiosyntheticEvent before water raw path [] [] noPhysicalSupply depth)
    (input : 0 < (liveResources before.native.current).count .ammonia) :
    (ammoniaAt? event.reached).isSome := by
  have native := actual_translation_ammonia_retained event.physicalEvent.seed.translation
  have count := physical_event_ammonia event.physicalEvent
  have positive : 0 < event.physicalEvent.deformation.current.stock.count
      (deformedNH3 event.physicalEvent.seed.translation.generatedFrame) := by
    rw [count]
    exact lt_of_lt_of_le input native
  let initial := CPS1ReactiveField.next (CPS1ReactiveField.start event.physicalEvent.deformation) [] [] []
  have initialHeld : CPS1ReactiveField.LiveMaterial.old (deformedNH3 event.physicalEvent.seed.translation.generatedFrame) ∈
      CPS1ReactiveField.liveStock initial := by
    apply List.mem_append_left _
    apply List.mem_map_of_mem
    apply List.count_pos_iff.mp
    rw [old_residual_ammonia]
    exact positive
  have entry := congrArg (fun value : CPS1ReactiveSourceEntry.Entry event.physicalEvent.seed.translation.generatedFrame =>
    CPS1ReactiveField.liveStock (entryCursor value).native.current) event.physicalEvent.actualEntry
  rw [initial_entry_current] at entry
  have reached := reached_live_stock event.outcome
  rw [entry] at reached
  have actualStock : LiveStock event.reached = CPS1ReactiveField.liveStock initial := reached
  apply ammonia_at_of_live (.old (deformedNH3 event.physicalEvent.seed.translation.generatedFrame))
  · rw [actualStock]
    exact initialHeld
  · rfl

end
end CPS1SameEventFunction
