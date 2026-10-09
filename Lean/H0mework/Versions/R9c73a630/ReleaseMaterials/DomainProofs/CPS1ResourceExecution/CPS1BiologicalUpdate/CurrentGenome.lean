import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.SourceGenome

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace CPS1BiologicalUpdate
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing CPS1ReactiveSourceEntry
open CPS1Deamination.ExecutionReadout
variable {frame : CPS1Recycling.Frame}

private theorem old_dna_reader (item : CPS1Deformation.Species frame) :
    (liveResource? (.old item)).bind nativeDNA? = deformedDNA? item := by
  cases item
  repeat first
    | rfl
    | (rename_i inherited; cases inherited)

theorem old_residual_genome (current : CPS1ReactiveField.Occurrence frame) :
    (CPS1ReactiveField.oldResidual current).filterMap deformedDNA? =
      current.old.current.stock.filterMap deformedDNA? := by
  unfold CPS1ReactiveField.oldResidual
  split
  · rfl
  · exact CPS1AtomicSource.Contract.filterMap_erase_none deformedDNA? _ _ rfl

theorem empty_fresh_stock (old : CPS1Deformation.Source.Occurrence frame) :
    (CPS1ReactiveField.next (CPS1ReactiveField.start old) [] [] []).ingress.atomic.source.stock =
      (CPS1ReactiveField.enzymeView old).map CPS1AddressedChemicalReaction.Material.inherited := by
  change (CPS1AddressedChemicalReaction.Source.next
    (CPS1AddressedChemicalReaction.Source.start (CPS1ReactiveField.freshIngress old)) [] []).stock = _
  simp only [CPS1AddressedChemicalReaction.Source.next,CPS1AddressedChemicalReaction.Source.execution,
    CPS1AddressedChemicalReaction.Source.requestedProgram,CPS1AddressedChemicalReaction.Source.available,
    CPS1AddressedChemicalReaction.Source.packet,CPS1AddressedChemicalReaction.Source.start,
    CPS1ReactiveField.freshIngress,CPS1LocalChemicalExecution.Source.localProgram,
    List.map_nil,List.flatMap_nil,List.nil_append,List.append_nil,
    CPS1AddressedChemicalReaction.rawPacket,List.zipIdx_nil,CPS1AddressedChemicalReaction.run_nil]

theorem initial_empty_live_dna (old : CPS1Deformation.Source.Occurrence frame) :
    readDNA (liveResources (CPS1ReactiveField.next (CPS1ReactiveField.start old) [] [] [])) =
      (old.current.stock.filterMap deformedDNA?).head? := by
  let current := CPS1ReactiveField.next (CPS1ReactiveField.start old) [] [] []
  have oldStock := old_residual_genome current
  have freshStock := empty_fresh_stock old
  change ((CPS1ReactiveField.liveStock current).filterMap liveResource? |>.filterMap nativeDNA?).head? = _
  rw [List.filterMap_filterMap]
  unfold CPS1ReactiveField.liveStock
  rw [List.filterMap_append,List.filterMap_map,List.filterMap_map]
  simp only [Function.comp_def,old_dna_reader]
  rw [oldStock]
  change ((old.current.stock.filterMap deformedDNA?) ++
    current.ingress.atomic.source.stock.filterMap
      (fun item => (liveResource? (.reactive item)).bind nativeDNA?)).head? = _
  rw [freshStock]
  have fresh : ((CPS1ReactiveField.enzymeView old).map
      CPS1AddressedChemicalReaction.Material.inherited).filterMap
      (fun item => (liveResource? (.reactive item)).bind nativeDNA?) = [] := by
    unfold CPS1ReactiveField.enzymeView
    split <;> rfl
  rw [fresh,List.append_nil]

theorem translation_genome_read {current : CPS1ReactiveField.Occurrence frame} {water : Nat}
    {raw : List RawSupply} (event : TranslationEvent current water raw) :
    readDNA event.native.stock = event.genomic.event.dna := by
  rw [event.actual,event.programSource,native_translation_preserves_genome,event.availableSource]
  have rawNone : (raw.map RawSupply.species).filterMap nativeDNA? = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro item member
    rcases List.mem_map.mp member with ⟨supply,held,rfl⟩
    cases supply <;> rfl
  change ((event.genomic.event.result.stock ++ raw.map RawSupply.species).filterMap nativeDNA?).head? = _
  rw [List.filterMap_append,rawNone,List.append_nil]
  exact event.genomic.event.dnaActual.symm

theorem reached_native_genome {before : CPS1ReactiveNuclear.SourceCursor frame}
    {water : Nat} {raw : List RawSupply} {path : CPS1Recycling.SplitSite} {depth : Nat}
    (event : NativeBiosyntheticEvent before water raw path [] [] noPhysicalSupply depth) :
    readDNA (liveResources event.reached.native.current) = event.physicalEvent.seed.translation.genomic.event.dna := by
  have reached := reached_genome_read event.outcome
  have entry := congrArg (fun value : Entry event.physicalEvent.seed.translation.generatedFrame =>
    readDNA (liveResources (entryCursor value).native.current)) event.physicalEvent.actualEntry
  have initial := initial_entry_current event.physicalEvent.deformation [] [] []
  have initialRead := congrArg (fun value => readDNA (liveResources value)) initial
  have stock := congrArg List.head? (physical_event_genome event.physicalEvent)
  exact reached.trans (entry.trans (initialRead.trans ((initial_empty_live_dna event.physicalEvent.deformation).trans
    (stock.trans (translation_genome_read event.physicalEvent.seed.translation)))))

end
end CPS1BiologicalUpdate
