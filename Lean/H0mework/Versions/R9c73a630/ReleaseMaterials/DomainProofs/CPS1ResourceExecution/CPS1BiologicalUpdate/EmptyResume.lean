import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.Next

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace CPS1BiologicalUpdate
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing CPS1Deamination CPS1Deamination.ExecutionReadout
variable {frame : CPS1Recycling.Frame}

private theorem empty_saved_suffix (current : CPS1ReactiveField.Occurrence frame)
    (word : List Base) (actualDNA : readDNA (liveResources current) = some word)
    (empty : (CPS1ReactiveField.editingSource current.old).editing.remaining = []) :
    ∃ source, savedSuffix current = .ok source := by
  unfold savedSuffix
  split
  · rename_i absent
    rw [actualDNA] at absent
    cases absent
  · split
    · rename_i failure cut
      rw [empty] at cut
      cases cut
    · exact ⟨_,rfl⟩

private theorem empty_genomic_selected (current : CPS1ReactiveField.Occurrence frame)
    (word : List Base) (actualDNA : readDNA (liveResources current) = some word)
    (empty : (CPS1ReactiveField.editingSource current.old).editing.remaining = []) :
    ∃ event, genomicUpdate current 0 = .updated event := by
  obtain ⟨source,selected⟩ := empty_saved_suffix current word actualDNA empty
  unfold genomicUpdate
  rw [selected]
  exact ⟨_,rfl⟩

theorem empty_resume_actual_stock (current : CPS1ReactiveField.Occurrence frame)
    (event : VerifiedResume current 0)
    (empty : (CPS1ReactiveField.editingSource current.old).editing.remaining = []) :
    event.event.result.stock = liveResources current ∧ event.event.dna = readDNA (liveResources current) := by
  have stock : event.event.result.stock = liveResources current := by
    rw [event.event.actual,event.event.savedSource,empty]
    simp only [execute,Inventory.execute,Continuation.refillWater,List.replicate_zero,List.append_nil]
    exact event.event.slice.native
  exact ⟨stock,event.event.dnaActual.trans (congrArg readDNA stock)⟩

-- The next decoding is read from the actual reached inventory and the completed stored suffix.
theorem next_translation_from_complete_source {before : CPS1ReactiveNuclear.SourceCursor frame}
    {water : Nat} {raw : List RawSupply} {path : CPS1Recycling.SplitSite} {depth : Nat}
    (event : NativeBiosyntheticEvent before water raw path [] [] noPhysicalSupply depth)
    (supply : List RawSupply)
    (complete : event.physicalEvent.seed.translation.genomic.event.result.remaining = []) :
    ∃ next : TranslationEvent event.reached.native.current 0 supply,
      translateLive event.reached.native.current 0 supply = .translated next ∧
      next.coding = event.physicalEvent.seed.translation.coding ∧
      next.peptide = event.physicalEvent.seed.translation.peptide := by
  let prior := event.physicalEvent.seed.translation
  have empty : (CPS1ReactiveField.editingSource event.reached.native.current.old).editing.remaining = [] := by
    rw [reached_editing_source event]
    exact complete
  have dna : readDNA (liveResources event.reached.native.current) = prior.genomic.event.dna :=
    reached_native_genome event
  have hasDNA := dna.trans prior.genomic.dna
  obtain ⟨genomic,selected⟩ := empty_genomic_selected event.reached.native.current _ hasDNA empty
  have resumed := (empty_resume_actual_stock event.reached.native.current genomic empty).2
  have sameCoding : genomic.event.coding = some prior.coding := by
    rw [genomic.event.codingActual,resumed,dna]
    exact prior.genomic.event.codingActual.symm.trans prior.codingSource
  have samePeptide : genomic.event.peptide = some prior.peptide := by
    rw [genomic.event.peptideActual]
    have codingSame : genomic.event.coding = prior.genomic.event.coding :=
      sameCoding.trans prior.codingSource.symm
    rw [codingSame]
    exact prior.genomic.event.peptideActual.symm.trans prior.peptideSource
  unfold translateLive
  rw [selected]
  dsimp only
  split
  · rename_i absent
    have impossible := sameCoding.symm.trans absent
    cases impossible
  · rename_i coding found
    have codingEq : coding = prior.coding := Option.some.inj (found.symm.trans sameCoding)
    split
    · rename_i absent
      have impossible := samePeptide.symm.trans absent
      cases impossible
    · rename_i peptide foundPeptide
      have peptideEq : peptide = prior.peptide := Option.some.inj (foundPeptide.symm.trans samePeptide)
      split
      · exact ⟨_,rfl,codingEq,peptideEq⟩
      · rename_i notMethionine
        exact False.elim (notMethionine (peptideEq ▸ prior.initiator))

end
end CPS1BiologicalUpdate
