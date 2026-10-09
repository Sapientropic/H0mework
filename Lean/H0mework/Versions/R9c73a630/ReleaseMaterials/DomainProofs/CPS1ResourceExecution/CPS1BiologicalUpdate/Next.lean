import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.CurrentGenome

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace CPS1BiologicalUpdate
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing CPS1ReactiveSourceEntry
variable {frame : CPS1Recycling.Frame}

theorem consume_execute_translated (before : CPS1ReactiveNuclear.SourceCursor frame)
    (water : Nat) (raw : List RawSupply) (path : CPS1Recycling.SplitSite)
    (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial)
    (physical : PhysicalRaw) (depth : Nat) (translation : TranslationEvent before.native.current water raw)
    (selected : translateLive before.native.current water raw = .translated translation) :
    consumeWhole (executeWhole before water raw path events feed physical depth) =
      .produced (nativeBiosyntheticEvent before water raw path events feed physical depth
        (physicalEvent before water raw path events feed physical
          (sourceSeed before.native.current water raw path events feed translation))
        (runBirth (physicalEvent before water raw path events feed physical
          (sourceSeed before.native.current water raw path events feed translation)).entry depth)) := by
  let returned := physicalEvent before water raw path events feed physical
    (sourceSeed before.native.current water raw path events feed translation)
  have generated : wholeUpdate before water raw path events feed physical = .generated returned := by
    unfold wholeUpdate generateSource
    rw [selected]
  have emitted := execute_whole_generated before water raw path events feed physical depth returned generated
  have recognise : ∀ whole : WholeRun before water raw path events feed physical depth,
      whole.event = .generated returned → HEq whole.next (runBirth returned.entry depth) →
      consumeWhole whole = .produced
        (nativeBiosyntheticEvent before water raw path events feed physical depth returned (runBirth returned.entry depth)) := by
    rintro ⟨original,originalSource,event,next,actual⟩ same nextSame
    cases same
    cases (eq_of_heq nextSame)
    rfl
  exact recognise _ emitted.1 emitted.2

theorem reached_old_source {entry : Entry frame} {depth : Nat} (outcome : BirthRun entry depth) :
    (reachedCursor outcome).native.current.old = (entryCursor entry).native.current.old := by
  cases outcome with
  | residual cursor failure actual => cases actual; simp only [reachedCursor,entryCursor]
  | fired entered actual run =>
    cases actual
    have whole := CPS1ReactiveJointNuclear.renew_whole entered.cursor depth
    rw [run.actual] at whole
    simpa only [reachedCursor,entryCursor] using whole.1

theorem physical_event_editing {before : CPS1ReactiveNuclear.SourceCursor frame}
    {water : Nat} {raw : List RawSupply} {path : CPS1Recycling.SplitSite}
    {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial} {physical : PhysicalRaw}
    (event : PhysicalEvent before water raw path events feed physical) :
    (CPS1ReactiveField.editingSource event.deformation).editing = event.seed.translation.genomic.event.result := by
  have deformation := congrArg CPS1Deformation.Source.Occurrence.previous event.deformationSource
  have molecular := congrArg CPS1MolecularFrame.Source.Occurrence.previous event.molecularSource
  have following := congrArg CPS1Following.Source.Occurrence.previous event.followingSource
  have nuclear := congrArg CPS1QuantumNuclear.Source.Occurrence.previous event.nuclearSource
  have electronic := congrArg CPS1ElectronicSource.Source.Occurrence.previous event.electronicSource
  have bath := congrArg CPS1EnzymeBath.Source.Occurrence.previous event.bathSource
  have atomic := congrArg CPS1AtomicDynamics.Source.Occurrence.previous event.atomicSource
  have atomized := congrArg CPS1AtomicSource.Current.Occurrence.previous event.seed.actualAtomic
  change event.deformation.previous = event.molecular at deformation
  change event.molecular.previous = event.following at molecular
  change event.following.previous = event.nuclear at following
  change event.nuclear.previous = event.electronic at nuclear
  change event.electronic.previous = event.bath at electronic
  change event.bath.previous = event.atomic at bath
  change event.atomic.previous = event.seed.atomic at atomic
  change event.seed.atomic.previous = event.seed.joined at atomized
  unfold CPS1ReactiveField.editingSource
  rw [deformation,molecular,following,nuclear,electronic,bath,atomic,atomized]
  exact event.seed.currentEditing

theorem reached_editing_source {before : CPS1ReactiveNuclear.SourceCursor frame}
    {water : Nat} {raw : List RawSupply} {path : CPS1Recycling.SplitSite}
    {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
    {physical : PhysicalRaw} {depth : Nat}
    (event : NativeBiosyntheticEvent before water raw path events feed physical depth) :
    (CPS1ReactiveField.editingSource event.reached.native.current.old).editing =
      event.physicalEvent.seed.translation.genomic.event.result := by
  have reached := reached_old_source event.outcome
  have entry := congrArg (fun value : Entry event.physicalEvent.seed.translation.generatedFrame =>
    (entryCursor value).native.current.old) event.physicalEvent.actualEntry
  have initial := congrArg (fun value => value.old)
    (initial_entry_current event.physicalEvent.deformation physical.actions physical.feed physical.rows)
  have old : event.reached.native.current.old = event.physicalEvent.deformation :=
    reached.trans (entry.trans initial)
  rw [old]
  exact physical_event_editing event.physicalEvent

end
end CPS1BiologicalUpdate
