import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LiveEditing.Consumers

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1LiveEditing
noncomputable section
open CPS1ResourceExecution CPS1Deamination CPS1Deamination.ExecutionReadout
open CPS1ReactiveSourceEntry
variable {frame : CPS1Recycling.Frame}

def BirthRun.Law {entry : Entry frame} {depth : Nat} (returned : BirthRun entry depth) : Prop :=
  match returned with
  | .residual cursor failure _ => entry = .residual cursor failure
  | .fired entered _ run =>
    entry = .admitted entered ∧
    CPS1ReactiveJointNuclear.renew entered.cursor depth = ⟨run.after.cursor,run.pulses,0,none⟩ ∧
    run.pulses.length = depth ∧ ∀ pulse ∈ run.pulses, pulse.Valid

theorem birth_data_law {entry : Entry frame} {depth : Nat} (returned : BirthRun entry depth) : returned.Law := by
  cases returned with
  | residual cursor failure actual => exact actual
  | fired entered actual run =>
    have finite := CPS1ReactiveJointNuclear.renew_ready entered.cursor depth entered.ready
    have whole := CPS1ReactiveJointNuclear.renew_whole entered.cursor depth
    rw [run.actual] at finite whole
    exact ⟨actual,run.actual,finite.2.2.1,whole.2.2.2.2.2⟩

def WholeDisposition.NextLaw {before : CPS1ReactiveNuclear.SourceCursor frame}
    {water : Nat} {raw : List RawSupply} {path : CPS1Recycling.SplitSite}
    {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial} {physical : PhysicalRaw}
    {depth : Nat} (event : WholeDisposition before water raw path events feed physical)
    (next : match event with | .rejected _ => PUnit | .generated returned => BirthRun returned.entry depth) : Prop :=
  match event, next with
  | .rejected _, _ => True
  | .generated _, run => run.Law

theorem execute_whole_next_law (before : CPS1ReactiveNuclear.SourceCursor frame)
    (water : Nat) (raw : List RawSupply) (path : CPS1Recycling.SplitSite)
    (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial)
    (physical : PhysicalRaw) (depth : Nat) :
    let returned := executeWhole before water raw path events feed physical depth
    WholeDisposition.NextLaw (depth := depth) returned.event returned.next := by
  let returned := executeWhole before water raw path events feed physical depth
  change WholeDisposition.NextLaw (depth := depth) returned.event returned.next
  rcases returned with ⟨original,originalSource,event,next,actual⟩
  cases event with
  | rejected original => exact True.intro
  | generated event => exact birth_data_law next

theorem whole_update_source_selected (before : CPS1ReactiveNuclear.SourceCursor frame)
    (water : Nat) (raw : List RawSupply) (path : CPS1Recycling.SplitSite)
    (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial) (physical : PhysicalRaw) :
    match wholeUpdate before water raw path events feed physical with
    | .rejected original => generateSource before.native.current water raw path events feed = original
    | .generated returned =>
      ∃ translation, translateLive before.native.current water raw = .translated translation ∧
        returned = physicalEvent before water raw path events feed physical
          (sourceSeed before.native.current water raw path events feed translation) := by
  unfold wholeUpdate generateSource
  cases selected : translateLive before.native.current water raw with
  | genomicRejected original => rfl
  | decodingRejected genomic unspent source failure => rfl
  | translated translation => exact ⟨translation,rfl,rfl⟩

theorem whole_update_carrier (before : CPS1ReactiveNuclear.SourceCursor frame)
    (water : Nat) (raw : List RawSupply) (path : CPS1Recycling.SplitSite)
    (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial) (physical : PhysicalRaw) :
    match wholeUpdate before water raw path events feed physical with
    | .rejected original => generateSource before.native.current water raw path events feed = original
    | .generated returned =>
      (CPS1ReactiveField.liveStock before.native.current).Perm
        (returned.seed.translation.genomic.event.slice.selected ++ returned.remainder) ∧
      returned.seed.translation.genomic.event.saved =
        (CPS1ReactiveField.editingSource before.native.current.old).editing.remaining ∧
      returned.seed.translation.genomic.event.result.stock.count .ammonia =
        (liveResources before.native.current).count .ammonia +
          returned.seed.translation.genomic.event.result.fired.length ∧
      returned.seed.translation.genomic.event.result.stock.count .water +
        returned.seed.translation.genomic.event.result.fired.length =
          (liveResources before.native.current).count .water + water ∧
      (returned.seed.translation.available ++ credit returned.seed.translation.native.fired).Perm
        (returned.seed.translation.native.stock ++ debit returned.seed.translation.native.fired) ∧
      returned.seed.translation.generatedFrame.native = returned.seed.translation.native ∧
      returned.seed.recycled = CPS1Recycling.run returned.seed.translation.generatedFrame events feed ∧
      returned.seed.joined.current = returned.seed.captured.current ∧
      returned.seed.joined.editing = returned.seed.translation.genomic.event.result ∧
      returned.entry = enterFromOld returned.deformation physical.actions physical.feed physical.rows ∧
      ∀ material : CPS1ReactiveField.Material
        (CPS1ReactiveField.next (CPS1ReactiveField.start returned.deformation)
          physical.actions physical.feed physical.rows), OriginalRows material := by
  have selected := whole_update_source_selected before water raw path events feed physical
  cases actual : wholeUpdate before water raw path events feed physical with
  | rejected original =>
    simp only [actual] at selected
    exact selected
  | generated returned =>
    dsimp only
    refine ⟨?_,returned.seed.translation.genomic.event.savedSource,
      returned.seed.translation.genomic.ammonia,returned.seed.translation.genomic.waterBalance,
      returned.seed.translation.whole,?_,returned.seed.actualRecycling,returned.seed.noReload,
      returned.seed.currentEditing,returned.actualEntry,?_⟩
    · rw [returned.remainderSource]
      exact returned.seed.wholeInput
    · rw [returned.seed.translation.frameSource]
    · intro material
      exact physical_original_rows before water raw path events feed physical returned material

theorem execute_whole_generated (before : CPS1ReactiveNuclear.SourceCursor frame)
    (water : Nat) (raw : List RawSupply) (path : CPS1Recycling.SplitSite)
    (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial)
    (physical : PhysicalRaw) (depth : Nat)
    (returned : PhysicalEvent before water raw path events feed physical)
    (selected : wholeUpdate before water raw path events feed physical = .generated returned) :
    (executeWhole before water raw path events feed physical depth).event = .generated returned ∧
    HEq (executeWhole before water raw path events feed physical depth).next (runBirth returned.entry depth) := by
  have recognise : ∀ event : WholeDisposition before water raw path events feed physical,
      event = .generated returned →
      HEq ((match event with
        | .rejected _ => PUnit.unit
        | .generated found => runBirth found.entry depth) :
        match event with
        | .rejected _ => PUnit
        | .generated found => BirthRun found.entry depth) (runBirth returned.entry depth) := by
    intro event same
    cases same
    exact HEq.rfl
  exact ⟨(executeWhole before water raw path events feed physical depth).actual.trans selected,
    recognise _ selected⟩

theorem execute_whole_rejected (before : CPS1ReactiveNuclear.SourceCursor frame)
    (water : Nat) (raw : List RawSupply) (path : CPS1Recycling.SplitSite)
    (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial)
    (physical : PhysicalRaw) (depth : Nat)
    (original : SourceDisposition before.native.current water raw path events feed)
    (selected : wholeUpdate before water raw path events feed physical = .rejected original) :
    (executeWhole before water raw path events feed physical depth).event = .rejected original ∧
    HEq (executeWhole before water raw path events feed physical depth).next PUnit.unit := by
  have recognise : ∀ event : WholeDisposition before water raw path events feed physical,
      event = .rejected original →
      HEq ((match event with
        | .rejected _ => PUnit.unit
        | .generated found => runBirth found.entry depth) :
        match event with
        | .rejected _ => PUnit
        | .generated found => BirthRun found.entry depth) PUnit.unit := by
    intro event same
    cases same
    exact HEq.rfl
  exact ⟨(executeWhole before water raw path events feed physical depth).actual.trans selected,
    recognise _ selected⟩

end
end CPS1LiveEditing
