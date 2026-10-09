import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LiveEditing.Physical
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveSourceEntry.Cycle

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1LiveEditing
noncomputable section
open CPS1ReactiveSourceEntry CPS1ReactiveJointNuclear
variable {frame : CPS1Recycling.Frame}

inductive BirthRun (entry : Entry frame) (depth : Nat)
  | residual (cursor : CPS1ReactiveNuclear.SourceCursor frame) (failure : EntryFailure frame)
      (actual : entry = .residual cursor failure)
  | fired (entered : Entered frame) (actual : entry = .admitted entered)
      (run : EnteredRun entered depth)

def runBirth (entry : Entry frame) (depth : Nat) : BirthRun entry depth :=
  match entry with
  | Entry.residual cursor failure => .residual cursor failure rfl
  | Entry.admitted entered => .fired entered rfl (renewEntered entered depth)

theorem birth_run_actual (entry : Entry frame) (depth : Nat) :
    match runBirth entry depth with
    | .residual cursor failure _ => entry = .residual cursor failure
    | .fired entered _ returned =>
      entry = .admitted entered ∧
      CPS1ReactiveJointNuclear.renew entered.cursor depth = ⟨returned.after.cursor,returned.pulses,0,none⟩ ∧
      returned.pulses.length = depth ∧ ∀ pulse ∈ returned.pulses, pulse.Valid := by
  cases runBirth entry depth with
  | residual cursor failure actual => exact actual
  | fired entered actual returned =>
    have ready := CPS1ReactiveJointNuclear.renew_ready entered.cursor depth entered.ready
    have whole := CPS1ReactiveJointNuclear.renew_whole entered.cursor depth
    rw [returned.actual] at ready whole
    exact ⟨actual,returned.actual,ready.2.2.1,whole.2.2.2.2.2⟩

structure WholeRun (before : CPS1ReactiveNuclear.SourceCursor frame)
    (water : Nat) (raw : List RawSupply) (path : CPS1Recycling.SplitSite)
    (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial) (physical : PhysicalRaw) (depth : Nat) where
  original : CPS1ReactiveNuclear.SourceCursor frame
  originalSource : original = before
  event : WholeDisposition before water raw path events feed physical
  next : match event with
    | .rejected _ => PUnit
    | .generated returned => BirthRun returned.entry depth
  actual : event = wholeUpdate before water raw path events feed physical

def executeWhole (before : CPS1ReactiveNuclear.SourceCursor frame)
    (water : Nat) (raw : List RawSupply) (path : CPS1Recycling.SplitSite)
    (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial) (physical : PhysicalRaw) (depth : Nat) :
    WholeRun before water raw path events feed physical depth :=
  let event := wholeUpdate before water raw path events feed physical
  ⟨before,rfl,event,match event with
    | .rejected _ => PUnit.unit
    | .generated returned => runBirth returned.entry depth,rfl⟩

theorem whole_run_original (before : CPS1ReactiveNuclear.SourceCursor frame)
    (water : Nat) (raw : List RawSupply) (path : CPS1Recycling.SplitSite)
    (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial) (physical : PhysicalRaw) (depth : Nat) :
    (executeWhole before water raw path events feed physical depth).original = before ∧
    (executeWhole before water raw path events feed physical depth).original.native = before.native ∧
    HEq (executeWhole before water raw path events feed physical depth).original.germ before.germ := by
  have same := (executeWhole before water raw path events feed physical depth).originalSource
  have germSame : ∀ (left right : CPS1ReactiveNuclear.SourceCursor frame),
      left = right → HEq left.germ right.germ := by
    intro left right equal
    cases equal
    exact HEq.rfl
  exact ⟨same,congrArg CPS1ReactiveNuclear.SourceCursor.native same,germSame _ _ same⟩

theorem physical_original_rows (before : CPS1ReactiveNuclear.SourceCursor frame)
    (water : Nat) (raw : List RawSupply) (path : CPS1Recycling.SplitSite)
    (events : List CPS1Recycling.RawEvent) (feed : List CPS1Recycling.RawMaterial) (physical : PhysicalRaw)
    (event : PhysicalEvent before water raw path events feed physical)
    (material : CPS1ReactiveField.Material
      (CPS1ReactiveField.next (CPS1ReactiveField.start event.deformation) physical.actions physical.feed physical.rows)) :
    OriginalRows material := NativeSource.original_rows_from_stock material event.generatedRows

end
end CPS1LiveEditing
