import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.Genome

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1BiologicalUpdate
noncomputable section
open CPS1ReactiveSourceEntry CPS1LiveEditing
variable {frame : CPS1Recycling.Frame}

def reachedCursor {entry : Entry frame} {depth : Nat} (outcome : BirthRun entry depth) :
    CPS1ReactiveNuclear.SourceCursor frame :=
  match outcome with
  | .residual cursor _ _ => cursor
  | .fired _ _ run => run.after.cursor

@[irreducible] def entryCursor (entry : Entry frame) : CPS1ReactiveNuclear.SourceCursor frame :=
  match entry with
  | .residual cursor _ => cursor
  | .admitted entered => entered.cursor

theorem initial_entry_current (old : CPS1Deformation.Source.Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (rows : List CPS1AddressedReactiveJoint.Rows.RawAction) :
    (entryCursor (enterFromOld old actions feed rows)).native.current =
      CPS1ReactiveField.next (CPS1ReactiveField.start old) actions feed rows := by
  unfold enterFromOld
  dsimp only
  repeat first
    | split
    | (simp only [entryCursor]; rfl)

theorem reached_genome_read {entry : Entry frame} {depth : Nat} (outcome : BirthRun entry depth) :
    CPS1Deamination.ExecutionReadout.readDNA (liveResources (reachedCursor outcome).native.current) =
      CPS1Deamination.ExecutionReadout.readDNA (liveResources (entryCursor entry).native.current) := by
  cases outcome with
  | residual cursor failure actual => cases actual; simp only [reachedCursor,entryCursor]
  | fired entered actual run =>
    cases actual
    simpa only [reachedCursor,entryCursor] using (physical_run_genome_read entered depth run).1

end
end CPS1BiologicalUpdate
