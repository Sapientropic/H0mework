import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.Update

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1BiologicalUpdate
noncomputable section
open CPS1ReactiveSourceEntry CPS1LiveEditing CPS1ReactiveJointNuclear
variable {frame : CPS1Recycling.Frame}

theorem physical_run_live_stock (entry : Entered frame) (depth : Nat) (run : EnteredRun entry depth) :
    CPS1ReactiveField.liveStock run.after.cursor.native.current =
      CPS1ReactiveField.liveStock entry.cursor.native.current := by
  have whole := renew_whole entry.cursor depth
  rw [run.actual] at whole
  dsimp only at whole
  unfold CPS1ReactiveField.liveStock CPS1ReactiveField.oldResidual
  rw [whole.1,whole.2.1]

theorem physical_run_genome_read (entry : Entered frame) (depth : Nat) (run : EnteredRun entry depth) :
    CPS1Deamination.ExecutionReadout.readDNA (liveResources run.after.cursor.native.current) =
      CPS1Deamination.ExecutionReadout.readDNA (liveResources entry.cursor.native.current) ∧
    readCoding (liveResources run.after.cursor.native.current) =
      readCoding (liveResources entry.cursor.native.current) ∧
    readProteinDamage run.after.cursor.native.current = readProteinDamage entry.cursor.native.current := by
  have stock := physical_run_live_stock entry depth run
  have resources : liveResources run.after.cursor.native.current = liveResources entry.cursor.native.current :=
    congrArg (List.filterMap liveResource?) stock
  refine ⟨congrArg CPS1Deamination.ExecutionReadout.readDNA resources,congrArg readCoding resources,?_⟩
  unfold readProteinDamage actualGenePeptide
  rw [resources]

end
end CPS1BiologicalUpdate
