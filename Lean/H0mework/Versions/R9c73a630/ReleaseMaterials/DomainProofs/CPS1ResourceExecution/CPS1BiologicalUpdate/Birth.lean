import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.Native

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1BiologicalUpdate
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing
variable {frame : CPS1Recycling.Frame}

theorem reactants_never_release (reaction : Reaction) (peptide : Peptide) :
    reaction.reactants.count (.releasedPeptide peptide) = 0 := by
  cases reaction <;> simp [Reaction.reactants,factorStock]

theorem debit_never_release (trace : List Reaction) (peptide : Peptide) :
    (debit trace).count (.releasedPeptide peptide) = 0 := by
  induction trace with
  | nil => rfl
  | cons reaction rest ih =>
    simpa only [debit,Inventory.debit,List.flatMap_cons,List.count_append,
      reactants_never_release,Nat.zero_add] using ih

theorem translation_release_delta (current : CPS1ReactiveField.Occurrence frame)
    (water : Nat) (raw : List RawSupply) (event : TranslationEvent current water raw) :
    event.native.stock.count (.releasedPeptide event.peptide) =
      event.available.count (.releasedPeptide event.peptide) +
        (credit event.native.fired).count (.releasedPeptide event.peptide) := by
  have balance := event.whole.count_eq (.releasedPeptide event.peptide)
  simp only [List.count_append,debit_never_release,Nat.add_zero] at balance
  exact balance.symm

theorem biosynthetic_birth_credit {before : CPS1ReactiveNuclear.SourceCursor frame}
    {water : Nat} {raw : List RawSupply} {path : CPS1Recycling.SplitSite}
    {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
    {physical : PhysicalRaw} {depth : Nat}
    (event : NativeBiosyntheticEvent before water raw path events feed physical depth) :
    event.newlyProduced =
      (credit event.physicalEvent.seed.translation.native.fired).count
        (.releasedPeptide event.physicalEvent.seed.translation.peptide) := by
  rw [event.newlyProducedSource,event.releaseBeforeSource,event.releaseAfterSource,
    translation_release_delta]
  omega

end
end CPS1BiologicalUpdate
