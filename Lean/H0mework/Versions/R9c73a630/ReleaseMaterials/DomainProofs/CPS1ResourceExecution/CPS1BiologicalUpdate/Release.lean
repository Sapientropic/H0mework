import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.Birth

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1BiologicalUpdate
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing
variable {frame : CPS1Recycling.Frame}

private theorem charge_credit_zero (tail : List AA) (peptide : Peptide) :
    (credit (tail.map Reaction.charge)).count (.releasedPeptide peptide) = 0 := by
  induction tail with
  | nil => rfl
  | cons aa rest ih =>
    simpa [credit,Inventory.credit,Reaction.products] using ih

private theorem elongation_credit_zero (chain : Peptide) (tail : List AA) (peptide : Peptide) :
    (credit (Program.compileElongation chain tail)).count (.releasedPeptide peptide) = 0 := by
  induction tail generalizing chain with
  | nil => rfl
  | cons aa rest ih =>
    simpa [credit,Inventory.credit,Program.compileElongation,Reaction.products] using ih (chain.extend aa)

private theorem native_elongation_credit_zero (tail : List AA) (peptide : Peptide) :
    (credit (CPS1InitiationTermination.UnifiedBoundary.elongation tail)).count
      (.releasedPeptide peptide) = 0 := by
  cases tail with
  | nil => rfl
  | cons aa rest =>
    simpa [CPS1InitiationTermination.UnifiedBoundary.elongation,credit,Inventory.credit,
      Reaction.products] using elongation_credit_zero (.M,[aa]) rest peptide

theorem compiled_release_credit (tail : List AA) :
    (credit (CPS1InitiationTermination.UnifiedBoundary.compile tail)).count
      (.releasedPeptide (.M,tail)) = 1 := by
  have charge := charge_credit_zero tail (.M,tail)
  have elongate := native_elongation_credit_zero tail (.M,tail)
  cases tail <;>
    simp [CPS1InitiationTermination.UnifiedBoundary.compile,
      CPS1InitiationTermination.UnifiedBoundary.termination,credit,Inventory.credit,
      Reaction.products,factorStock,List.flatMap_append] at charge elongate ⊢ <;> omega

private theorem missing_none_remaining_nil (program : List Reaction) (stock : Stock)
    (complete : (execute program stock).missing = none) :
    (execute program stock).remaining = [] := by
  induction program generalizing stock with
  | nil => rfl
  | cons reaction rest ih =>
    cases fired : fire reaction stock with
    | error missing => simp [execute,Inventory.execute,fired] at complete
    | ok next =>
      have after : (execute rest next).missing = none := by
        simpa [execute,Inventory.execute,fired] using complete
      simpa [execute,Inventory.execute,fired] using ih next after

theorem translation_release_is_new (current : CPS1ReactiveField.Occurrence frame)
    (water : Nat) (raw : List RawSupply) (event : TranslationEvent current water raw)
    (complete : event.native.missing = none) :
    event.native.fired = event.program ∧
    (credit event.native.fired).count (.releasedPeptide event.peptide) = 1 ∧
    event.native.stock.count (.releasedPeptide event.peptide) =
      event.available.count (.releasedPeptide event.peptide) + 1 := by
  have ready : (execute event.program event.available).missing = none := by
    rw [← event.actual]
    exact complete
  have rest := missing_none_remaining_nil event.program event.available ready
  have fired := execution_decomposes event.program event.available
  rw [rest,List.append_nil,← event.actual] at fired
  have credited : (credit event.native.fired).count (.releasedPeptide event.peptide) = 1 := by
    rw [fired,event.programSource]
    have peptideSame : event.peptide = (.M,event.peptide.2) :=
      Prod.ext event.initiator rfl
    rw [peptideSame]
    exact compiled_release_credit event.peptide.2
  exact ⟨fired,credited,by rw [translation_release_delta,credited]⟩

end
end CPS1BiologicalUpdate
