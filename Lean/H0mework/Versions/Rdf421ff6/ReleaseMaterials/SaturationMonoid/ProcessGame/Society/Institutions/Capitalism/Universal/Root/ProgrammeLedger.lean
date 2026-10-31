import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeSource

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeLedger

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ProgrammeWorld ProgrammeSource

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : Input Party Good Port Technology Instrument)

def evolution (current : (V input).Current) :=
  (patch input (emitted input current)).toLedgerWriteEvolution

def transferReceiptOf {sourceSupport targetSupport : (N input).Support}
    {before : OpenResponsibilityAt (N input) sourceSupport}
    {after : OpenResponsibilityAt (N input) targetSupport} :
    LedgerEntryEvolutionAt (N input) before after →
      Option ((N input).DispositionAt sourceSupport .transfer)
  | .transferred receipt _ _ _ => some receipt
  | .carried _ _ | .maintained _ _ _ _ _ _ => none

/-- This reads the receipt in the actual complete-patch destination, rather
than independently reconstructing an observation beside the ledger. -/
theorem destination_transfer_receipt (current : Source.Program.RawCurrent Party Good Technology Instrument)
    (past : List (Source.Program.RawCurrent Party Good Technology Instrument))
    (entry : OpenResponsibilityAt (N input) (supportAt input (.running current past))) :
    transferReceiptOf input ((evolution input (.running current past)).destination entry).2 =
      some (ProgrammeWorld.transferReceipt (observation? input) (.running current past)) := by
  rcases entry with ⟨row, opened⟩
  cases opened
  cases row <;> rfl

def writtenTransferReceipt (current : Source.Program.RawCurrent Party Good Technology Instrument)
    (past : List (Source.Program.RawCurrent Party Good Technology Instrument))
    (entry : OpenResponsibilityAt (N input) (supportAt input (.running current past))) :
    (N input).DispositionAt (supportAt input (.running current past)) .transfer :=
  (transferReceiptOf input ((evolution input (.running current past)).destination entry).2).get
    (by rw [destination_transfer_receipt]; rfl)

theorem writtenTransferReceipt_exact (current : Source.Program.RawCurrent Party Good Technology Instrument)
    (past : List (Source.Program.RawCurrent Party Good Technology Instrument))
    (entry : OpenResponsibilityAt (N input) (supportAt input (.running current past))) :
    writtenTransferReceipt input current past entry =
      ProgrammeWorld.transferReceipt (observation? input) (.running current past) := by
  unfold writtenTransferReceipt
  generalize_proofs isSome
  simp only [destination_transfer_receipt]
  rfl

theorem origin_exact (current : (V input).Current)
    (entry : OpenResponsibilityAt (N input) (supportAt input (next input current))) :
    ((evolution input current).origin entry).1 = sourceEntry input current entry.1 := by
  change sourceEntry input current (rowAt input (rowIndex input entry.1)) = _
  exact congrArg (sourceEntry input current) (rowAt_index input entry.1)

theorem destination_exact (current : (V input).Current)
    (entry : OpenResponsibilityAt (N input) (supportAt input current)) :
    ((evolution input current).destination entry).1 = targetEntry input current entry.1 := by
  change targetEntry input current (rowAt input (rowIndex input entry.1)) = _
  exact congrArg (targetEntry input current) (rowAt_index input entry.1)

theorem targetEntry_fst (current : (V input).Current)
    (row : Row (ProgrammeSource.registrationSize input)) :
    (targetEntry input current row).1 = row := by
  cases current <;> rfl

theorem targetEntry_complete (current : (V input).Current)
    (entry : OpenResponsibilityAt (N input) (supportAt input (next input current))) :
    targetEntry input current entry.1 = entry := by
  rcases entry with ⟨row, opened⟩
  cases current <;> cases opened <;> rfl

theorem sourceEntry_complete_running (current : Source.Program.RawCurrent Party Good Technology Instrument)
    (past : List (Source.Program.RawCurrent Party Good Technology Instrument))
    (entry : OpenResponsibilityAt (N input) (supportAt input (.running current past))) :
    sourceEntry input (.running current past) entry.1 = entry := by
  rcases entry with ⟨row, opened⟩
  cases opened
  rfl

theorem destination_injective (current : (V input).Current) :
    Function.Injective (fun entry => ((evolution input current).destination entry).1) := by
  intro left right same
  dsimp only at same
  have targetSame := (destination_exact input current left).symm.trans
    (same.trans (destination_exact input current right))
  have rows := (targetEntry_fst input current left.1).symm.trans
    ((congrArg Sigma.fst targetSame).trans (targetEntry_fst input current right.1))
  rcases left with ⟨left, leftOpen⟩
  rcases right with ⟨right, rightOpen⟩
  cases rows
  cases current with
  | bootstrap =>
      cases left <;> cases leftOpen <;> cases rightOpen <;> rfl
  | running _ _ => cases leftOpen; cases rightOpen; rfl

theorem running_origin_injective
    (current : Source.Program.RawCurrent Party Good Technology Instrument)
    (past : List (Source.Program.RawCurrent Party Good Technology Instrument)) :
    Function.Injective
      (fun entry => ((evolution input (.running current past)).origin entry).1) := by
  intro left right same
  dsimp only at same
  rw [origin_exact, origin_exact] at same
  have rows := congrArg Sigma.fst same
  rcases left with ⟨left, leftOpen⟩
  rcases right with ⟨right, rightOpen⟩
  change left = right at rows
  cases rows
  cases leftOpen
  cases rightOpen
  rfl

def childRows : List (Row (ProgrammeSource.registrationSize input)) :=
  .inherited :: List.ofFn Row.instruction

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem mem_childRows (row : Row (ProgrammeSource.registrationSize input)) :
    row ∈ childRows input ↔ row ≠ .obstruction := by
  cases row <;> simp [childRows]

theorem first_origin_parent_iff
    (entry : OpenResponsibilityAt (N input) (supportAt input (next input .bootstrap))) :
    ((evolution input .bootstrap).origin entry).1 = inheritedEntry _ (ProgrammeSource.registrationSize input) ↔
      entry.1 ≠ .obstruction := by
  rw [origin_exact]
  rcases entry with ⟨row, opened⟩
  cases row with
  | inherited =>
      constructor
      · intro _ same
        cases same
      · intro _
        rfl
  | instruction _ =>
      constructor
      · intro _ same
        cases same
      · intro _
        rfl
  | obstruction =>
      constructor
      · intro same
        have rows := congrArg Sigma.fst same
        change (Row.obstruction : Row (ProgrammeSource.registrationSize input)) = .inherited at rows
        cases rows
      · intro impossible
        exact (impossible rfl).elim

theorem first_child_debit
    (entry : OpenResponsibilityAt (N input) (supportAt input (next input .bootstrap)))
    (child : entry.1 ≠ .obstruction) :
    entry.progressBudget <
      (inheritedEntry (Source.Program.RawCurrent Party Good Technology Instrument)
        (ProgrammeSource.registrationSize input)).progressBudget := by
  rcases entry with ⟨row, opened⟩
  cases row with
  | inherited | instruction _ => exact Nat.one_lt_two
  | obstruction => exact (child rfl).elim

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeLedger
