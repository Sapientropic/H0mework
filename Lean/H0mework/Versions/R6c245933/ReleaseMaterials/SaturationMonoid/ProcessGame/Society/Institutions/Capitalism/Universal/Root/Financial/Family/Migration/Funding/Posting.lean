import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Funding.Book

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1200000
namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Funding.Posting
open ResponsibilityLifecycle FinancingBook FinancingBook.Posting
open Financial.Family.Migration.Posting
variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

def issued (row : Row sources) (selected : Bool) (side : Side) (party : Party) (good : Good) : ℚ :=
  match row with
  | .birth _ claim => Balance.holding sources claim (shares (Funding.initial sources claim) selected) side party good
  | .cross _ _ => 0

private theorem update_balance {state : ResponsibilityState (vocabulary sources)} (book : Book sources state)
    (edge : (process sources).Edge state) (selected : Bool) (side : Side) (party : Party) (good : Good) :
    position sources (Funding.update sources book edge).after selected side party good +
      payment sources (Funding.update sources book edge).row selected side party good =
    position sources book selected side party good + issued sources (Funding.update sources book edge).row selected side party good +
      assigned sources (Funding.update sources book edge).row selected side party good := by
  cases edge with
  | admit claim =>
      simp only [Funding.update,position,List.map_append,List.map_cons,List.map_nil,List.sum_append,
        List.sum_cons,List.sum_nil,payment,issued,assigned,add_zero]
      rfl
  | cross index obligation present boundary =>
      change Boundary sources obligation at boundary
      let entry := AssignedFinancing.Joint.Entry.ofBoundary sources boundary (book.before index obligation present)
      let cell : Cell sources := ⟨(Boundary.disposition sources boundary).targetSlot,
        entry.result.final⟩
      have localBalance := AssignedFinancing.Joint.Posting.entry_balance sources entry selected side party good
      have oldClaim := congrArg (slotClaim sources) ((book.at_slot index).trans present)
      have relevant : value sources cell selected side party good +
          AssignedFinancing.Joint.Posting.payment sources entry selected side party good =
        value sources (book.cellAt index) selected side party good +
          AssignedFinancing.Joint.Posting.assignment sources entry selected side party good := by
        dsimp only [value,cell]
        rw [boundary_claim sources boundary,oldClaim]
        simpa only [Share.Split.reindex,shares,Book.before,entry,
          AssignedFinancing.Joint.Entry.ofBoundary,AssignedFinancing.Joint.Posting.beforeShares,
          AssignedFinancing.Joint.Posting.afterShares,slotClaim,slotObligation] using localBalance
      change ((book.cells.set index.val cell).map fun cell => value sources cell selected side party good).sum +
          AssignedFinancing.Joint.Posting.payment sources entry selected side party good =
        position sources book selected side party good + 0 +
          AssignedFinancing.Joint.Posting.assignment sources entry selected side party good
      rw [List.map_set,List.sum_set']
      simp only [List.length_map,book.length,index.isLt,↓reduceDIte,List.getElem_map]
      change position sources book selected side party good + (-value sources (book.cellAt index) selected side party good +
        value sources cell selected side party good) + _ = _
      linarith only [relevant]
  | reopen _ _ _ impossible => exact impossible.elim

theorem run_balance {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) (before : Book sources first)
    (selected : Bool) (side : Side) (party : Party) (good : Good) :
    position sources (Funding.fold sources run before).after selected side party good +
      tally sources (Funding.fold sources run before).rows (payment sources) selected side party good (fun _ => true) =
    position sources before selected side party good +
      tally sources (Funding.fold sources run before).rows (issued sources) selected side party good (fun _ => true) +
      tally sources (Funding.fold sources run before).rows (assigned sources) selected side party good (fun _ => true) := by
  induction run with
  | nil => simp only [Funding.fold,tally,List.map_nil,List.sum_nil,add_zero]
  | step prior edge ih =>
      have next := update_balance sources (Funding.fold sources prior before).after edge selected side party good
      simp only [Funding.fold,tally,List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,
        List.sum_nil,add_zero,if_true] at ih ⊢
      linarith only [ih,next]

theorem nativeCharge_balance {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) (before : Book sources first)
    (selected : Bool) (party : Party) (good : Good) :
    nativeCharge sources (Funding.fold sources run before) selected party good =
      tally sources (Funding.fold sources run before).rows (issued sources) selected .debit party good (fun _ => true) -
      tally sources (Funding.fold sources run before).rows (issued sources) selected .credit party good (fun _ => true) +
      tally sources (Funding.fold sources run before).rows (assigned sources) selected .debit party good (fun _ => true) -
      tally sources (Funding.fold sources run before).rows (assigned sources) selected .credit party good (fun _ => true) := by
  have debit := run_balance sources run before selected .debit party good
  have credit := run_balance sources run before selected .credit party good
  unfold nativeCharge
  linarith only [debit,credit]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Funding.Posting
