import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.FinancingBook

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1200000
namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.FinancingBook
open ResponsibilityLifecycle
open Financial.Family.Migration.Posting
variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

namespace Posting

def shares {balance : Shares (Party := Party)} (split : Share.Split balance) (selected : Bool) :=
  if selected then split.selected else split.remainder

omit [DecidableEq Port] in
private theorem holding_partition (claim : Claim sources) {balance : Shares (Party := Party)}
    (split : Share.Split balance) (side : Side) (party : Party) (good : Good) :
    Balance.holding sources claim (shares split true) side party good +
      Balance.holding sources claim (shares split false) side party good =
        Balance.holding sources claim balance side party good := by
  have total : Financial.total (sources claim.1) split.selected + Financial.total (sources claim.1) split.remainder =
      Financial.total (sources claim.1) balance := by
    calc
      _ = Financial.total (sources claim.1) (split.selected + split.remainder) := by
        unfold Financial.total
        rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
      _ = _ := congrArg (Financial.total (sources claim.1)) split.exact
  have valuedTotal := congrArg (fun q => q * (sources claim.1).law.settlementRate claim.2.instrument) total
  have pointwise := congrArg (fun q => q * (sources claim.1).law.settlementRate claim.2.instrument) (split.pointwise party)
  simp only [add_mul] at valuedTotal pointwise
  cases side <;> simp only [Balance.holding,shares,Bool.false_eq_true,if_true,if_false] <;>
    split_ifs <;> linarith only [valuedTotal,pointwise]

def value (cell : Cell sources) (selected : Bool) (side : Side) (party : Party) (good : Good) :=
  Balance.holding sources (slotClaim sources cell.slot) (shares cell.shares selected) side party good

def position {state : ResponsibilityState (vocabulary sources)} (book : Book sources state)
    (selected : Bool) (side : Side) (party : Party) (good : Good) : ℚ :=
  (book.cells.map fun cell => value sources cell selected side party good).sum

private theorem sum_partition {α : Type} (items : List α) (left right total : α → ℚ)
    (exact : ∀ item, left item + right item = total item) :
    (items.map left).sum + (items.map right).sum = (items.map total).sum := by
  induction items with
  | nil => exact add_zero 0
  | cons item rest ih => simp only [List.map_cons,List.sum_cons]; linarith [exact item]

theorem position_partition {state : ResponsibilityState (vocabulary sources)} (book : Book sources state)
    (side : Side) (party : Party) (good : Good) :
    position sources book true side party good + position sources book false side party good =
      Balance.position sources state side party good := by
  unfold position Balance.position
  rw [← book.slots_exact,List.map_map]
  apply sum_partition
  intro cell
  exact holding_partition sources _ cell.shares side party good

def payment (row : Row sources) (selected : Bool) (side : Side) (party : Party) (good : Good) : ℚ :=
  match row with
  | .birth _ _ => 0
  | .cross _ entry => AssignedFinancing.Joint.Posting.payment sources entry selected side party good

def issued (row : Row sources) (selected : Bool) (side : Side) (party : Party) (good : Good) : ℚ :=
  match row with
  | .birth _ claim => Balance.holding sources claim (shares (initial sources claim) selected) side party good
  | .cross _ _ => 0

def assigned (row : Row sources) (selected : Bool) (side : Side) (party : Party) (good : Good) : ℚ :=
  match row with
  | .birth _ _ => 0
  | .cross _ entry => AssignedFinancing.Joint.Posting.assignment sources entry selected side party good

theorem payment_partition (row : Row sources) (side : Side) (party : Party) (good : Good) :
    payment sources row true side party good + payment sources row false side party good =
      Financial.Family.Migration.Posting.amount sources row.event side party good := by
  cases row with
  | birth => cases side <;> simp only [payment,Row.event,Financial.Family.Migration.Posting.amount,add_zero]
  | cross index entry => exact AssignedFinancing.Joint.Posting.payment_partition sources entry side party good

theorem issued_partition (row : Row sources) (side : Side) (party : Party) (good : Good) :
    issued sources row true side party good + issued sources row false side party good =
      Balance.issued sources row.event side party good := by
  cases row with
  | birth index claim => exact holding_partition sources claim (initial sources claim) side party good
  | cross => simp only [issued,Row.event,AssignedFinancing.Joint.Entry.event,Boundary.event,Balance.issued,add_zero]

theorem assigned_partition (row : Row sources) (side : Side) (party : Party) (good : Good) :
    assigned sources row true side party good + assigned sources row false side party good =
      Balance.assigned sources row.event side party good := by
  cases row with
  | birth => cases side <;> simp only [assigned,Row.event,Balance.assigned,add_zero]
  | cross index entry => exact AssignedFinancing.Joint.Posting.assignment_partition sources entry side party good

private theorem update_balance {state : ResponsibilityState (vocabulary sources)} (book : Book sources state)
    (edge : (process sources).Edge state) (selected : Bool) (side : Side) (party : Party) (good : Good) :
    position sources (update sources book edge).after selected side party good +
      payment sources (update sources book edge).row selected side party good =
    position sources book selected side party good + issued sources (update sources book edge).row selected side party good +
      assigned sources (update sources book edge).row selected side party good := by
  cases edge with
  | admit claim =>
      simp only [update,position,List.map_append,List.map_cons,List.map_nil,List.sum_append,
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

/-- Queries filter original event windows, including each later review's own
source visit. They do not compare source functions or reuse a global ordinal. -/
def tally (rows : List (Row sources)) (field : Row sources → Bool → Side → Party → Good → ℚ)
    (selected : Bool) (side : Side) (party : Party) (good : Good) (window : Exposure.Window sources → Bool) : ℚ :=
  (rows.map fun row => if window (AssignedFinancing.Joint.Posting.eventWindow sources row.event) then
    field row selected side party good else 0).sum

def actual {first last : ResponsibilityState (vocabulary sources)} (run : (process sources).Run first last)
    (field : Family.Event sources → Side → Party → Good → ℚ) (side : Side) (party : Party) (good : Good)
    (window : Exposure.Window sources → Bool) : ℚ :=
  (run.events.map fun event => if window (AssignedFinancing.Joint.Posting.eventWindow sources (sourceEvent sources event)) then
    field (sourceEvent sources event) side party good else 0).sum

theorem tally_partition {first last : ResponsibilityState (vocabulary sources)}
    {run : (process sources).Run first last} {before : Book sources first} (flow : Flow sources run before)
    (field : Row sources → Bool → Side → Party → Good → ℚ)
    (original : Family.Event sources → Side → Party → Good → ℚ)
    (exact : ∀ row side party good, field row true side party good + field row false side party good = original row.event side party good)
    (side : Side) (party : Party) (good : Good) (window : Exposure.Window sources → Bool) :
    tally sources flow.rows field true side party good window + tally sources flow.rows field false side party good window =
      actual sources run original side party good window := by
  have trace := congrArg (fun events : List (LifecycleEvent (vocabulary sources)) =>
    (events.map fun event => if window (AssignedFinancing.Joint.Posting.eventWindow sources (sourceEvent sources event)) then
      original (sourceEvent sources event) side party good else 0).sum) flow.events_exact
  simp only [List.map_map] at trace
  unfold tally actual
  rw [← trace]
  apply sum_partition
  intro row
  dsimp only [Function.comp_apply]
  rw [Row.native_source]
  split_ifs
  · exact exact row side party good
  · exact add_zero 0

theorem run_balance {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) (before : Book sources first)
    (selected : Bool) (side : Side) (party : Party) (good : Good) :
    position sources (fold sources run before).after selected side party good +
      tally sources (fold sources run before).rows (payment sources) selected side party good (fun _ => true) =
    position sources before selected side party good +
      tally sources (fold sources run before).rows (issued sources) selected side party good (fun _ => true) +
      tally sources (fold sources run before).rows (assigned sources) selected side party good (fun _ => true) := by
  induction run with
  | nil => simp only [fold,tally,List.map_nil,List.sum_nil,add_zero]
  | step prior edge ih =>
      have next := update_balance sources (fold sources prior before).after edge selected side party good
      simp only [fold,tally,List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,
        List.sum_nil,add_zero,if_true] at ih ⊢
      linarith only [ih,next]

/-- This signed native charge includes both actual repayments and the change of
all liabilities/assets. The independent two components cover the original book. -/
def nativeCharge {first last : ResponsibilityState (vocabulary sources)}
    {run : (process sources).Run first last} {before : Book sources first} (flow : Flow sources run before)
    (selected : Bool) (party : Party) (good : Good) : ℚ :=
  tally sources flow.rows (payment sources) selected .debit party good (fun _ => true) -
  tally sources flow.rows (payment sources) selected .credit party good (fun _ => true) +
  position sources flow.after selected .debit party good - position sources before selected .debit party good -
  position sources flow.after selected .credit party good + position sources before selected .credit party good

theorem nativeCharge_balance {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) (before : Book sources first)
    (selected : Bool) (party : Party) (good : Good) :
    nativeCharge sources (fold sources run before) selected party good =
      tally sources (fold sources run before).rows (issued sources) selected .debit party good (fun _ => true) -
      tally sources (fold sources run before).rows (issued sources) selected .credit party good (fun _ => true) +
      tally sources (fold sources run before).rows (assigned sources) selected .debit party good (fun _ => true) -
      tally sources (fold sources run before).rows (assigned sources) selected .credit party good (fun _ => true) := by
  have debit := run_balance sources run before selected .debit party good
  have credit := run_balance sources run before selected .credit party good
  unfold nativeCharge
  linarith only [debit,credit]

theorem nativeCharge_partition {first last : ResponsibilityState (vocabulary sources)}
    {run : (process sources).Run first last} {before : Book sources first} (flow : Flow sources run before)
    (party : Party) (good : Good) :
    nativeCharge sources flow true party good + nativeCharge sources flow false party good =
      runAmount sources run .debit party good - runAmount sources run .credit party good +
      Balance.position sources last .debit party good - Balance.position sources first .debit party good -
      Balance.position sources last .credit party good + Balance.position sources first .credit party good := by
  have debit := tally_partition sources flow (payment sources) (Financial.Family.Migration.Posting.amount sources)
    (payment_partition sources) .debit party good (fun _ => true)
  have credit := tally_partition sources flow (payment sources) (Financial.Family.Migration.Posting.amount sources)
    (payment_partition sources) .credit party good (fun _ => true)
  have firstDebit := position_partition sources before .debit party good
  have firstCredit := position_partition sources before .credit party good
  have lastDebit := position_partition sources flow.after .debit party good
  have lastCredit := position_partition sources flow.after .credit party good
  simp only [actual,if_true] at debit credit
  unfold nativeCharge runAmount
  linarith only [debit,credit,firstDebit,firstCredit,lastDebit,lastCredit]

end Posting
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.FinancingBook
