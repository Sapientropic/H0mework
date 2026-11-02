import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.FinancingBook.Cash.Origin
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.FinancingBook.Posting

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.FinancingBook.Cash
open ResponsibilityLifecycle Source.Program
variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

def rowKeys : Row sources → List Nat
  | .birth _ claim => (DelayedFinancing.origins sources claim).map fun origin => origin.access.access.val.index
  | .cross _ entry => (AssignedFinancing.origins sources entry.boundary).map fun origin => origin.access.access.val.index

def Checked (row : Row sources) (index : Nat) : Prop :=
  match row with
  | .birth _ claim => ∃ origin ∈ DelayedFinancing.origins sources claim, origin.access.access.val.index = index
  | .cross _ entry => ∃ origin ∈ AssignedFinancing.origins sources entry.boundary, origin.access.access.val.index = index

theorem row_keys_exact (row : Row sources) (index : Nat) : index ∈ rowKeys sources row ↔ Checked sources row index := by
  cases row <;> exact List.mem_map

def rawAt (window : Exposure.Window sources) := (sources window.1).law.rawItems
  (ProgrammeSource.rawCurrent (sources window.1) window.2.current)
  (ProgrammeSource.rawEvent (sources window.1) window.2.current)

theorem checked_original (row : Row sources) (index : Nat) (checked : Checked sources row index) :
    ∃ item ∈ rawAt sources (AssignedFinancing.Joint.Posting.eventWindow sources row.event), item.index = index := by
  cases row with
  | birth position claim =>
      obtain ⟨origin,_,same⟩ := checked
      exact ⟨origin.access.access.val,origin.access.access.property,same⟩
  | cross position entry =>
      obtain ⟨origin,_,same⟩ := checked
      exact ⟨origin.access.access.val,origin.access.access.property,same⟩

variable (receipt : Financial.Family.Migration.Posting.VisitReceipt sources)

/-- This is a restriction of the actual native visit, using the same Book fold.
The checked cash keys do not depend on a choice of financial share refinement. -/
def flow := FinancingBook.fold sources (receipt.native sources) (generated sources receipt.before)

def positions := (flow sources receipt).rows.flatMap (rowKeys sources)
def selected (index : Nat) := DelayedFinancing.Cash.markedBy (positions sources receipt) index

theorem row_window (row : Row sources) (member : row ∈ (flow sources receipt).rows) :
    AssignedFinancing.Joint.Posting.eventWindow sources row.event = receipt.window sources := by
  have native : row.native ∈ (receipt.native sources).events := by
    rw [← (flow sources receipt).events_exact]
    exact List.mem_map.mpr ⟨row,member,rfl⟩
  have own := Origin.actual_visit sources receipt row.native native
  rw [Row.native_source] at own
  exact own

theorem selected_exact (index : Nat) : selected sources receipt index = true ↔
    ∃ row ∈ (flow sources receipt).rows, Checked sources row index := by
  constructor
  · intro marked
    obtain ⟨position,member,same⟩ := List.any_eq_true.mp marked
    have same := beq_iff_eq.mp same
    subst position
    obtain ⟨row,inside,hit⟩ := List.mem_flatMap.mp member
    exact ⟨row,inside,(row_keys_exact sources row index).mp hit⟩
  · rintro ⟨row,member,checked⟩
    apply List.any_eq_true.mpr
    exact ⟨index,List.mem_flatMap.mpr ⟨row,member,(row_keys_exact sources row index).mpr checked⟩,beq_iff_eq.mpr rfl⟩

theorem selected_has_its_original_native_event_and_cash (index : Nat) (marked : selected sources receipt index = true) :
    ∃ row ∈ (flow sources receipt).rows, Checked sources row index ∧
      row.native ∈ (receipt.native sources).events ∧
      ∃ item ∈ DelayedFinancing.Cash.rawItems sources receipt, item.index = index := by
  obtain ⟨row,member,checked⟩ := (selected_exact sources receipt index).mp marked
  refine ⟨row,member,checked,?_,?_⟩
  · rw [← (flow sources receipt).events_exact]
    exact List.mem_map.mpr ⟨row,member,rfl⟩
  · have original := checked_original sources row index checked
    rw [row_window sources receipt row member] at original
    exact original

/-- Union the original raw access indices before folding any actual cash item.
Settlement is excluded here: it is already present in the same Book's charge. -/
def cash (selected credit : Bool) (party : Party) (good : Good) : ℚ :=
  DelayedFinancing.Cash.cashBy sources receipt (positions sources receipt) selected credit party good

theorem duplicate_keys_do_not_duplicate_cash (keys : List Nat) (selected credit : Bool) (party : Party) (good : Good) :
    DelayedFinancing.Cash.cashBy sources receipt (keys ++ keys) selected credit party good =
      DelayedFinancing.Cash.cashBy sources receipt keys selected credit party good :=
  DelayedFinancing.Cash.duplicate_explanations_do_not_duplicate_any_cash sources receipt keys selected credit party good

theorem cash_partition (credit : Bool) (party : Party) (good : Good) :
    cash sources receipt true credit party good + cash sources receipt false credit party good =
      ((DelayedFinancing.Cash.rawItems sources receipt).map fun item => if PublicFunction.Costs.isDebtPayment item.request then 0 else
        flowAt (if credit then (sources receipt.sourceIndex).law.actualCredit item.before item.request
          else (sources receipt.sourceIndex).law.actualDebit item.before item.request) party good).sum := by
  unfold cash DelayedFinancing.Cash.cashBy
  induction DelayedFinancing.Cash.rawItems sources receipt with
  | nil => simp only [List.map_nil,List.sum_nil,add_zero]
  | cons item rest ih =>
    simp only [List.map_cons,List.sum_cons]
    cases DelayedFinancing.Cash.markedBy (positions sources receipt) item.index <;>
      simp only [Bool.false_eq_true,Bool.true_eq_false,if_false,if_true] <;> linarith

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.FinancingBook.Cash
