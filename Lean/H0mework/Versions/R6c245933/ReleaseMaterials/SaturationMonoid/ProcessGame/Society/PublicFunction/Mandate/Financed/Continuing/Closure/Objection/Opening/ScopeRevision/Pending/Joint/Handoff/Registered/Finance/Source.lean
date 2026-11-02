import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Runtime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Funding.Cash
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Posting.Balance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery.ReturnIncidence

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Finance
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Financial.Family.Migration.Posting
noncomputable section
local notation "sources" => Pending.Joint.Finance.sources
abbrev Visit := VisitReceipt sources
abbrev Item := ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit

def raw (receipt : Visit) : List Item := Financial.Family.Migration.DelayedFinancing.Cash.rawItems sources receipt
def origin (receipt : Visit) : Current × List Action :=
  (ProgrammeSource.rawCurrent (sources receipt.sourceIndex) (receipt.window sources).2.current,
   ProgrammeSource.rawEvent (sources receipt.sourceIndex) (receipt.window sources).2.current)
def selected (receipt : Visit) (index : Nat) : Bool :=
  Financial.Family.Migration.Funding.Cash.selected sources receipt index ||
    Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Discovery.ReturnIncidence.selected
      (sources receipt.sourceIndex).law (origin receipt).1 (origin receipt).2 index

def flow (receipt : Visit) (item : Item) (incoming : Bool) (actor : Bool) (good : Good) : ℚ :=
  flowAt (if incoming then (sources receipt.sourceIndex).law.actualCredit item.before item.request else
    (sources receipt.sourceIndex).law.actualDebit item.before item.request) actor good

def cashAt (receipt : Visit) (item : Item) (side incoming : Bool) (actor : Bool) (good : Good) : ℚ :=
  if PublicFunction.Costs.isDebtPayment item.request then 0 else
    if selected receipt item.index = side then flow receipt item incoming actor good else 0

def cash (entries : List Visit) (side incoming : Bool) (actor : Bool) (good : Good) : ℚ :=
  (entries.map fun receipt => ((raw receipt).map fun item => cashAt receipt item side incoming actor good).sum).sum

def quantity (entries : List Visit) (incoming : Bool) (actor : Bool) (good : Good) : ℚ :=
  (entries.map fun receipt => ((raw receipt).map fun item => flow receipt item incoming actor good).sum).sum

private theorem local_partition (receipt : Visit) (incoming : Bool) (actor : Bool) (good : Good) :
    ((raw receipt).map fun item => cashAt receipt item true incoming actor good).sum +
    ((raw receipt).map fun item => cashAt receipt item false incoming actor good).sum +
      atVisit sources (receipt.window sources) (if incoming then .credit else .debit) actor good =
    ((raw receipt).map fun item => flow receipt item incoming actor good).sum := by
  unfold atVisit rawTotal
  change _ + _ + ((raw receipt).map fun item => rawAmount sources receipt.sourceIndex item
    (if incoming then .credit else .debit) actor good).sum = _
  induction raw receipt with
  | nil => simp
  | cons item rest ih =>
    simp only [List.map_cons,List.sum_cons] at *
    have cashHead : cashAt receipt item true incoming actor good + cashAt receipt item false incoming actor good =
        if PublicFunction.Costs.isDebtPayment item.request then 0 else flow receipt item incoming actor good := by
      unfold cashAt
      cases debt : PublicFunction.Costs.isDebtPayment item.request <;>
        cases choice : selected receipt item.index <;> simp_all only [Bool.false_eq_true,Bool.true_eq_false,if_false,if_true,add_zero,zero_add]
    have nativeHead : (if PublicFunction.Costs.isDebtPayment item.request then 0 else flow receipt item incoming actor good) +
        rawAmount sources receipt.sourceIndex item (if incoming then .credit else .debit) actor good =
        flow receipt item incoming actor good := by
      cases operation : item.request.operation <;> cases incoming <;>
        simp only [PublicFunction.Costs.isDebtPayment,operation,rawAmount,flow,Bool.false_eq_true,if_false,if_true,add_zero,zero_add]
    linarith only [cashHead,nativeHead,ih]

variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (authority : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : Pending.Joint.Inventory authority originInputs)
  (fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs)
  (word : List Action)

def before : Pending.Joint.Finance.Account := (Registered.legacy authority inventory).finance
def after : Pending.Joint.Finance.Account := Registered.account authority inventory fresh word
def run : (Financial.Family.process sources).Run
    (before authority inventory).current (after authority inventory fresh word).current :=
  Registered.financialRun authority inventory fresh word

theorem initial_matrix : Financial.Family.ledgerClaims sources (before authority inventory).current =
    (PublicFunction.Costs.Visits.rawAt sources (Registered.input authority inventory fresh word) 0).claims := by
  exact Pending.Joint.financial_matrix_at_every_actual_cut authority (Registered.legacy authority inventory)

def entries : List Visit := intervalReceipts sources (Registered.input authority inventory fresh word) 0 4
  (before authority inventory) (Registered.compatible authority inventory fresh word) (initial_matrix authority inventory fresh word)
@[irreducible] def book : Financial.Family.Migration.FinancingBook.Book sources (before authority inventory).current :=
  Financial.Family.Migration.Funding.generated sources (before authority inventory)
@[irreducible] def funded : Financial.Family.Migration.FinancingBook.Flow sources (run authority inventory fresh word) (book authority inventory) :=
  Financial.Family.Migration.Funding.fold sources (run authority inventory fresh word) (book authority inventory)
def charge := Financial.Family.Migration.FinancingBook.Posting.nativeCharge sources (funded authority inventory fresh word)
def account (side : Bool) (actor : Bool) (good : Good) : ℚ :=
  cash (entries authority inventory fresh word) side false actor good - cash (entries authority inventory fresh word) side true actor good +
    charge authority inventory fresh word side actor good

theorem every_visit_and_native_event_is_the_original_actual_interval :
    (entries authority inventory fresh word).map (VisitReceipt.window sources) =
      PublicFunction.Costs.Visits.interval sources (Registered.input authority inventory fresh word) 0 4 ∧
    ((entries authority inventory fresh word).map fun receipt => (receipt.native sources).events).flatten =
      (run authority inventory fresh word).events :=
  ⟨intervalReceipts_keys _ _ _ _ _ _ _,intervalReceipts_events _ _ _ _ _ _ _⟩

theorem every_financing_slot_and_event_is_the_same_original_run :
    (funded authority inventory fresh word).after.cells.map Financial.Family.Migration.FinancingBook.Cell.slot =
      (after authority inventory fresh word).current.slots ∧
    (funded authority inventory fresh word).rows.map Financial.Family.Migration.FinancingBook.Row.native =
      (run authority inventory fresh word).events :=
  ⟨(funded authority inventory fresh word).after.slots_exact,(funded authority inventory fresh word).events_exact⟩

private theorem receipt_sum (entries : List Visit) (incoming : Bool) (actor : Bool) (good : Good) :
    cash entries true incoming actor good + cash entries false incoming actor good +
      Financial.Family.Migration.Posting.total sources (entries.map (VisitReceipt.window sources))
        (if incoming then .credit else .debit) actor good = quantity entries incoming actor good := by
  induction entries with
  | nil => simp [cash,quantity,Financial.Family.Migration.Posting.total]
  | cons receipt rest ih =>
    have head := local_partition receipt incoming actor good
    simp only [cash,quantity,List.map_cons,List.sum_cons,Financial.Family.Migration.Posting.total] at *
    linarith only [head,ih]

theorem each_actual_payment_has_one_cash_or_original_native_leg (incoming : Bool) (actor : Bool) (good : Good) :
    cash (entries authority inventory fresh word) true incoming actor good +
      cash (entries authority inventory fresh word) false incoming actor good +
      runAmount sources (run authority inventory fresh word) (if incoming then .credit else .debit) actor good =
    quantity (entries authority inventory fresh word) incoming actor good := by
  have exact := receipt_sum (entries authority inventory fresh word) incoming actor good
  rw [(every_visit_and_native_event_is_the_original_actual_interval authority inventory fresh word).1] at exact
  have payment : runAmount sources (run authority inventory fresh word) (if incoming then .credit else .debit) actor good =
      total sources (PublicFunction.Costs.Visits.interval sources (Registered.input authority inventory fresh word) 0 4)
        (if incoming then .credit else .debit) actor good :=
    interval_amount sources (Registered.input authority inventory fresh word) 0 4 (before authority inventory)
      (Registered.compatible authority inventory fresh word) (initial_matrix authority inventory fresh word) _ actor good
  linarith only [exact,payment]

private def atWindow (entry : PublicFunction.Costs.Visits.Window sources) (incoming : Bool) (actor : Bool) (good : Good) : ℚ :=
  (((sources entry.1).law.rawItems (ProgrammeSource.rawCurrent (sources entry.1) entry.2.current)
    (ProgrammeSource.rawEvent (sources entry.1) entry.2.current)).map fun item =>
      flowAt (if incoming then (sources entry.1).law.actualCredit item.before item.request else
        (sources entry.1).law.actualDebit item.before item.request) actor good).sum
private def windowsTotal (windows : List (PublicFunction.Costs.Visits.Window sources))
    (incoming : Bool) (actor : Bool) (good : Good) := (windows.map fun entry => atWindow entry incoming actor good).sum

private theorem interval_material (index : Pending.Joint.Finance.Input) (start count : Nat) (actor : Bool) (good : Good) :
    (PublicFunction.Costs.Visits.rawAt sources index (start+count)).stock actor good +
      windowsTotal (PublicFunction.Costs.Visits.interval sources index start count) false actor good =
    (PublicFunction.Costs.Visits.rawAt sources index start).stock actor good +
      windowsTotal (PublicFunction.Costs.Visits.interval sources index start count) true actor good := by
  induction count generalizing start with
  | zero => simp [windowsTotal,PublicFunction.Costs.Visits.interval]
  | succ count ih =>
    have front := (sources index).law.actual_next_material_balance
      (PublicFunction.Costs.Visits.rawAt sources index start)
      (ProgrammeSource.rawEvent (sources index) (ProgrammeHistory.visitAt (sources index) start).current) actor good
    rw [← PublicFunction.Costs.Visits.raw_next sources index start] at front
    change (PublicFunction.Costs.Visits.rawAt sources index (start+1)).stock actor good +
      atWindow (PublicFunction.Costs.Visits.window sources index start) false actor good =
      (PublicFunction.Costs.Visits.rawAt sources index start).stock actor good +
      atWindow (PublicFunction.Costs.Visits.window sources index start) true actor good at front
    have tail := ih (start+1)
    rw [show start+(count+1)=start+1+count by omega]
    simp only [PublicFunction.Costs.Visits.interval,windowsTotal,List.map_cons,List.sum_cons] at *
    linarith only [front,tail]

theorem all_original_raw_items_balance_the_same_actual_material_endpoints (actor : Bool) (good : Good) :
    (Registered.final authority inventory fresh word).stock actor good +
      quantity (entries authority inventory fresh word) false actor good =
    (PublicFunction.Costs.Visits.rawAt sources (Registered.input authority inventory fresh word) 0).stock actor good +
      quantity (entries authority inventory fresh word) true actor good := by
  have amounts (incoming : Bool) : quantity (entries authority inventory fresh word) incoming actor good =
      windowsTotal ((entries authority inventory fresh word).map (VisitReceipt.window sources)) incoming actor good := by
    simp only [quantity,windowsTotal,List.map_map]
    rfl
  rw [amounts false,amounts true,(every_visit_and_native_event_is_the_original_actual_interval authority inventory fresh word).1]
  exact interval_material (Registered.input authority inventory fresh word) 0 4 actor good

def quotedBefore (actor : Bool) (good : Good) : ℚ :=
  (PublicFunction.Costs.Visits.rawAt sources (Registered.input authority inventory fresh word) 0).stock actor good +
    Balance.position sources (before authority inventory).current .credit actor good -
    Balance.position sources (before authority inventory).current .debit actor good

def quotedAfter (actor : Bool) (good : Good) : ℚ :=
  (Registered.final authority inventory fresh word).stock actor good +
    Balance.position sources (after authority inventory fresh word).current .credit actor good -
    Balance.position sources (after authority inventory fresh word).current .debit actor good

theorem the_union_cash_and_complete_native_charge_are_exactly_the_original_net_change (actor : Bool) (good : Good) :
    account authority inventory fresh word true actor good + account authority inventory fresh word false actor good =
      quotedBefore authority inventory fresh word actor good - quotedAfter authority inventory fresh word actor good := by
  have debit := each_actual_payment_has_one_cash_or_original_native_leg authority inventory fresh word false actor good
  have credit := each_actual_payment_has_one_cash_or_original_native_leg authority inventory fresh word true actor good
  have material := all_original_raw_items_balance_the_same_actual_material_endpoints authority inventory fresh word actor good
  have native := Financial.Family.Migration.FinancingBook.Posting.nativeCharge_partition sources
    (funded authority inventory fresh word) actor good
  change charge authority inventory fresh word true actor good + charge authority inventory fresh word false actor good = _ at native
  simp only [Bool.false_eq_true,if_false,if_true] at debit credit
  unfold account quotedBefore quotedAfter
  linarith only [debit,credit,material,native]


end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Finance
