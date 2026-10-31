import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Check
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Newborn
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Native
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Accounting

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Ledger

open ResponsibilityLifecycle
open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root

def terminalFlag {V : ResponsibilityLifecycle.Vocabulary} (state : ResponsibilityState V) : Bool :=
  match (state.slots[0]? : Option (ObligationSlot V)) with | some (ObligationSlot.terminal _) => true | _ => false

theorem terminal_flag_iff {V : ResponsibilityLifecycle.Vocabulary} (state : ResponsibilityState V) :
    terminalFlag state = true ↔ state.TerminalAt 0 := by
  unfold terminalFlag ResponsibilityState.TerminalAt
  cases selected : state.slots[0]? with
  | none => simp
  | some slot => cases slot <;> simp

/-- Ordered local balance updates, independent of Raw's sum of all flows. -/
def post (stock : Party → Good → ℚ) (item : Item) : Party → Good → ℚ := fun actor good =>
  stock actor good - flowAt (law.actualDebit item.before item.request) actor good +
    flowAt (law.actualCredit item.before item.request) actor good

def inventory : Party → Good → ℚ := ((occurrences 25).map Occurrence.item).foldl post initial.stock

def addFlow (measure : Item → Flow Party Good) (stock : Party → Good → ℚ) (item : Item) : Party → Good → ℚ :=
  fun actor good => stock actor good + flowAt (measure item) actor good

def rawItems (shared : Bool) : List Item := (List.range 25).flatMap (Participation.itemsAt shared)

def debit (shared : Bool) : Party → Good → ℚ :=
  (rawItems shared).foldl (addFlow (fun item => law.actualDebit item.before item.request)) (fun _ _ => 0)

def credit (shared : Bool) : Party → Good → ℚ :=
  (rawItems shared).foldl (addFlow (fun item => law.actualCredit item.before item.request)) (fun _ _ => 0)

def amount : ℚ := debit false 0 .labor - debit true 0 .labor

def stockGain : ℚ := (rawFrame 25).raw.stock 0 .labor - (Participation.frameAt false 25).raw.stock 0 .labor

def Floor (current : Current) (actor : Party) : Prop :=
  (actor < 3 ∨ 0 < current.stock actor .seed) → 1 ≤ current.stock actor .life ∧ 1 ≤ current.stock actor .spare

instance (current : Current) (actor : Party) : Decidable (Floor current actor) := by unfold Floor; infer_instance

inductive Row where
  | originalService (index : productionSource.Slot)
  | bornService (index : Fin 4) (kind : Kind)
  | financialCut (ordinal : Fin 26)
  | cut (actor : Fin 6) (event : Observation)
  | inventory (actor : Fin 6) (good : Good)
  | cost (actor : Fin 6) (good : Good)
  | withdrawal
  | dividend
  | dialogue

def Holds : Row → Prop
  | .originalService index => terminalFlag (OutstandingSource.NativeService.historyAt productionSource index 24).state = true
  | .bornService index kind => terminalFlag (Newborn.historyAt (born index) kind (25 - (born index).ordinal)).state = true
  | .financialCut ordinal => ∀ debtor holder : Fin 6,
      Financial.BalanceConservation.ledgerClaims productionSource.input (account true ordinal).current () debtor holder =
        (rawFrame ordinal).raw.claims () debtor holder
  | .cut actor event => Floor event.val.item.before actor ∧
      Floor (law.step event.val.item.before event.val.item.request) actor
  | .inventory actor good => inventory actor good = (rawFrame 25).raw.stock actor good
  | .cost actor good => credit true actor good = credit false actor good ∧
      debit true actor good + (if actor.val = 0 ∧ good = .labor then 1 else 0) = debit false actor good
  | .withdrawal => (rawFrame 21).register 1 = .released ∧ (rawFrame 21).register 2 = .declined ∧
      law.Valid (rawFrame 21).raw (audit 1) ∧ (rawWord 21).isEmpty = true ∧
      (rawFrame 22).register 1 = .released ∧
      ((itemsAt 22).map (fun item => cycleTag item.request) = [1, 2, 3]) ∧
      (∀ item ∈ itemsAt 22, law.Valid item.before item.request) ∧
      (rawFrame 23).raw.stock 1 .seed = (rawFrame 22).raw.stock 1 .seed + 2
  | .dividend => amount = 1 ∧ 0 < amount ∧ stockGain = amount
  | .dialogue => (Participation.Native.historyAt true 12).state.history.map LifecycleEvent.kind =
      [.admitted, .maintained, .deferred, .maintained, .bearerRelease, .maintained]

instance : DecidablePred Holds := by intro row; cases row <;> unfold Holds <;> infer_instance

def rows : List Row :=
  ((List.finRange productionSource.seed.task.slots.length).map Row.originalService) ++
    ((List.finRange 4).flatMap fun index => [.bornService index .life, .bornService index .maintenance]) ++
    ((List.finRange 26).map Row.financialCut) ++
    ((List.finRange 6).flatMap fun actor => (occurrences 25).attach.map (Row.cut actor)) ++
    ((List.finRange 6).flatMap fun actor => goods.map (Row.inventory actor)) ++
    ((List.finRange 6).flatMap fun actor => goods.map (Row.cost actor)) ++
    [.dividend, .dialogue, .withdrawal]

def verify := Check.run rows Holds

theorem actual_ledger_rows_hold : ∀ row : Row, Holds row := by
  intro row
  cases row with
  | originalService index =>
    have paid : ∀ index : productionSource.Slot, Holds (.originalService index) := by decide +kernel
    exact paid index
  | bornService index kind =>
    have paid : ∀ index : Fin 4, ∀ kind : Kind, Holds (.bornService index kind) := by decide +kernel
    exact paid index kind
  | financialCut ordinal =>
    intro debtor holder
    have same := congrFun (congrFun (congrFun (financial_matrix true ordinal) ()) debtor) holder
    rw [Participation.actual_current_is_the_machine] at same
    exact same
  | cut actor event =>
    have safe : ∀ actor : Fin 6, ∀ occurrence ∈ occurrences 25,
        Floor occurrence.item.before actor ∧ Floor (law.step occurrence.item.before occurrence.item.request) actor := by
      decide +kernel
    exact safe actor event.val event.property
  | inventory actor good =>
    have balanced : ∀ actor : Fin 6, ∀ good : Good, Holds (.inventory actor good) := by decide +kernel
    exact balanced actor good
  | cost actor good =>
    have balanced : ∀ actor : Fin 6, ∀ good : Good, Holds (.cost actor good) := by decide +kernel
    exact balanced actor good
  | withdrawal => decide +kernel
  | dividend => decide +kernel
  | dialogue => decide +kernel

theorem actual_ledger_verifier_accepts : verify = .accepted ⟨fun row _ => actual_ledger_rows_hold row⟩ :=
  Check.run_accepts rows Holds (fun row _ => actual_ledger_rows_hold row)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Ledger
