import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Check
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Accounting

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Raw

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Exit

structure Requirement where
  bearer : Party
  goods : Bundle Good
  purpose : Use
  earliest : ℚ
  deadline : ℚ
  bornAfter : Option (Nat × Nat)

def Matches (requirement : Requirement) (occurrence : Occurrence) : Prop :=
  law.Valid occurrence.item.before occurrence.item.request ∧
    Necessity.UseMatches occurrence.item.request.operation requirement.bearer requirement.goods requirement.purpose ∧
    requirement.earliest ≤ (rawFrame occurrence.ordinal).raw.clock ∧
    (law.next (rawFrame occurrence.ordinal).raw (rawWord occurrence.ordinal)).clock ≤ requirement.deadline ∧
    (match requirement.bornAfter with
      | none => True
      | some birth => birth.1 < occurrence.ordinal ∨ birth.1 = occurrence.ordinal ∧ birth.2 < occurrence.item.index)

instance (requirement : Requirement) (occurrence : Occurrence) : Decidable (Matches requirement occurrence) := by
  unfold Matches; split <;> infer_instance

structure Payment (data : List Occurrence) (requirement : Requirement) where
  occurrence : Occurrence
  original : occurrence ∈ data
  satisfied : Matches requirement occurrence

def payments (data : List Occurrence) (requirement : Requirement) : List (Payment data requirement) :=
  data.attach.filterMap fun occurrence => if checked : Matches requirement occurrence.val then
    some ⟨occurrence.val, occurrence.property, checked⟩ else none

def task (index : productionSource.Slot) : Requirement :=
  let slot := productionSource.seed.slot index
  ⟨slot.bearer, slot.goods, slot.purpose, productionSource.seed.task.earliest,
    productionSource.seed.task.deadline, none⟩

def newborn (birth : Birth) (kind : Kind) : Requirement :=
  ⟨birth.child, kind.goods, kind.purpose, birth.item.before.clock, birth.item.before.clock + 3,
    some (birth.ordinal, birth.item.index)⟩

def firstVisit (index : Fin 4) : Nat :=
  if index.val = 0 then 6 else if index.val = 1 then 8 else if index.val = 2 then 9 else 10

def Floor (current : Current) (actor : Party) : Prop :=
  (actor < 3 ∨ 0 < current.stock actor .seed) → 1 ≤ current.stock actor .life ∧ 1 ≤ current.stock actor .spare

instance (current : Current) (actor : Party) : Decidable (Floor current actor) := by unfold Floor; infer_instance

def stockFromItems (actor : Party) (good : Good) : ℚ :=
  initial.stock actor good + law.totalCredit ((occurrences 25).map Occurrence.item) actor good -
    law.totalDebit ((occurrences 25).map Occurrence.item) actor good

def amount : ℚ :=
  law.totalDebit ((List.range 25).flatMap (Participation.itemsAt false)) 0 .labor -
    law.totalDebit ((occurrences 25).map Occurrence.item) 0 .labor

inductive Row where
  | originalService (index : productionSource.Slot)
  | bornService (index : Fin 4) (kind : Kind)
  | firstProduction (index : Fin 4)
  | cut (event : Observation) (actor : Fin 6)
  | inventory (actor : Fin 6) (good : Good)
  | cost (actor : Fin 6) (good : Good)
  | nonPositiveDividend
  | withdrawal
  | returnToRole

def Holds : Row → Prop
  | .originalService index => (payments (occurrences 25) (task index)).isEmpty = false
  | .bornService index kind => (payments (occurrences 25) (newborn (born index) kind)).isEmpty = false
  | .firstProduction index => (productionsAt (born index) (firstVisit index)).isEmpty = false
  | .cut event actor => Floor event.val.item.before actor ∧
      Floor (law.step event.val.item.before event.val.item.request) actor
  | .inventory actor good => stockFromItems actor good = (rawFrame 25).raw.stock actor good
  | .cost actor good =>
      law.totalCredit ((occurrences 25).map Occurrence.item) actor good =
        law.totalCredit ((List.range 25).flatMap (Participation.itemsAt false)) actor good ∧
      law.totalDebit ((occurrences 25).map Occurrence.item) actor good +
        (if actor.val = 0 ∧ good = .labor then 1 else 0) =
        law.totalDebit ((List.range 25).flatMap (Participation.itemsAt false)) actor good
  | .nonPositiveDividend => amount = 1 ∧ 0 < amount
  | .withdrawal => (rawFrame 21).register 1 = .released ∧ (rawFrame 21).register 2 = .declined ∧
      law.Valid (rawFrame 21).raw (audit 1) ∧ (rawWord 21).isEmpty = true ∧
      (rawFrame 22).register 1 = .released ∧
      ((itemsAt 22).map (fun item => cycleTag item.request) = [1, 2, 3]) ∧
      (∀ item ∈ itemsAt 22, law.Valid item.before item.request) ∧
      (rawFrame 23).raw.stock 1 .seed = (rawFrame 22).raw.stock 1 .seed + 2
  | .returnToRole => (rawFrame 24).register 1 = .released ∧
      law.Valid (rawFrame 24).raw (Participation.request 1 .accept) ∧ (rawFrame 25).register 1 = .active ∧
      flowAt (law.actualDebit (rawFrame 24).raw (Participation.request 1 .accept)) 1 .labor = 1

instance : DecidablePred Holds := by intro row; cases row <;> unfold Holds <;> infer_instance

def rows : List Row :=
  ((List.finRange productionSource.seed.task.slots.length).map Row.originalService) ++
    ((List.finRange 4).flatMap fun index => [.bornService index .life, .bornService index .maintenance, .firstProduction index]) ++
    ((occurrences 25).attach.flatMap fun event => (List.finRange 6).map (Row.cut event)) ++
    ((List.finRange 6).flatMap fun actor => goods.map (Row.inventory actor)) ++
    ((List.finRange 6).flatMap fun actor => goods.map (Row.cost actor)) ++
    [.nonPositiveDividend, .withdrawal, .returnToRole]

def verify := Check.run rows Holds

theorem actual_raw_rows_hold : ∀ row : Row, Holds row := by
  intro row
  cases row with
  | originalService index =>
    have paid : ∀ index : productionSource.Slot, Holds (.originalService index) := by decide +kernel
    exact paid index
  | bornService index kind =>
    have paid : ∀ index : Fin 4, ∀ kind : Kind, Holds (.bornService index kind) := by decide +kernel
    exact paid index kind
  | firstProduction index =>
    have produced : ∀ index : Fin 4, Holds (.firstProduction index) := by decide +kernel
    exact produced index
  | cut event actor =>
    have safe : ∀ occurrence ∈ occurrences 25, ∀ actor : Fin 6,
        Floor occurrence.item.before actor ∧ Floor (law.step occurrence.item.before occurrence.item.request) actor := by
      decide +kernel
    exact safe event.val event.property actor
  | inventory actor good =>
    have balanced : ∀ actor : Fin 6, ∀ good : Good, Holds (.inventory actor good) := by decide +kernel
    exact balanced actor good
  | cost actor good =>
    have balanced : ∀ actor : Fin 6, ∀ good : Good, Holds (.cost actor good) := by decide +kernel
    exact balanced actor good
  | nonPositiveDividend => decide +kernel
  | withdrawal => decide +kernel
  | returnToRole => decide +kernel

theorem actual_raw_verifier_accepts : verify = .accepted ⟨fun row _ => actual_raw_rows_hold row⟩ :=
  Check.run_accepts rows Holds (fun row _ => actual_raw_rows_hold row)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Raw
