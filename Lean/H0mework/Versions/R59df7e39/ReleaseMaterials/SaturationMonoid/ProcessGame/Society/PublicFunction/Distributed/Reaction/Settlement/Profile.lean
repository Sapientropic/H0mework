import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Identity.Family
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Migration.Realization

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Settlement

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

abbrev Program := Identity.Program code
abbrev OriginalHistory := Identity.OriginalHistory code
abbrev machine := Identity.machine code

def before (program : Program code) (history : OriginalHistory code) (table : Table code) :=
  Financial.accountAt (machine code program history table).input (history.val.length + 1)

def migration (program : Program code) (history : OriginalHistory code) (table : Table code)
    (index : Fin (before code program history table).current.slots.length) :=
  (Native.generate (machine code program history table) history.val.length).migrations index.val
    ((before code program history table).current.slots.get index)
    (List.getElem?_eq_getElem index.isLt)

/-- Pairs retain different meanings in the same claim unit: still owed,
and already received through this slot's actual accepted payment events. -/
def holdings (program : Program code) (history : OriginalHistory code) (table : Table code) :
    List (List (ℚ × ℚ)) :=
  let source := machine code program history table
  List.ofFn fun index : Fin (before code program history table).current.slots.length =>
    let actual := migration code program history table index
    code.parties.map fun holder =>
      (Financial.slotBalance source.input actual.slot holder, actual.path.receivedBy source.input holder)

def holdingAt (matrix : List (List (ℚ × ℚ))) (index holder : Nat) : ℚ × ℚ :=
  ((matrix[index]?).getD [])[holder]? |>.getD (0, 0)

theorem holding_at_is_the_actual_slot_and_receipt (program : Program code) (history : OriginalHistory code)
    (table : Table code) (index : Fin (before code program history table).current.slots.length) (holder : Party) :
    holdingAt (holdings code program history table) index.val (code.parties.idxOf holder) =
      (Financial.slotBalance (machine code program history table).input
        (migration code program history table index).slot holder,
       (migration code program history table index).path.receivedBy
         (machine code program history table).input holder) := by
  have lookup : (holdings code program history table)[index.val]? = some (code.parties.map fun holder =>
      (Financial.slotBalance (machine code program history table).input
        (migration code program history table index).slot holder,
       (migration code program history table index).path.receivedBy
         (machine code program history table).input holder)) := by
    unfold holdings
    rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using index.isLt)]
    simp only [List.getElem_ofFn]
  unfold holdingAt
  rw [lookup]
  simp only [Option.getD_some, List.getElem?_map, List.getElem?_idxOf (code.parties_cover holder), Option.map_some]

def rights (matrix : List (List (ℚ × ℚ))) : List (List ℚ) :=
  matrix.map (List.map (fun value => value.1 + value.2))

theorem rights_at (matrix : List (List (ℚ × ℚ))) (index holder : Nat) :
    ((((rights matrix)[index]?).getD [])[holder]?).getD 0 =
      (holdingAt matrix index holder).1 + (holdingAt matrix index holder).2 := by
  unfold rights holdingAt
  cases row : matrix[index]? with
  | none => simp [List.getElem?_map, row]
  | some values =>
      cases entry : values[holder]? <;> simp [List.getElem?_map, row, entry]

def remaining (program : Program code) (history : OriginalHistory code) (table : Table code)
    (index : Nat) (holder : Party) : ℚ :=
  (holdingAt (holdings code program history table) index (code.parties.idxOf holder)).1

def received (program : Program code) (history : OriginalHistory code) (table : Table code)
    (index : Nat) (holder : Party) : ℚ :=
  (holdingAt (holdings code program history table) index (code.parties.idxOf holder)).2

structure Profile (Party Good Port Technology Instrument : Type) where
  originalDebts : List (Identity.DebtImage Party Good Port Technology Instrument)
  newbornDebts : List (Identity.DebtImage Party Good Port Technology Instrument)
  rights : List (List ℚ)
  uncoveredClaims : List ℚ
  firstServices : List (Option Nat)
  control : Open.Control Technology
  deriving DecidableEq

def profile (program : Program code) (history : OriginalHistory code) (table : Table code) :
    Profile Party Good Port Technology Instrument :=
  let source := machine code program history table
  let original := before code program history table
  let actual := Native.generate source history.val.length
  let after := (source.actualExecution history.val.length).after
  ⟨Identity.financeImage code source.input original,
    (Identity.financeImage code source.input actual.finance).drop original.current.slots.length,
    rights (holdings code program history table),
    code.instruments.flatMap fun instrument => code.parties.flatMap fun debtor =>
      code.parties.map fun creditor => after.claims instrument debtor creditor -
        Financial.BalanceConservation.ledgerClaims source.input actual.finance.current instrument debtor creditor,
    (List.finRange source.code.task.slots.length).map (Identity.firstService source (history.val.length + 1)),
    ⟨after.technology, after.clock, after.round⟩⟩

theorem equal_profiles_and_less_unpaid_give_more_actual_receipts
    (new old : Program code) (history : OriginalHistory code) (table : Table code)
    (same : profile code new history table = profile code old history table)
    (index : Nat) (holder : Party)
    (less : remaining code new history table index holder ≤ remaining code old history table index holder) :
    received code old history table index holder ≤ received code new history table index holder := by
  have rows := congrArg Profile.rights same
  have point := congrArg (fun matrix : List (List ℚ) => ((matrix[index]?).getD [])[code.parties.idxOf holder]? |>.getD 0) rows
  change ((((rights (holdings code new history table))[index]?).getD [])[code.parties.idxOf holder]?).getD 0 =
    ((((rights (holdings code old history table))[index]?).getD [])[code.parties.idxOf holder]?).getD 0 at point
  rw [rights_at, rights_at] at point
  change remaining code new history table index holder + received code new history table index holder =
    remaining code old history table index holder + received code old history table index holder at point
  linarith

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Settlement
