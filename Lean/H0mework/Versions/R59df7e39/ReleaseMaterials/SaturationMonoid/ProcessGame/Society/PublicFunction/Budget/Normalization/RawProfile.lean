import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Future
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Settlement.Comparison

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.RawProfile

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument) (input : Input source.code) (cut : Nat)

abbrev start := source.history.length + 2 + cut
abbrev horizon := (Residual.seed source input cut).remaining
abbrev finish := start source cut + horizon source input cut
abbrev originalSlots := (Financial.accountAt source.input (start source cut)).current.slots.length
abbrev machine (opponent : Opponent source.code) (term : List (Option source.code.Policy)) :=
  Future.target source input cut opponent term
abbrev before (rival : Opponent source.code) (term : List (Option source.code.Policy)) :=
  Financial.accountAt (machine source input cut rival term).input (start source cut)
abbrev after (rival : Opponent source.code) (term : List (Option source.code.Policy)) :=
  Financial.accountAt (machine source input cut rival term).input (finish source input cut)
abbrev terminal (rival : Opponent source.code) (term : List (Option source.code.Policy)) :=
  (machine source input cut rival term).currentAt (finish source input cut)

def migration (rival : Opponent source.code) (term : List (Option source.code.Policy))
    (index : Fin (before source input cut rival term).current.slots.length) :=
  Financial.Migration.actual (machine source input cut rival term).input (start source cut) (horizon source input cut)
    index.val ((before source input cut rival term).current.slots.get index) (List.getElem?_eq_getElem index.isLt)

theorem before_keeps_the_original_slot_count (rival : Opponent source.code) (term : List (Option source.code.Policy))
    (active : source.feedback? = some input) :
    (before source input cut rival term).current.slots.length = originalSlots source cut := by
  have same := Future.complete_finance_before source input cut rival term active (start source cut) (Nat.le_refl _)
  simpa only [Identity.financeImage, List.length_map] using congrArg List.length same.slots

/-- Owed and actually received have the same claim unit but distinct sources. -/
def holdings (rival : Opponent source.code) (term : List (Option source.code.Policy)) : List (List (ℚ × ℚ)) :=
  List.ofFn fun index : Fin (before source input cut rival term).current.slots.length =>
    let actual := migration source input cut rival term index
    source.code.parties.map fun holder =>
      (Financial.slotBalance (machine source input cut rival term).input actual.slot holder,
        actual.path.receivedBy (machine source input cut rival term).input holder)

def remaining (rival : Opponent source.code) (term : List (Option source.code.Policy)) (index : Nat) (holder : Party) : ℚ :=
  (Settlement.holdingAt (holdings source input cut rival term) index (source.code.parties.idxOf holder)).1

def received (rival : Opponent source.code) (term : List (Option source.code.Policy)) (index : Nat) (holder : Party) : ℚ :=
  (Settlement.holdingAt (holdings source input cut rival term) index (source.code.parties.idxOf holder)).2

theorem holding_is_the_actual_slot_and_receipt (rival : Opponent source.code) (term : List (Option source.code.Policy))
    (index : Fin (before source input cut rival term).current.slots.length) (holder : Party) :
    Settlement.holdingAt (holdings source input cut rival term) index.val (source.code.parties.idxOf holder) =
      (Financial.slotBalance (machine source input cut rival term).input (migration source input cut rival term index).slot holder,
        (migration source input cut rival term index).path.receivedBy (machine source input cut rival term).input holder) := by
  have lookup : (holdings source input cut rival term)[index.val]? = some (source.code.parties.map fun holder =>
      (Financial.slotBalance (machine source input cut rival term).input (migration source input cut rival term index).slot holder,
        (migration source input cut rival term index).path.receivedBy (machine source input cut rival term).input holder)) := by
    unfold holdings
    rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using index.isLt)]
    simp only [List.getElem_ofFn]
  unfold Settlement.holdingAt
  rw [lookup]
  simp only [Option.getD_some, List.getElem?_map, List.getElem?_idxOf (source.code.parties_cover holder), Option.map_some]

theorem every_original_holder_has_exact_native_conservation (rival : Opponent source.code)
    (term : List (Option source.code.Policy)) (index : Fin (before source input cut rival term).current.slots.length) (holder : Party) :
    remaining source input cut rival term index.val holder + received source input cut rival term index.val holder =
      Financial.slotBalance (machine source input cut rival term).input
        ((before source input cut rival term).current.slots.get index) holder +
      (migration source input cut rival term index).path.assignedTo (machine source input cut rival term).input holder := by
  change (Settlement.holdingAt _ _ _).1 + (Settlement.holdingAt _ _ _).2 = _
  rw [holding_is_the_actual_slot_and_receipt]
  exact (migration source input cut rival term index).path.holder_conservation _ holder

def profile (rival : Opponent source.code) (term : List (Option source.code.Policy)) :
    Settlement.Profile Party Good Port Technology Instrument :=
  let candidate := machine source input cut rival term
  let first := before source input cut rival term
  let last := after source input cut rival term
  let current := terminal source input cut rival term
  ⟨Identity.financeImage source.code candidate.input first,
    (Identity.financeImage source.code candidate.input last).drop first.current.slots.length,
    Settlement.rights (holdings source input cut rival term),
    source.code.instruments.flatMap fun instrument => source.code.parties.flatMap fun debtor =>
      source.code.parties.map fun creditor => current.claims instrument debtor creditor -
        Financial.BalanceConservation.ledgerClaims candidate.input last.current instrument debtor creditor,
    (List.finRange source.code.task.slots.length).map (Identity.firstService candidate (start source cut - 1)),
    ⟨current.technology, current.clock, current.round⟩⟩

def serviceTime (rival : Opponent source.code) (term : List (Option source.code.Policy)) (index : Fin source.code.task.slots.length) : ℚ :=
  ((Identity.firstService (machine source input cut rival term) (finish source input cut - 1) index).getD (finish source input cut) : ℚ)

def material (rival : Opponent source.code) (term : List (Option source.code.Policy)) : Settlement.Material Party Good → ℚ
  | .debit party good => ((List.range (horizon source input cut)).map fun offset =>
      let actual := (machine source input cut rival term).actualExecution (start source cut - 1 + offset)
      source.code.law.totalDebit actual.interpreted.items party good).sum
  | .credit party good => -((List.range (horizon source input cut)).map fun offset =>
      let actual := (machine source input cut rival term).actualExecution (start source cut - 1 + offset)
      source.code.law.totalCredit actual.interpreted.items party good).sum
  | .inventory party good => -(terminal source input cut rival term).stock party good
  | .clock => (terminal source input cut rival term).clock
  | .admissibility => if source.code.eligible
      (Residual.run source.code (Residual.scheduleAt source cut term) ⟨rival, input.budget⟩
        (Residual.seed source input cut) (horizon source input cut)).past then 0 else 1

theorem same_rights_and_less_owed_give_more_actual_receipts
    (rival : Opponent source.code) (new old : List (Option source.code.Policy))
    (same : profile source input cut rival new = profile source input cut rival old)
    (index : Nat) (holder : Party)
    (less : remaining source input cut rival new index holder ≤ remaining source input cut rival old index holder) :
    received source input cut rival old index holder ≤ received source input cut rival new index holder := by
  have rows := congrArg Settlement.Profile.rights same
  have point := congrArg (fun matrix : List (List ℚ) => ((matrix[index]?).getD [])[source.code.parties.idxOf holder]? |>.getD 0) rows
  change ((((Settlement.rights (holdings source input cut rival new))[index]?).getD [])[source.code.parties.idxOf holder]?).getD 0 =
    ((((Settlement.rights (holdings source input cut rival old))[index]?).getD [])[source.code.parties.idxOf holder]?).getD 0 at point
  rw [Settlement.rights_at, Settlement.rights_at] at point
  change remaining source input cut rival new index holder + received source input cut rival new index holder =
    remaining source input cut rival old index holder + received source input cut rival old index holder at point
  linarith

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization.RawProfile
