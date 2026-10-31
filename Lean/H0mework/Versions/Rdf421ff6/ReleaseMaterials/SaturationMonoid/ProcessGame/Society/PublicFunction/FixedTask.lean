import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.CapturedSource

/-!
# A public task which survives its provider's failed occurrence

The task is fixed in the source declaration before its first request. Every
later planning occurrence consumes that same task, including its original
time window. A new current cannot refresh the deadline or replace an unpaid
service bundle. Financial claims remain in the original raw interpreter.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Exit

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

structure FixedTaskSource (Party Good Port Technology Instrument : Type)
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] where
  law : RawLaw Party Good Port Technology Instrument
  initial : RawCurrent Party Good Technology Instrument
  task : PublicTaskSpec Party Good
  actionsAt : RawCurrent Party Good Technology Instrument →
    List (Request Party Good Port Technology Instrument)
  budget : Nat
  original : RawEvent Party Good Port Technology Instrument
  refused : ∃ item ∈ law.rawItems (law.next initial []) original,
    ¬ law.Valid item.before item.request

namespace FixedTaskSource

variable (source : FixedTaskSource Party Good Port Technology Instrument)

def captured : CapturedSource Party Good Port Technology Instrument where
  code := ⟨source.law, source.initial, fun _ => source.task, source.actionsAt, source.budget⟩
  original := source.original
  refused := source.refused

abbrev input := source.captured.input

theorem source_task_homology (current : RawCurrent Party Good Technology Instrument) :
    source.captured.code.taskAt current = source.task := rfl

def outcomeAt (depth : Nat) :=
  source.captured.code.compileAt (source.captured.currentAt (depth + 2))

theorem paid_projects_to_original_task (depth : Nat)
    (plan : PaidServicePlan source.law (source.captured.currentAt (depth + 2))
      source.task (source.actionsAt (source.captured.currentAt (depth + 2))) source.budget)
    (generated : source.outcomeAt depth = .paid plan) :
    ServiceAdequate source.law (source.captured.currentAt (depth + 2)) source.task
      (source.captured.actualExecution (depth + 1)).submitted ∧
    source.captured.currentAt (depth + 3) = plan.next := by
  have consumed := source.captured.paid_plan_reaches_same_root_next depth plan generated
  exact ⟨consumed.1 ▸ plan.sound.1, consumed.2.2⟩

/-- An original task slot is paid only by its own full bundle and purpose,
inside its unchanged source window, at an actual execution occurrence. -/
def SlotPaidAt (slot : ServiceSlot Party Good) (depth : Nat) : Prop :=
  source.task.earliest ≤ (source.captured.actualExecution depth).before.clock ∧
  (source.captured.actualExecution depth).after.clock ≤ source.task.deadline ∧
  Necessity.BundlePaid source.law (source.captured.actualExecution depth).before
    (source.captured.actualExecution depth).submitted slot.bearer slot.goods slot.purpose

instance (slot : ServiceSlot Party Good) (depth : Nat) :
    Decidable (source.SlotPaidAt slot depth) := by
  unfold SlotPaidAt
  infer_instance

/-- Slot identity is its original list position. Equal-looking slots do not
lose their original bearer, service bundle, purpose or source window. -/
abbrev Slot := Fin source.task.slots.length

def slot (index : source.Slot) := source.task.slots[index]

/-- A source-generated first-payment record, not an externally supplied
certificate. `depth` is the last actual occurrence checked so far. -/
def firstPayment (index : source.Slot) : Nat → Option Nat
  | 0 => if source.SlotPaidAt (source.slot index) 0 then some 0 else none
  | depth + 1 => match firstPayment index depth with
    | some paid => some paid
    | none => if source.SlotPaidAt (source.slot index) (depth + 1)
        then some (depth + 1) else none

theorem firstPayment_sound (index : source.Slot) (depth paid : Nat)
    (generated : source.firstPayment index depth = some paid) :
    paid ≤ depth ∧ source.SlotPaidAt (source.slot index) paid := by
  induction depth with
  | zero =>
    unfold firstPayment at generated
    split at generated
    next valid => cases Option.some.inj generated; exact ⟨Nat.le_refl _, valid⟩
    next => cases generated
  | succ depth ih =>
    simp only [firstPayment] at generated
    split at generated
    next original previous =>
      obtain ⟨bounded, valid⟩ := ih (previous.trans generated)
      exact ⟨Nat.le_succ_of_le bounded, valid⟩
    next =>
      split at generated
      next valid => cases Option.some.inj generated; exact ⟨Nat.le_refl _, valid⟩
      next => cases generated

theorem firstPayment_none (index : source.Slot) (depth : Nat)
    (unpaid : source.firstPayment index depth = none) :
    ∀ earlier ≤ depth, ¬ source.SlotPaidAt (source.slot index) earlier := by
  induction depth with
  | zero =>
    intro earlier bound
    have same : earlier = 0 := Nat.eq_zero_of_le_zero bound
    subst earlier
    simpa only [firstPayment, ite_eq_right_iff, reduceCtorEq, imp_false] using unpaid
  | succ depth ih =>
    simp only [firstPayment] at unpaid
    split at unpaid
    next => cases unpaid
    next previous =>
      have last : ¬ source.SlotPaidAt (source.slot index) (depth + 1) := by
        split at unpaid
        next => cases unpaid
        next missing => exact missing
      intro earlier bound
      by_cases before : earlier ≤ depth
      · exact ih previous earlier before
      · have same : earlier = depth + 1 := by omega
        exact same ▸ last

theorem firstPayment_preserved (index : source.Slot) (depth paid : Nat)
    (settled : source.firstPayment index depth = some paid) :
    source.firstPayment index (depth + 1) = some paid := by
  simp only [firstPayment, settled]

def residual (index : source.Slot) (depth : Nat) : Bundle Good :=
  match source.firstPayment index depth with
  | none => (source.slot index).goods
  | some _ => []

theorem unresolved_residual_exact (index : source.Slot) (depth : Nat)
    (unpaid : source.firstPayment index depth = none) :
    source.residual index depth = (source.slot index).goods := by
  simp only [residual, unpaid]

theorem residual_cleared_has_actual_receipt (index : source.Slot) (depth : Nat)
    (nonempty : (source.slot index).goods ≠ [])
    (cleared : source.residual index depth = []) :
    ∃ paid ≤ depth, source.SlotPaidAt (source.slot index) paid := by
  cases generated : source.firstPayment index depth with
  | none => exact False.elim (nonempty ((source.unresolved_residual_exact index depth generated).symm.trans cleared))
  | some paid => exact ⟨paid, source.firstPayment_sound index depth paid generated⟩

end FixedTaskSource

end SaturationMonoid.ProcessGame.Society.PublicFunction
