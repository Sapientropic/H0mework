import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Prefix
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingResponsibility

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : PublicFunction.OutstandingSource Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)

abbrev originalIndex := Settlement.physicalIndex source.input depth count
def originalPayments := (source.frameAt (originalIndex source depth count)).payments

variable (past : List (Compile.RawInput Party Good Port Technology Instrument))

def beforeAt (position : Fin past.length) :=
  Physical.stateAt source.input depth count prefixLimit renewalLimit
    (Physical.Prefix.eventCursor past position).past

def resultAt (position : Fin past.length) :=
  Physical.resultAt source.input depth count prefixLimit renewalLimit (Physical.Prefix.eventCursor past position)

/-- The source window is checked against the actual command target. A
primitive microstep does not acquire an invented period duration. -/
def PaidOn (position : Fin past.length) (index : source.Slot) : Prop :=
  source.seed.task.earliest ≤ (beforeAt source depth count prefixLimit renewalLimit past position).raw.clock ∧
  ((resultAt source depth count prefixLimit renewalLimit past position).next source.input depth count prefixLimit renewalLimit
    (beforeAt source depth count prefixLimit renewalLimit past position)).raw.clock ≤ source.seed.task.deadline ∧
  Exit.Necessity.BundlePaid source.seed.law
    (beforeAt source depth count prefixLimit renewalLimit past position).raw
    ((resultAt source depth count prefixLimit renewalLimit past position).requests source.input depth count prefixLimit renewalLimit
      (beforeAt source depth count prefixLimit renewalLimit past position))
    (source.seed.slot index).bearer (source.seed.slot index).goods (source.seed.slot index).purpose

instance (position : Fin past.length) (index : source.Slot) :
    Decidable (PaidOn source depth count prefixLimit renewalLimit past position index) := by
  unfold PaidOn
  infer_instance

private def inspectPast (index : source.Slot) :=
  Material.inspectList (fun position : Fin past.length =>
    ¬ PaidOn source depth count prefixLimit renewalLimit past position index) (List.finRange past.length)

def newPayment? (index : source.Slot) :
    Option {position : Fin past.length // PaidOn source depth count prefixLimit renewalLimit past position index} :=
  match inspectPast source depth count prefixLimit renewalLimit past index with
  | .clear _ => none
  | .failure position _ unpaid => some ⟨position, not_not.mp unpaid⟩

/-- A derived view of the existing payment type, recomputed from the actual
prefix. It stores no new runtime account and grants no old-emitter receipt. -/
def payments (index : source.Slot) : Option Nat :=
  match originalPayments source depth count index with
  | some paid => some paid
  | none => (newPayment? source depth count prefixLimit renewalLimit past index).map
      (fun actual => originalIndex source depth count + actual.val.val + 1)

theorem an_original_payment_keeps_its_original_ordinal (index : source.Slot) (paid : Nat)
    (recorded : originalPayments source depth count index = some paid) :
    payments source depth count prefixLimit renewalLimit past index = some paid := by
  simp only [payments, recorded]

theorem no_new_payment_iff_every_actual_occurrence_is_unpaid (index : source.Slot) :
    newPayment? source depth count prefixLimit renewalLimit past index = none ↔
      ∀ position, ¬ PaidOn source depth count prefixLimit renewalLimit past position index := by
  cases inspected : inspectPast source depth count prefixLimit renewalLimit past index with
  | clear unpaid =>
      constructor
      · intro _ position
        exact unpaid position (by simp)
      · intro _
        simp only [newPayment?, inspected]
  | failure position member unpaid =>
      constructor
      · intro impossible
        simp only [newPayment?, inspected] at impossible
        cases impossible
      · intro absent
        exact (unpaid (absent position)).elim

theorem an_unpaid_slot_has_no_hidden_original_or_actual_receipt (index : source.Slot) :
    payments source depth count prefixLimit renewalLimit past index = none ↔
      originalPayments source depth count index = none ∧
        ∀ position, ¬ PaidOn source depth count prefixLimit renewalLimit past position index := by
  cases original : originalPayments source depth count index with
  | some paid => simp only [payments, original, reduceCtorEq, false_and]
  | none =>
      simpa only [payments, original, Option.map_eq_none_iff, true_and] using
        no_new_payment_iff_every_actual_occurrence_is_unpaid source depth count prefixLimit renewalLimit past index

#print axioms an_original_payment_keeps_its_original_ordinal
#print axioms no_new_payment_iff_every_actual_occurrence_is_unpaid
#print axioms an_unpaid_slot_has_no_hidden_original_or_actual_receipt

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services
