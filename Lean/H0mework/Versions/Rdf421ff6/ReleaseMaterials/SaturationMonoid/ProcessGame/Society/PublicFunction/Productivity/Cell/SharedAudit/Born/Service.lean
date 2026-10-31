import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Born.Trace

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Born

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Exit

inductive Kind where
  | life | maintenance
  deriving DecidableEq

instance : Fintype Kind where
  elems := {.life, .maintenance}
  complete := by intro kind; cases kind <;> simp

def Kind.goods : Kind → Bundle Good
  | .life => [(.life, 1)]
  | .maintenance => [(.spare, 1)]

def Kind.purpose : Kind → Use
  | .life => .necessity
  | .maintenance => .maintenance

/-- The obligation is fixed at the seed transfer, before its payment is known. -/
def taskSlot (birth : Birth) (kind : Kind) : ServiceSlot Party Good :=
  ⟨birth.child, kind.goods, kind.purpose⟩

def Later (birth : Birth) (ordinal : Nat) (item : Item) : Prop :=
  birth.ordinal < ordinal ∨ birth.ordinal = ordinal ∧ birth.item.index < item.index

instance (birth : Birth) (ordinal : Nat) (item : Item) : Decidable (Later birth ordinal item) := by
  unfold Later; infer_instance

def Window (birth : Birth) (ordinal : Nat) : Prop :=
  birth.item.before.clock ≤ (frameAt ordinal).raw.clock ∧
    (law.next (frameAt ordinal).raw (wordAt ordinal (frameAt ordinal))).clock ≤ birth.item.before.clock + 3

instance (birth : Birth) (ordinal : Nat) : Decidable (Window birth ordinal) := by
  unfold Window; infer_instance

structure PaymentData (birth : Birth) (kind : Kind) (ordinal : Nat) (items : List Item) where
  item : Item
  original : item ∈ items
  accepted : law.Valid item.before item.request
  use : Necessity.UseMatches item.request.operation birth.child kind.goods kind.purpose
  after_seed : Later birth ordinal item
  window : Window birth ordinal

def paymentsFrom (birth : Birth) (kind : Kind) (ordinal : Nat) (items : List Item) :
    List (PaymentData birth kind ordinal items) :=
  if window : Window birth ordinal then
    items.attach.filterMap fun item =>
      if paid : law.Valid item.val.before item.val.request ∧
          Necessity.UseMatches item.val.request.operation birth.child kind.goods kind.purpose ∧
          Later birth ordinal item.val then
        some ⟨item.val, item.property, paid.1, paid.2.1, paid.2.2, window⟩
      else none
  else []

abbrev Payment (birth : Birth) (kind : Kind) (ordinal : Nat) :=
  PaymentData birth kind ordinal (itemsAt ordinal)

def payments (birth : Birth) (kind : Kind) (ordinal : Nat) : List (Payment birth kind ordinal) :=
  paymentsFrom birth kind ordinal (itemsAt ordinal)

def Paid (birth : Birth) (kind : Kind) (ordinal : Nat) : Prop :=
  (payments birth kind ordinal).isEmpty = false

instance (birth : Birth) (kind : Kind) (ordinal : Nat) : Decidable (Paid birth kind ordinal) := by
  unfold Paid; infer_instance

def payment (birth : Birth) (kind : Kind) (ordinal : Nat) (paid : Paid birth kind ordinal) :
    Payment birth kind ordinal :=
  (payments birth kind ordinal).head (List.isEmpty_eq_false_iff.mp paid)

theorem payment_is_in_the_original_root (birth : Birth) (kind : Kind) (ordinal : Nat)
    (paid : Paid birth kind ordinal) :
    (payment birth kind ordinal paid).item ∈ law.rawItems (source.currentAt ordinal)
      (Institutions.Capitalism.Universal.Root.ProgrammeSource.rawEvent source.input
        (Institutions.Capitalism.Universal.Root.ProgrammeHistory.visitAt source.input ordinal).current) := by
  rw [← items_are_the_original_execution]
  exact (payment birth kind ordinal paid).original

structure ProductionData (birth : Birth) (ordinal : Nat) where
  item : Item
  original : item ∈ itemsAt ordinal
  accepted : law.Valid item.before item.request
  operation : item.request.operation = .produce birth.child
  after_seed : Later birth ordinal item
  seed : 0 < item.before.stock birth.child .seed

def Produces (operation : Operation Party Good Technology Unit) (actor : Party) : Prop :=
  match operation with | .produce operator => operator = actor | _ => False

instance (operation : Operation Party Good Technology Unit) (actor : Party) : Decidable (Produces operation actor) := by
  unfold Produces; cases operation <;> infer_instance

def productionsAt (birth : Birth) (ordinal : Nat) : List (ProductionData birth ordinal) :=
  (itemsAt ordinal).attach.filterMap fun item =>
    if checked : law.Valid item.val.before item.val.request ∧
        Produces item.val.request.operation birth.child ∧
        Later birth ordinal item.val ∧ 0 < item.val.before.stock birth.child .seed then
      some ⟨item.val, item.property, checked.1,
        by
          have operation := checked.2.1
          cases equation : item.val.request.operation <;> simp only [Produces, equation] at operation
          rename_i actor
          exact congrArg Operation.produce operation,
        checked.2.2.1, checked.2.2.2⟩
    else none

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Born
