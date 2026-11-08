import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Fold
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Principal

/-!
# One original debt with distinct decision, exposure and creditor addresses

The old authority is a stock-port rule. A signed destructive operation pays
its real revision input and changes the permission to impose a transfer.
Reattachment is an additional material payment to the exposed bearer.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers

open Capitalism.Universal.Root Capitalism.Universal.Source.Program

abbrev Party := Fin 3
abbrev controller : Party := 0
abbrev creditor : Party := 1
abbrev exposed : Party := 2

abbrev State := RawCurrent Party Unit Bool Unit
abbrev Command := Request Party Unit Party Bool Unit
abbrev Word := RawEvent Party Unit Party Bool Unit

def law : RawLaw Party Unit Party Bool Unit where
  technique := fun _ _ => ⟨[], [], [], []⟩
  controller := fun _ port => port
  allowed := fun emergency port signer =>
    decide (port = signer ∨ (emergency = true ∧ port = exposed ∧ signer = controller))
  stockPort := fun _ bearer _ => bearer
  revisionPort := fun _ => controller
  revisionCost := fun old new => if old = false ∧ new = true then [((), 2)] else []
  settlementUnit := fun _ => ()
  settlementRate := fun _ => 1
  issuerPort := fun _ => controller
  necessities := fun _ _ => []
  mandatoryMaintenance := fun _ _ => []
  duration := fun _ => 1

def initial : State where
  stock := fun person _ => if person = creditor then 1 else 10
  claims := fun _ _ _ => 0
  technology := false
  clock := 0
  round := 0

def request (signer : Party) (operation : Operation Party Unit Bool Unit) : Command :=
  ⟨signer, [], signer, [], operation⟩

def issue : Command := request controller (.issue () controller creditor 6)
def settle : Command := request controller (.settle () controller creditor 6)
def destroy : Command := request controller (.revise controller true)
def levy : Command := request controller (.transfer exposed controller [((), 6)])
def restore (amount : ℚ) : Command := request controller (.transfer controller exposed [((), amount)])

def peace : Word := [settle]
def imposed : Word := [destroy, levy, settle]
def reattached (amount : ℚ) : Word := imposed ++ [restore amount]

def input : ProgrammeSource.Input Party Unit Party Bool Unit where
  law := law
  initial := initial
  instructions := [issue]

def cut : State := ProgrammeSource.rawCurrent input (ProgrammeHistory.visitAt input 2).current
def opening := Financial.accountAt input 2

def paid (word : Word) : State := (law.execute cut 0 word).final

def stock (current : State) : Party → ℚ := fun party => current.stock party ()
def total (current : State) : ℚ := stock current controller + stock current creditor + stock current exposed
def pressure (word : Word) : ℚ := stock (paid word) controller - stock (paid peace) controller

theorem original_issue_and_account :
    cut.claims () controller creditor = 6 ∧
      ((opening.current.slots.map (Financial.slotClaim input)).map (fun claim =>
        (claim.instruction.index, claim.debtor, claim.holder, claim.quantity))) =
        [(0, controller, creditor, 6)] ∧
      Financial.outstanding input opening.current = 6 := by
  decide +kernel

theorem one_old_policy_opens_exposure_only_after_paid_destruction :
    ¬ law.Valid cut levy ∧ law.Valid cut destroy ∧
      law.Valid (law.step cut destroy) levy ∧
      law.actualDebit cut destroy = [((controller, ()), 2)] ∧
      law.actualCredit cut destroy = [] := by
  decide +kernel

theorem admitted_words_are_wholly_paid :
    (∀ item ∈ law.rawItems cut peace, law.Valid item.before item.request) ∧
      (∀ item ∈ law.rawItems cut imposed, law.Valid item.before item.request) ∧
      (∀ item ∈ law.rawItems cut (reattached 6), law.Valid item.before item.request) := by
  decide +kernel

theorem exposed_address_pays_the_same_old_principal :
    (paid [destroy, levy]).claims () controller creditor = 6 ∧
      stock (paid [destroy, levy]) exposed = 4 ∧
      (paid peace).claims () controller creditor = 0 ∧
      (paid imposed).claims () controller creditor = 0 ∧
      (paid (reattached 6)).claims () controller creditor = 0 ∧
      stock (paid peace) creditor = 7 ∧ stock (paid imposed) creditor = 7 ∧
      stock (paid (reattached 6)) creditor = 7 := by
  decide +kernel

theorem liability_reattachment_reverses_pressure_without_reversing_destruction :
    pressure imposed = 4 ∧ pressure (reattached 6) = -2 ∧
      stock (paid peace) exposed = 10 ∧ stock (paid imposed) exposed = 4 ∧
      stock (paid (reattached 6)) exposed = 10 ∧
      total (paid peace) = total cut ∧
      total (paid imposed) = total cut - 2 ∧ total (paid (reattached 6)) = total cut - 2 := by
  decide +kernel

theorem the_first_indifferent_cash_payment_is_four :
    pressure (reattached 4) = 0 ∧ law.Valid (paid imposed) (restore 4) ∧
      ¬ law.Valid (paid imposed) (restore 9) := by
  decide +kernel

#print axioms original_issue_and_account
#print axioms one_old_policy_opens_exposure_only_after_paid_destruction
#print axioms exposed_address_pays_the_same_old_principal
#print axioms liability_reattachment_reverses_pressure_without_reversing_destruction

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers
