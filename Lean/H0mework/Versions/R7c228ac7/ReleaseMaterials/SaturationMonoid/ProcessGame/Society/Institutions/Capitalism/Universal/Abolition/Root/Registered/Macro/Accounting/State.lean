import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.InitialLedger

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument) (sourcePosition : Nat)
  (review : Option (ReviewPhase.ContextAt input) := none)

abbrev seedAccount := Account.seedAccount (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
abbrev seedRun := Account.seedRun (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
abbrev N := Account.N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

local notation "A" => Account.Current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "seed" => Account.initial (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "ingress" => initialLedger (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

/-- The unique initial phase executes the physical request once. Financial
items become available only in the resulting accounting phase. -/
structure Current where
  private mk ::
  progress : Option A

namespace Current
variable {input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition}
variable {phase : Option (ReviewPhase.ContextAt input)}

def underlying (current : Current (review := phase) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition) := current.progress.getD (Account.initial (review := phase) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
def position (current : Current (review := phase) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition) := current.underlying.position
def account (current : Current (review := phase) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition) := current.underlying.account
theorem native (current : Current (review := phase) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition) :
    Nonempty ((Epoch.Finance.process input depth count).Run
      (seedAccount (review := phase) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).current current.account.current) :=
  current.underlying.native
end Current

local notation "C" => Current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

def initial : C := ⟨none⟩
def bodyPaid (current : C) := current.progress.isSome

def next : C → C
  | ⟨none⟩ => ⟨some seed⟩
  | ⟨some account⟩ => ⟨some (Account.next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition account)⟩

def item? : C → Option (Epoch.Finance.ActualItem input depth count)
  | ⟨none⟩ => none
  | ⟨some account⟩ => Account.item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition account

def writes : C → Bool
  | ⟨none⟩ => Physical.materialWrite input depth count prefixLimit renewalLimit
      (Inventory.eventCursor (review := review) input depth count prefixLimit renewalLimit start proposal)
  | ⟨some account⟩ => (Account.item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition account).isSome

def supportAt : C → (N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).Support
  | ⟨none⟩ => (ingress).1
  | ⟨some account⟩ => Account.supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition account

def owner (current : C) : OpenResponsibilityAt
    (N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
    (supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current) :=
  match current with
  | ⟨none⟩ => ((ingress).2.val.origin (Account.owner (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition seed)).1
  | ⟨some account⟩ => Account.owner (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition account

def wholeEvolution (current : C) : LedgerWriteEvolutionAt
    (N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
    ⟨supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current⟩
    ⟨supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
      (next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current)⟩ :=
  match current with
  | ⟨none⟩ => (ingress).2.val
  | ⟨some account⟩ => Account.wholeEvolution (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition account

def nativeTransition (current : C) : (Epoch.Finance.process input depth count).Run current.account.current
    (next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current).account.current :=
  match current with
  | ⟨none⟩ => .nil
  | ⟨some account⟩ => Account.nativeTransition (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition account

def pending (current : C) := (Inventory.items (review := review) input depth count prefixLimit renewalLimit start proposal).drop current.position

def physical : C → Actual.State (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument) (Port := Port)
  | ⟨none⟩ => Physical.stateAt input depth count prefixLimit renewalLimit start.past
  | ⟨some account⟩ => Account.physical (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition account

theorem account_next_of_item (current : C) (item : Epoch.Finance.ActualItem input depth count)
    (found : item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current = some item) :
    (next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current).account =
      (Epoch.Finance.consume input depth count item current.account).next input depth count := by
  rcases current with ⟨phase⟩
  cases phase with
  | none => cases found
  | some account =>
      change (Account.nextFrom (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition account
        (Account.item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition account)).account = _
      rw [show Account.item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition account = some item from found]
      rfl

theorem account_next_of_empty (current : C)
    (absent : item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current = none) :
    (next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current).account = current.account := by
  rcases current with ⟨phase⟩
  cases phase with
  | none => rfl
  | some account =>
      change (Account.nextFrom (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition account
        (Account.item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition account)).account = _
      rw [show Account.item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition account = none from absent]
      rfl

theorem first_body_keeps_the_entire_native_account :
    (next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
      (initial (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)).account =
    (initial (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).account := rfl

theorem first_body_releases_the_original_pending_inventory :
    pending (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
      (next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
        (initial (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)) =
      (Inventory.items (review := review) input depth count prefixLimit renewalLimit start proposal).drop sourcePosition := rfl

theorem the_first_body_has_no_admissible_financial_head :
    item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
      (initial (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition) = none := rfl

theorem every_generated_next_has_a_completed_body (current : C) :
    bodyPaid (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
      (next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current) = true := by
  rcases current with ⟨phase⟩
  cases phase <;> rfl

theorem first_body_is_the_same_physical_next :
    physical (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
      (next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
        (initial (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)) =
      Physical.stateAt input depth count prefixLimit renewalLimit
        (Physical.next (Inventory.eventCursor (review := review) input depth count prefixLimit renewalLimit start proposal)).past := rfl

theorem bookkeeping_does_not_replay_the_physical_body (current : C)
    (paid : bodyPaid (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current = true) :
    physical (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
        (next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current) =
      physical (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current := by
  rcases current with ⟨phase⟩
  cases phase with
  | none => cases paid
  | some account => rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting
