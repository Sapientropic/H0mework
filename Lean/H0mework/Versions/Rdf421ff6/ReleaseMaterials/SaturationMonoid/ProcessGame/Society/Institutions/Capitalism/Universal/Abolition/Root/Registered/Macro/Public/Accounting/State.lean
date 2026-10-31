import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Inventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)
  (anchor : (Epoch.Finance.process input depth count).GeneratedState)

structure FinancialCurrent where
  private mk ::
  position : Nat
  account : (Epoch.Finance.process input depth count).GeneratedState
  native : Nonempty ((Epoch.Finance.process input depth count).Run anchor.current account.current)

/-- `none` is the unique unexecuted body. Financial steps can only occur
after that body; they carry the same complete original account. -/
structure Current where
  private mk ::
  progress : Option (FinancialCurrent input depth count anchor)

namespace Current

variable {input depth count anchor}

def bodyPaid (current : Current input depth count anchor) := current.progress.isSome

def position (current : Current input depth count anchor) : Nat :=
  current.progress.map FinancialCurrent.position |>.getD 0

def account (current : Current input depth count anchor) : (Epoch.Finance.process input depth count).GeneratedState :=
  current.progress.map FinancialCurrent.account |>.getD anchor

theorem native (current : Current input depth count anchor) :
    Nonempty ((Epoch.Finance.process input depth count).Run anchor.current current.account.current) := by
  rcases current with ⟨progress⟩
  cases progress with
  | none => exact ⟨.nil⟩
  | some financial => exact financial.native

def afterItem (current : Current input depth count anchor)
    (paid : current.bodyPaid = true) (item : Epoch.Finance.ActualItem input depth count) :
    Current input depth count anchor := by
  rcases current with ⟨progress⟩
  cases progress with
  | none => cases paid
  | some financial =>
      exact ⟨some ⟨financial.position + 1,
        (Epoch.Finance.consume input depth count item financial.account).next input depth count,
        financial.native.map fun prior => prior.concatRuns (Epoch.Finance.process input depth count)
          ((Epoch.Finance.consume input depth count item financial.account).transition input depth count)⟩⟩

def afterIssued (current : Current input depth count anchor)
    (_paid : current.bodyPaid = true) (claim : Epoch.Finance.NewClaim input depth count) :
    Current input depth count (current.account.step (Epoch.Finance.process input depth count) (.admit (.inr claim))) :=
  ⟨some ⟨current.position + 1, _, ⟨.nil⟩⟩⟩

theorem after_item_reads_the_source_generated_native_account
    (current : Current input depth count anchor) (paid : current.bodyPaid = true)
    (item : Epoch.Finance.ActualItem input depth count) :
    (current.afterItem paid item).account =
      (Epoch.Finance.consume input depth count item current.account).next input depth count ∧
      (current.afterItem paid item).position = current.position + 1 ∧
      (current.afterItem paid item).bodyPaid = true := by
  rcases current with ⟨progress⟩
  cases progress with
  | none => cases paid
  | some financial => exact ⟨rfl, rfl, rfl⟩

end Current

def initial : Current input depth count anchor := ⟨none⟩

def bodyTarget : Current input depth count anchor := ⟨some ⟨0, anchor, ⟨.nil⟩⟩⟩

variable {input depth count anchor}

theorem the_unexecuted_body_is_the_original_initial_state
    (current : Current input depth count anchor) (unpaid : current.bodyPaid ≠ true) :
    current = initial input depth count anchor := by
  rcases current with ⟨progress⟩
  cases progress with
  | none => rfl
  | some financial => exact False.elim (unpaid rfl)

theorem the_first_body_preserves_the_literal_original_account :
    (bodyTarget input depth count anchor).account = (initial input depth count anchor).account ∧
      (bodyTarget input depth count anchor).position = 0 ∧
      (bodyTarget input depth count anchor).bodyPaid = true := ⟨rfl, rfl, rfl⟩

#print axioms initial
#print axioms the_first_body_preserves_the_literal_original_account

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting
