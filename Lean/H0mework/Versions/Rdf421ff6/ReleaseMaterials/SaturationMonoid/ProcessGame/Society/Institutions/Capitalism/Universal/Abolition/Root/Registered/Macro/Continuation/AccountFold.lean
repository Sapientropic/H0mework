import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.State

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation

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

local notation "C" => Accounting.Current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "accountAt" => Inventory.accountAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal

/-- This is the source fold equation to carry through actual macro visits.
It supplies no new account, financial instruction, or occurrence. -/
def AccountIsSourceFold (current : C) : Prop := current.account = accountAt current.position

theorem initial_account_is_the_original_source_fold :
    AccountIsSourceFold (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
      (Accounting.initial (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition) := rfl

theorem next_preserves_the_original_source_account_fold (current : C)
    (same : AccountIsSourceFold (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      start proposal sourcePosition current) :
    AccountIsSourceFold (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
      (Accounting.next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current) := by
  rcases current with ⟨phase⟩
  cases phase with
  | none => rfl
  | some account =>
      cases found : Accounting.Account.item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
          start proposal sourcePosition account with
      | none =>
          change account.account = accountAt account.position at same
          change (Accounting.Account.nextFrom (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
            start proposal sourcePosition account
            (Accounting.Account.item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
              start proposal sourcePosition account)).account =
              accountAt (Accounting.Account.nextFrom (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
                start proposal sourcePosition account
                (Accounting.Account.item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
                  start proposal sourcePosition account)).position
          rw [found]
          exact same
      | some item =>
          change account.account = accountAt account.position at same
          change (Accounting.Account.nextFrom (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
            start proposal sourcePosition account
            (Accounting.Account.item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
              start proposal sourcePosition account)).account =
              accountAt (Accounting.Account.nextFrom (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
                start proposal sourcePosition account
                (Accounting.Account.item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
                  start proposal sourcePosition account)).position
          rw [found]
          change (Epoch.Finance.consume input depth count item account.account).next input depth count =
            accountAt (account.position + 1)
          rw [Inventory.one_item_is_one_native_transition (review := review) input depth count prefixLimit renewalLimit
            sourceDepth sourceCount start proposal account.position item found]
          rw [same]

#print axioms initial_account_is_the_original_source_fold
#print axioms next_preserves_the_original_source_account_fold

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation
