import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Continuation.Installed
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.State

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

def accountingFamily (current : C) : Epoch.Finance.Future.Continuation.AccountFamily input depth count
    (Accounting.N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition) current.account :=
  Epoch.Finance.Future.Installed.accountFamily input depth count sourceDepth sourceCount
    (Accounting.seedRun (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
    current.account current.native

theorem same_source_step_reads_the_literal_next_support (current : C) :
    (accountingFamily (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      start proposal sourcePosition current).support
      (Accounting.next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current).account
      ⟨Accounting.nativeTransition (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current⟩ =
    Accounting.supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
      (Accounting.next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current) := by
  rcases current with ⟨phase⟩
  cases phase <;> rfl

/-- The next batch can consume the current root's literal account and
support. The original mapped ingress is excluded until its body has actually
crossed Enter; no financial item is used to pay that boundary. -/
theorem completed_body_uses_the_literal_existing_financial_world (current : C)
    (paid : Accounting.bodyPaid (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      start proposal sourcePosition current = true) :
    (accountingFamily (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      start proposal sourcePosition current).N =
        Accounting.N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition ∧
    (accountingFamily (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      start proposal sourcePosition current).initial = current.account ∧
    (accountingFamily (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      start proposal sourcePosition current).currentSupport =
        Accounting.supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current := by
  rcases current with ⟨phase⟩
  cases phase with
  | none => cases paid
  | some account => exact ⟨rfl, rfl, rfl⟩

theorem generated_body_supplies_its_own_continuation_base (current : C) :
    type_of% (completed_body_uses_the_literal_existing_financial_world (review := review) input depth count prefixLimit renewalLimit
      sourceDepth sourceCount start proposal sourcePosition
      (Accounting.next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current)
      (Accounting.every_generated_next_has_a_completed_body (review := review) input depth count prefixLimit renewalLimit
        sourceDepth sourceCount start proposal sourcePosition current)) :=
  completed_body_uses_the_literal_existing_financial_world (review := review) input depth count prefixLimit renewalLimit
    sourceDepth sourceCount start proposal sourcePosition
    (Accounting.next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current)
    (Accounting.every_generated_next_has_a_completed_body (review := review) input depth count prefixLimit renewalLimit
      sourceDepth sourceCount start proposal sourcePosition current)

#print axioms accountingFamily
#print axioms same_source_step_reads_the_literal_next_support
#print axioms completed_body_uses_the_literal_existing_financial_world
#print axioms generated_body_supplies_its_own_continuation_base

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation
