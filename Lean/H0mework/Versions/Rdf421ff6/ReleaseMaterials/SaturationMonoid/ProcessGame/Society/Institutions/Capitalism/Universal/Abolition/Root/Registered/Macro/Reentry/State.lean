import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.State
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Continuation.Family

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument)
  {review : Option (ReviewPhase.ContextAt input)}
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (family : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)
  (seed_eq : Accounting.seedAccount (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0 = anchor)

local notation "C" => Accounting.Current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0
local notation "advance" => Accounting.next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0

/- This equality is an internal splice paid by the complete original input
fold. The state and account remain the existing Accounting values. -/
include seed_eq in
theorem nativeTail (current : C) : Epoch.Finance.Future.Continuation.NativeTail input depth count anchor current.account := by
  rw [← seed_eq]
  exact current.native

def supportAt (current : C) : world.Support :=
  family.support current.account (nativeTail (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal seed_eq current)

def owner (current : C) : OpenResponsibilityAt world
    (supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq current) :=
  family.owner current.account (nativeTail (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal seed_eq current)

private theorem support_congr {left right : (Epoch.Finance.process input depth count).GeneratedState}
    (leftTail : Epoch.Finance.Future.Continuation.NativeTail input depth count anchor left)
    (rightTail : Epoch.Finance.Future.Continuation.NativeTail input depth count anchor right)
    (same : left = right) : family.support left leftTail = family.support right rightTail := by
  cases same
  rfl

private def stationary (N : WorldRelationNetwork) (support : N.Support) :
    LedgerWriteEvolutionAt N ⟨support⟩ ⟨support⟩ where
  destination := fun entry => ⟨entry, .carried rfl HEq.rfl⟩
  origin := fun entry => ⟨entry, .carried rfl HEq.rfl⟩

private def castTransition {N : WorldRelationNetwork} {source before after : N.Support}
    (same : before = after) (evolution : LedgerWriteEvolutionAt N ⟨source⟩ ⟨before⟩)
    (keys : Financial.Installation.KeepsKeys evolution) :
    { generated : LedgerWriteEvolutionAt N ⟨source⟩ ⟨after⟩ // Financial.Installation.KeepsKeys generated } := by
  cases same
  exact ⟨evolution, keys⟩

def transition (current : C) :
    { generated : LedgerWriteEvolutionAt world
        ⟨supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq current⟩
        ⟨supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq (advance current)⟩ //
      Financial.Installation.KeepsKeys generated } := by
  let native := nativeTail (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal seed_eq current
  cases found : Accounting.item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0 current with
  | none =>
      have same := Accounting.account_next_of_empty (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0 current found
      exact castTransition (support_congr input depth count family _ _ same.symm)
        (stationary world (family.support current.account native)) ⟨fun _ => rfl, fun _ => rfl⟩
  | some item =>
      have same := Accounting.account_next_of_item (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0 current item found
      exact castTransition (support_congr input depth count family _ _ same.symm)
        (family.itemEvolution current.account native item) (family.item_keys current.account native item)

def wholeEvolution (current : C) :=
  (transition (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq current).val

theorem whole_keys (current : C) : Financial.Installation.KeepsKeys
    (wholeEvolution (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq current) :=
  (transition (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq current).property

theorem initial_support_is_the_same_current_world :
    supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq
      (Accounting.initial (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0) = family.currentSupport := by
  cases seed_eq
  rfl

include seed_eq in
theorem initial_account_is_the_same_current_account :
    (Accounting.initial (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0).account = anchor := seed_eq

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry.transition
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry.initial_support_is_the_same_current_world
