import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.Account

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument)
  (sourcePosition : Nat)
  (review : Option (ReviewPhase.ContextAt input) := none)

abbrev seedAccount := Inventory.accountAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
abbrev seedRun := Inventory.completeRun (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
abbrev N := Epoch.Finance.Future.world input depth count
  (Epoch.Finance.Future.Installed.base input depth count sourceDepth sourceCount)
  (Inventory.baseAccount input depth count sourceDepth sourceCount)
  (seedRun (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)

structure Current where
  private mk ::
  position : Nat
  account : (Epoch.Finance.process input depth count).GeneratedState
  native : Nonempty ((Epoch.Finance.process input depth count).Run
    (seedAccount (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).current account.current)

def initial : Current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition :=
  ⟨sourcePosition, seedAccount (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition, ⟨.nil⟩⟩

variable (current : Current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)

def item? := (Inventory.items (review := review) input depth count prefixLimit renewalLimit start proposal)[current.position]?

def nextFrom : Option (Epoch.Finance.ActualItem input depth count) →
    Current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
  | some item => ⟨current.position + 1,
      (Epoch.Finance.consume input depth count item current.account).next input depth count,
      current.native.map fun prior => prior.concatRuns (Epoch.Finance.process input depth count)
        ((Epoch.Finance.consume input depth count item current.account).transition input depth count)⟩
  | none => current

def next := nextFrom (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current
  (item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current)

def transitionFrom : (selected : Option (Epoch.Finance.ActualItem input depth count)) →
    (Epoch.Finance.process input depth count).Run current.account.current
      (nextFrom (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current selected).account.current
  | some item => (Epoch.Finance.consume input depth count item current.account).transition input depth count
  | none => .nil

def nativeTransition := transitionFrom (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current
  (item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current)

def supportAt : (N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).Support :=
  Epoch.Finance.Future.Installed.support input depth count sourceDepth sourceCount
    (seedRun (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
    current.account current.native

def owner := Epoch.Finance.Future.Installed.owner input depth count sourceDepth sourceCount
  (seedRun (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  current.account current.native

private def stationary (world : WorldRelationNetwork) (support : world.Support) :
    LedgerWriteEvolutionAt world ⟨support⟩ ⟨support⟩ where
  destination := fun entry => ⟨entry, .carried rfl HEq.rfl⟩
  origin := fun entry => ⟨entry, .carried rfl HEq.rfl⟩

def evolutionFrom : (selected : Option (Epoch.Finance.ActualItem input depth count)) →
    LedgerWriteEvolutionAt
      (N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
      ⟨supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current⟩
      ⟨supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
        (nextFrom (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current selected)⟩
  | some item => Epoch.Finance.Future.Installed.itemEvolution input depth count sourceDepth sourceCount
      (seedRun (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
      current.account current.native item
  | none => stationary _ _

def wholeEvolution := evolutionFrom (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current
  (item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current)

def pending := (Inventory.items (review := review) input depth count prefixLimit renewalLimit start proposal).drop current.position

def physical (_current : Current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition) := Physical.stateAt input depth count prefixLimit renewalLimit
  (Inventory.physicalAfter (review := review) input depth count prefixLimit renewalLimit start proposal).past

theorem accounting_does_not_replay_the_body :
    physical (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
        (next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current) =
      physical (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current := rfl

theorem every_existing_row_keeps_its_original_claim
    (entry : OpenResponsibilityAt
      (N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
      (supportAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current)) :
    ((wholeEvolution (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current).destination entry).1.claim = entry.claim :=
  ((wholeEvolution (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current).destination entry).2.toDebtLineage.claim_eq.symm

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.Account
