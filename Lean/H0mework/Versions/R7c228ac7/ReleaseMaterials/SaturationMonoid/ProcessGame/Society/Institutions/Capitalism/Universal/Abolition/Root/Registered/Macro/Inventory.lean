import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Registration
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase.Context
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Mandatory.Step
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.ActualPast.Fold

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inventory

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (current : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument)
  (review : Option (ReviewPhase.ContextAt input) := none)

abbrev eventCursor := Mandatory.executionCursor (review := review) input depth count prefixLimit renewalLimit current proposal
abbrev tag : Epoch.Interface.Tag input depth count :=
  .actual prefixLimit renewalLimit (eventCursor (review := review) input depth count prefixLimit renewalLimit current proposal)
abbrev visit := (Epoch.Interface.root input depth count
  (tag (review := review) input depth count prefixLimit renewalLimit current proposal)).initialVisit

def items := Epoch.Finance.inventory input depth count
  (tag (review := review) input depth count prefixLimit renewalLimit current proposal)
  (visit (review := review) input depth count prefixLimit renewalLimit current proposal)

abbrev baseAccount := Epoch.Finance.Future.Installed.initial input depth count sourceDepth sourceCount

def before := Epoch.Finance.ActualPast.account input depth count prefixLimit renewalLimit current.past
  (baseAccount input depth count sourceDepth sourceCount)

def beforeRun := Epoch.Finance.ActualPast.run input depth count prefixLimit renewalLimit current.past
  (baseAccount input depth count sourceDepth sourceCount)

/-- Only an already generated item position advances the accounting prefix. -/
def accountAt : Nat → (Epoch.Finance.process input depth count).GeneratedState
  | 0 => before input depth count prefixLimit renewalLimit sourceDepth sourceCount current
  | position + 1 =>
      let account := accountAt position
      match (items (review := review) input depth count prefixLimit renewalLimit current proposal)[position]? with
      | some item => (Epoch.Finance.consume input depth count item account).next input depth count
      | none => account

def runAt : (position : Nat) → (Epoch.Finance.process input depth count).Run
    (before input depth count prefixLimit renewalLimit sourceDepth sourceCount current).current
    (accountAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount current proposal position).current
  | 0 => .nil
  | position + 1 => by
      unfold accountAt
      split
      · rename_i item found
        exact (runAt position).concatRuns (Epoch.Finance.process input depth count)
          ((Epoch.Finance.consume input depth count item
            (accountAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount current proposal position)).transition input depth count)
      · exact runAt position

def completeRun (position : Nat) :=
  (beforeRun input depth count prefixLimit renewalLimit sourceDepth sourceCount current).concatRuns
    (Epoch.Finance.process input depth count)
    (runAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount current proposal position)

def pending (position : Nat) := (items (review := review) input depth count prefixLimit renewalLimit current proposal).drop position

def physicalAfter := Physical.next (eventCursor (review := review) input depth count prefixLimit renewalLimit current proposal)

theorem inventory_is_the_literal_physical_execution :
    (items (review := review) input depth count prefixLimit renewalLimit current proposal).map
      (Epoch.Finance.ActualItem.instruction input depth count) =
      (Physical.execution input depth count prefixLimit renewalLimit
        (eventCursor (review := review) input depth count prefixLimit renewalLimit current proposal)).items :=
  Epoch.Finance.inventory_is_exact input depth count _ _

theorem items_are_never_replayed :
    (items (review := review) input depth count prefixLimit renewalLimit current proposal).Nodup :=
  Epoch.Finance.inventory_positions_are_not_replayed input depth count _ _

theorem original_proposal_and_executed_opcode :
    (Mandatory.produce (review := review) input depth count prefixLimit renewalLimit current proposal).originalProposal = proposal ∧
      (eventCursor (review := review) input depth count prefixLimit renewalLimit current proposal).incoming =
        Mandatory.executionRaw (review := review) input depth count prefixLimit renewalLimit current proposal := ⟨rfl, rfl⟩

theorem one_item_is_one_native_transition (position : Nat)
    (item : Epoch.Finance.ActualItem input depth count)
    (found : (items (review := review) input depth count prefixLimit renewalLimit current proposal)[position]? = some item) :
    accountAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount current proposal (position + 1) =
      (Epoch.Finance.consume input depth count item
        (accountAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount current proposal position)).next input depth count := by
  simp only [accountAt, found]

theorem completed_inventory_has_no_pending :
    pending (review := review) input depth count prefixLimit renewalLimit current proposal
      (items (review := review) input depth count prefixLimit renewalLimit current proposal).length = [] := List.drop_length

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inventory

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inventory.inventory_is_the_literal_physical_execution
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inventory.completeRun
