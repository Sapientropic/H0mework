import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Instruction
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Inherited

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat)

private def consumeItems : List (ActualItem input depth count) →
    (process input depth count).GeneratedState → (process input depth count).GeneratedState
  | [], state => state
  | origin :: rest, state =>
      consumeItems rest ((consume input depth count origin state).next input depth count)

private def consumeItems_run (origins : List (ActualItem input depth count))
    (state : (process input depth count).GeneratedState) :
    (process input depth count).Run state.current
      (consumeItems input depth count origins state).current := by
  induction origins generalizing state with
  | nil => exact .nil
  | cons origin rest ih =>
      exact ((consume input depth count origin state).transition input depth count).concatRuns
        (process input depth count)
        (ih ((consume input depth count origin state).next input depth count))

private theorem consumeItems_claims (origins : List (ActualItem input depth count))
    (state : (process input depth count).GeneratedState) :
    state.current.slots.map (slotClaim input depth count) <+:
      (consumeItems input depth count origins state).current.slots.map (slotClaim input depth count) := by
  induction origins generalizing state with
  | nil => exact List.prefix_rfl
  | cons origin rest ih =>
      exact ((consume input depth count origin state).original_claims_retained input depth count).trans
        (ih ((consume input depth count origin state).next input depth count))

/-- Enumerate this occurrence's real positions once; no caller list is used
as the public source of new financial origins. -/
def inventory (tag : Interface.Tag input depth count) (visit : Interface.Visit input depth count tag) : List (ActualItem input depth count) :=
  List.ofFn fun position => Interface.ActualOccurrence.item input depth count ⟨tag, visit, position⟩

theorem inventory_is_exact (tag : Interface.Tag input depth count) (visit : Interface.Visit input depth count tag) :
    (inventory input depth count tag visit).map (ActualItem.instruction input depth count) =
      (Interface.execution input depth count tag visit.current).items := by
  calc
    _ = (List.ofFn fun position => (⟨tag, visit, position⟩ : ActualItem input depth count)).map
        (ActualItem.instruction input depth count) := by
      simp only [inventory, List.map_ofFn, Function.comp_def]
      apply congrArg List.ofFn
      funext position
      exact Interface.ActualOccurrence.item_instruction input depth count _
    _ = _ := by
      simp only [List.map_ofFn, Function.comp_def, ActualItem.instruction,
        Interface.ActualItem.instruction, List.ofFn_get]

theorem inventory_positions_are_not_replayed (tag : Interface.Tag input depth count) (visit : Interface.Visit input depth count tag) :
    (inventory input depth count tag visit).Nodup := by
  apply List.nodup_ofFn.mpr
  intro first second same
  apply Fin.ext
  have positions := congrArg (fun item : ActualItem input depth count => item.position.val) same
  simpa only [Interface.ActualOccurrence.item_position] using positions

theorem inventory_is_the_same_shared_occurrence (tag : Interface.Tag input depth count)
    (visit : Interface.Visit input depth count tag) :
    inventory input depth count (Interface.ActualOccurrence.tagOf input depth count tag visit)
      (Interface.ActualOccurrence.visitOf input depth count tag visit) = inventory input depth count tag visit := by
  cases tag <;> rfl

def consumeVisit (tag : Interface.Tag input depth count) (visit : Interface.Visit input depth count tag)
    (state : (process input depth count).GeneratedState) : (process input depth count).GeneratedState :=
  consumeItems input depth count (inventory input depth count tag visit) state

theorem shared_occurrence_has_one_financial_update (tag : Interface.Tag input depth count)
    (visit : Interface.Visit input depth count tag) (state : (process input depth count).GeneratedState) :
    consumeVisit input depth count (Interface.ActualOccurrence.tagOf input depth count tag visit)
      (Interface.ActualOccurrence.visitOf input depth count tag visit) state = consumeVisit input depth count tag visit state := by
  unfold consumeVisit
  rw [inventory_is_the_same_shared_occurrence]

def consumeVisit_run (tag : Interface.Tag input depth count) (visit : Interface.Visit input depth count tag)
    (state : (process input depth count).GeneratedState) :
    (process input depth count).Run state.current (consumeVisit input depth count tag visit state).current :=
  consumeItems_run input depth count _ state

theorem consumeVisit_preserves_original_claims (tag : Interface.Tag input depth count) (visit : Interface.Visit input depth count tag)
    (state : (process input depth count).GeneratedState) :
    state.current.slots.map (slotClaim input depth count) <+:
      (consumeVisit input depth count tag visit state).current.slots.map (slotClaim input depth count) :=
  consumeItems_claims input depth count _ state

theorem actual_epoch_keeps_the_complete_inherited_history (tag : Interface.Tag input depth count) (visit : Interface.Visit input depth count tag) :
    (Settlement.oldCursor input depth count).account.current.history.map (Legacy.lifecycle input depth count) <+:
      (consumeVisit input depth count tag visit (inheritedAccount input depth count)).current.history :=
  Legacy.old_history_remains_a_prefix_of_every_native_extension input depth count _
    (consumeVisit_run input depth count tag visit (inheritedAccount input depth count))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.inventory_positions_are_not_replayed
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.actual_epoch_keeps_the_complete_inherited_history
