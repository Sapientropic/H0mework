import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Legacy.Run
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.ExecutedHistory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Financial.Installation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat)

/-- Read the actual carried account, not a replay indexed by a guessed depth. -/
def inheritedAccount : (process input depth count).GeneratedState :=
  Legacy.generated input depth count (Settlement.oldCursor input depth count).account

def inheritedPending : List (Origin input depth count) :=
  (Cursor.pending input (Settlement.oldCursor input depth count)).map Origin.original

/-- Pending requests remain visible even when a fresh old body has not yet
executed. This predicate admits only the original committed history prefix. -/
def AlreadyOccurred (original : Financial.InstructionOrigin input) : Prop :=
  (ProgrammeSource.rawCurrent input original.visit.current).round <
    input.initial.round + Settlement.physicalIndex input depth count

instance (original : Financial.InstructionOrigin input) : Decidable (AlreadyOccurred input depth count original) := by
  unfold AlreadyOccurred
  infer_instance

def committedPending : List (Financial.InstructionOrigin input) :=
  (Cursor.pending input (Settlement.oldCursor input depth count)).filter
    (fun original => decide (AlreadyOccurred input depth count original))

def deferredRequests : List (Financial.InstructionOrigin input) :=
  (Cursor.pending input (Settlement.oldCursor input depth count)).filter
    (fun original => decide (¬ AlreadyOccurred input depth count original))

theorem actual_pending_has_a_strictly_committed_origin
    (original : Financial.InstructionOrigin input)
    (member : original ∈ committedPending input depth count) :
    ∃ ordinal < Settlement.physicalIndex input depth count,
      original.visit = ProgrammeHistory.visitAt input ordinal := by
  obtain ⟨pending, observed⟩ := List.mem_filter.mp member
  have before := of_decide_eq_true observed
  obtain ⟨ordinal, _afterTick, same⟩ :=
    Cursor.pending_origin_has_actually_occurred input (Settlement.oldCursor input depth count) original pending
  unfold AlreadyOccurred at before
  rw [same, ProgrammeHistory.visit_round] at before
  exact ⟨ordinal, by omega, same⟩

theorem every_original_pending_request_is_retained
    (original : Financial.InstructionOrigin input)
    (member : original ∈ Cursor.pending input (Settlement.oldCursor input depth count)) :
    Origin.original original ∈ inheritedPending input depth count ∧
      (original ∈ committedPending input depth count ∨ original ∈ deferredRequests input depth count) := by
  refine ⟨List.mem_map.mpr ⟨original, member, rfl⟩, ?_⟩
  by_cases occurred : AlreadyOccurred input depth count original
  · exact Or.inl (List.mem_filter.mpr ⟨member, decide_eq_true occurred⟩)
  · exact Or.inr (List.mem_filter.mpr ⟨member, decide_eq_true occurred⟩)

theorem inherited_actual_account_is_not_restarted :
    (inheritedAccount input depth count).current.slots =
      (Settlement.oldCursor input depth count).account.current.slots.map (Legacy.slot input depth count) ∧
    (inheritedAccount input depth count).current.history =
      (Settlement.oldCursor input depth count).account.current.history.map (Legacy.lifecycle input depth count) :=
  Legacy.every_slot_and_history_entry_is_retained input depth count _

theorem new_actor_keeps_the_carried_old_slot_count {tag : Interface.Tag input depth count} {visit : Interface.Visit input depth count tag} {party : Party}
    (_born : Interface.Actors.At input depth count tag visit party) :
    (inheritedAccount input depth count).current.slots.length =
      (Settlement.oldCursor input depth count).account.current.slots.length := by
  rw [(inherited_actual_account_is_not_restarted input depth count).1]
  exact List.length_map _

theorem new_actor_keeps_every_original_pending_position {tag : Interface.Tag input depth count} {visit : Interface.Visit input depth count tag} {party : Party}
    (_born : Interface.Actors.At input depth count tag visit party) :
    (inheritedPending input depth count).length =
      (Cursor.pending input (Settlement.oldCursor input depth count)).length := List.length_map _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.inherited_actual_account_is_not_restarted
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.actual_pending_has_a_strictly_committed_origin
