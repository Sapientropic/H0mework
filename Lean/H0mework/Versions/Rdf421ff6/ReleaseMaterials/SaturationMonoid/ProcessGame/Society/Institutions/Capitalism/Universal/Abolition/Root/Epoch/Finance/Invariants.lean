import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Lifecycle
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Review

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat)

def Coherent (obligation : AdmittedObligation (vocabulary input depth count)) : Prop :=
  obligation.admission.sourceEvent.claim input depth count = obligation.content ∧
  obligation.scope = obligation.content.origin input depth count ∧
  obligation.beneficiary = obligation.content ∧
  obligation.bearer = obligation.content.debtorActor input depth count

def slotObligation : ObligationSlot (vocabulary input depth count) →
    AdmittedObligation (vocabulary input depth count)
  | .live obligation => obligation
  | .terminal archive => archive.obligation

def slotClaim (slot : ObligationSlot (vocabulary input depth count)) :=
  (slotObligation input depth count slot).content

def slotBalance : ObligationSlot (vocabulary input depth count) → Financial.Balance input
  | .live obligation => obligation.residual
  | .terminal _ => 0

def SlotSound (slot : ObligationSlot (vocabulary input depth count)) : Prop :=
  Coherent input depth count (slotObligation input depth count slot) ∧
    Financial.Nonnegative input (slotBalance input depth count slot)

def Sound (state : ResponsibilityState (vocabulary input depth count)) : Prop :=
  ∀ slot ∈ state.slots, SlotSound input depth count slot

theorem admission_sound (claim : Claim input depth count) :
    SlotSound input depth count (.live (admission input depth count claim).toObligation) := by
  cases claim with
  | inl original => exact ⟨⟨rfl, rfl, rfl, rfl⟩, Financial.initial_nonnegative input original⟩
  | inr fresh => exact ⟨⟨rfl, rfl, rfl, rfl⟩,
      Event.after_nonnegative input depth count (.birth fresh) trivial⟩

theorem boundary_sound {obligation : AdmittedObligation (vocabulary input depth count)}
    (boundary : Boundary input depth count obligation)
    (coherent : Coherent input depth count obligation) :
    SlotSound input depth count (boundaryDisposition input depth count boundary).targetSlot := by
  unfold boundaryDisposition
  split
  · exact ⟨coherent, fun _ => le_refl 0⟩
  · exact ⟨coherent, boundary.event.after_nonnegative input depth count boundary.lawful⟩

theorem boundary_claim {obligation : AdmittedObligation (vocabulary input depth count)}
    (boundary : Boundary input depth count obligation) :
    slotClaim input depth count (boundaryDisposition input depth count boundary).targetSlot =
      obligation.content := by unfold boundaryDisposition; split <;> rfl

theorem edge_sound {state : ResponsibilityState (vocabulary input depth count)}
    (sound : Sound input depth count state) (edge : (process input depth count).Edge state) :
    Sound input depth count edge.target := by
  intro slot member
  cases edge with
  | admit claim =>
      rcases List.mem_append.mp member with old | fresh
      · exact sound slot old
      · have same : slot = .live (admission input depth count claim).toObligation :=
          by simpa only [List.mem_singleton, process] using fresh
        exact same ▸ admission_sound input depth count claim
  | cross index obligation present boundary =>
      rcases List.mem_or_eq_of_mem_set member with old | changed
      · exact sound slot old
      · subst slot
        exact boundary_sound input depth count boundary
          (sound (.live obligation) (present ▸ List.get_mem state.slots index)).1
  | reopen _ _ _ impossible => exact impossible.elim

theorem generated_sound (state : (process input depth count).GeneratedState) :
    Sound input depth count state.current := by
  rcases state with ⟨state, generated⟩
  induction generated with
  | nil => exact fun _ member => (List.not_mem_nil member).elim
  | step prior edge ih => exact edge_sound input depth count ih edge

theorem live_sound (state : (process input depth count).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary input depth count))
    (present : state.current.slots.get index = .live obligation) :
    Coherent input depth count obligation ∧ Financial.Nonnegative input obligation.residual :=
  generated_sound input depth count state (.live obligation)
    (present ▸ List.get_mem state.current.slots index)

def reviewBoundary (obligation : AdmittedObligation (vocabulary input depth count))
    (coherent : Coherent input depth count obligation)
    (receipt : Review input depth count obligation.content)
    (remaining : ℚ) (nonnegative : Financial.Nonnegative input obligation.residual)
    (available : 0 ≤ remaining) (withinSource : remaining ≤ receipt.quantity) :
    Boundary input depth count obligation where
  event := .review obligation.content receipt obligation.residual remaining
  lawful := ⟨nonnegative, available, withinSource⟩
  content_eq := rfl
  before_eq := rfl
  owns := {
    anchor_eq := by
      change MinimalRegistrableSourceAnchor.canonical
        (obligation.content.origin input depth count)
        (obligation.content.origin input depth count) =
        MinimalRegistrableSourceAnchor.canonical
          ((obligation.admission.sourceEvent.claim input depth count).origin input depth count)
          ((obligation.admission.sourceEvent.claim input depth count).origin input depth count)
      rw [coherent.1]
    incidence_eq := by
      change obligation.content.origin input depth count =
        (obligation.admission.sourceEvent.claim input depth count).origin input depth count
      rw [coherent.1] }
  scope_eq := coherent.2.1

theorem boundary_balance {obligation : AdmittedObligation (vocabulary input depth count)}
    (boundary : Boundary input depth count obligation) :
    slotBalance input depth count (boundaryDisposition input depth count boundary).targetSlot =
      boundary.event.after input depth count := by
  unfold boundaryDisposition
  split
  · rename_i cleared
    exact cleared.symm
  · rfl

theorem cross_retains_all_claims (state : (process input depth count).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary input depth count))
    (present : state.current.slots.get index = .live obligation)
    (boundary : Boundary input depth count obligation) :
    (state.step (process input depth count) (.cross index obligation present boundary)).current.slots.map
        (slotClaim input depth count) =
      state.current.slots.map (slotClaim input depth count) := by
  change (state.current.slots.set index (boundaryDisposition input depth count boundary).targetSlot).map _ = _
  rw [List.map_set, boundary_claim]
  apply List.ext_getElem
  · simp
  · intro position left right
    rw [List.getElem_set]
    split
    · rename_i same
      subst position
      simpa only [List.getElem_map, List.get_eq_getElem, slotClaim, slotObligation]
        using (congrArg (slotClaim input depth count) present).symm
    · rfl

theorem edge_retains_all_claims {state : ResponsibilityState (vocabulary input depth count)}
    (edge : (process input depth count).Edge state) :
    state.slots.map (slotClaim input depth count) <+: edge.target.slots.map (slotClaim input depth count) := by
  cases edge with
  | admit claim =>
      change _ <+: (state.slots ++ _).map _
      rw [List.map_append]
      exact List.prefix_append _ _
  | cross index obligation present boundary =>
      change Boundary input depth count obligation at boundary
      change _ <+: (state.slots.set index (boundaryDisposition input depth count boundary).targetSlot).map _
      rw [List.map_set, boundary_claim]
      have same : (state.slots.map (slotClaim input depth count)).set index obligation.content =
          state.slots.map (slotClaim input depth count) := by
        apply List.ext_getElem
        · simp
        · intro position left right
          rw [List.getElem_set]
          split
          · rename_i equal
            subst position
            simpa only [List.getElem_map, List.get_eq_getElem, slotClaim, slotObligation]
              using (congrArg (slotClaim input depth count) present).symm
          · rfl
      rw [same]
  | reopen _ _ _ impossible => exact impossible.elim

theorem run_retains_all_claims {before after : ResponsibilityState (vocabulary input depth count)}
    (run : (process input depth count).Run before after) :
    before.slots.map (slotClaim input depth count) <+: after.slots.map (slotClaim input depth count) := by
  induction run with
  | nil => exact List.prefix_rfl
  | step prior edge inherited => exact inherited.trans (edge_retains_all_claims input depth count edge)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance
