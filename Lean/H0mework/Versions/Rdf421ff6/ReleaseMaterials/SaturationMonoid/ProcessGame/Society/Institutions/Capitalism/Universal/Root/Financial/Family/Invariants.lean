import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family

open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

def admit (state : (process sources).GeneratedState) (claim : Claim sources) : (process sources).GeneratedState :=
  state.step (process sources) (.admit claim)

def cross (state : (process sources).GeneratedState)
    (slot : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary sources))
    (present : state.current.slots.get slot = .live obligation) (boundary : Boundary sources obligation) :
    (process sources).GeneratedState := state.step (process sources) (.cross slot obligation present boundary)

def slotObligation : ObligationSlot (vocabulary sources) → AdmittedObligation (vocabulary sources)
  | .live obligation => obligation
  | .terminal archive => archive.obligation

def slotBalance : ObligationSlot (vocabulary sources) → Shares (Party := Party)
  | .live obligation => obligation.residual
  | .terminal _ => 0

def slotClaim (slot : ObligationSlot (vocabulary sources)) : Claim sources :=
  (slotObligation sources slot).content

def SlotSound (slot : ObligationSlot (vocabulary sources)) : Prop :=
  Coherent sources (slotObligation sources slot) ∧ (∀ holder, 0 ≤ slotBalance sources slot holder)

def Sound (state : ResponsibilityState (vocabulary sources)) : Prop :=
  ∀ slot ∈ state.slots, SlotSound sources slot

omit [DecidableEq Port] in
theorem Event.after_nonnegative (event : Event sources) (lawful : event.Lawful sources) :
    ∀ holder, 0 ≤ event.after sources holder := by
  cases event with
  | birth claim => exact initial_nonnegative (sources claim.1) claim.2
  | review claim receipt before cap => exact receipt.after_nonnegative sources before cap lawful.1 lawful.2.1

theorem boundary_sound {obligation : AdmittedObligation (vocabulary sources)}
    (boundary : Boundary sources obligation) (coherent : Coherent sources obligation) :
    SlotSound sources (Boundary.disposition sources boundary).targetSlot := by
  unfold Boundary.disposition
  split
  · exact ⟨coherent, fun _ => le_refl 0⟩
  · exact ⟨coherent, boundary.receipt.after_nonnegative sources obligation.residual boundary.cap boundary.nonnegative boundary.available⟩

theorem boundary_claim {obligation : AdmittedObligation (vocabulary sources)}
    (boundary : Boundary sources obligation) :
    slotClaim sources (Boundary.disposition sources boundary).targetSlot = obligation.content := by
  unfold Boundary.disposition
  split <;> rfl

theorem boundary_balance {obligation : AdmittedObligation (vocabulary sources)}
    (boundary : Boundary sources obligation) :
    slotBalance sources (Boundary.disposition sources boundary).targetSlot = (boundary.event sources).after sources := by
  unfold Boundary.disposition
  split
  · rename_i cleared
    exact cleared.symm
  · rfl

theorem edge_sound {state : ResponsibilityState (vocabulary sources)}
    (sound : Sound sources state) (edge : (process sources).Edge state) :
    Sound sources edge.target := by
  intro slot member
  cases edge with
  | admit claim =>
      rcases List.mem_append.mp member with old | fresh
      · exact sound slot old
      · have same : slot = .live (admission sources claim).toObligation := by
          simpa only [List.mem_singleton, process] using fresh
        subst slot
        exact ⟨(show Coherent sources (admission sources claim).toObligation from ⟨rfl, rfl, rfl, rfl⟩), initial_nonnegative (sources claim.1) claim.2⟩
  | cross index obligation present boundary =>
      rcases List.mem_or_eq_of_mem_set member with old | changed
      · exact sound slot old
      · subst slot
        have original := sound (.live obligation) (present ▸ List.get_mem state.slots index)
        exact boundary_sound sources boundary original.1
  | reopen _ _ _ impossible => exact impossible.elim

theorem generated_sound (state : (process sources).GeneratedState) : Sound sources state.current := by
  rcases state with ⟨state, generated⟩
  induction generated with
  | nil => exact fun _ member => (List.not_mem_nil member).elim
  | step prior edge ih => exact edge_sound sources ih edge

theorem live_sound (state : (process sources).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary sources))
    (present : state.current.slots.get index = .live obligation) :
    Coherent sources obligation ∧ (∀ holder, 0 ≤ obligation.residual holder) :=
  generated_sound sources state (.live obligation) (present ▸ List.get_mem state.current.slots index)

theorem cross_length (state : (process sources).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary sources))
    (present : state.current.slots.get index = .live obligation)
    (boundary : Boundary sources obligation) :
    (cross sources state index obligation present boundary).current.slots.length =
      state.current.slots.length := List.length_set

theorem cross_retains_all_claims (state : (process sources).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary sources))
    (present : state.current.slots.get index = .live obligation)
    (boundary : Boundary sources obligation) :
    (cross sources state index obligation present boundary).current.slots.map (slotClaim sources) =
      state.current.slots.map (slotClaim sources) := by
  change (state.current.slots.set index (Boundary.disposition sources boundary).targetSlot).map _ = _
  rw [List.map_set, boundary_claim]
  apply List.ext_getElem
  · simp
  · intro position left right
    rw [List.getElem_set]
    split
    · rename_i same
      subst position
      simpa only [List.getElem_map, List.get_eq_getElem, slotClaim, slotObligation]
        using (congrArg (slotClaim sources) present).symm
    · rfl

theorem cross_keeps_history (state : (process sources).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary sources))
    (present : state.current.slots.get index = .live obligation)
    (boundary : Boundary sources obligation) :
    state.current.history <+:
      (cross sources state index obligation present boundary).current.history :=
  NativeResponsibilityProcess.Edge.history_prefix (process sources) _

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family
