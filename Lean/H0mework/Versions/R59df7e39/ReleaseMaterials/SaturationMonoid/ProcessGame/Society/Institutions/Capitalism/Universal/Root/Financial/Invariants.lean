import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Lifecycle

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial

open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def slotObligation : ObligationSlot (vocabulary input) → AdmittedObligation (vocabulary input)
  | .live obligation => obligation
  | .terminal archive => archive.obligation

def slotBalance : ObligationSlot (vocabulary input) → Balance input
  | .live obligation => obligation.residual
  | .terminal _ => 0

def slotClaim (slot : ObligationSlot (vocabulary input)) : IssuedClaim input :=
  (slotObligation input slot).content

def SlotSound (slot : ObligationSlot (vocabulary input)) : Prop :=
  Coherent input (slotObligation input slot) ∧ Nonnegative input (slotBalance input slot)

def Sound (state : ResponsibilityState (vocabulary input)) : Prop :=
  ∀ slot ∈ state.slots, SlotSound input slot

omit [DecidableEq Port] in
theorem Event.after_nonnegative (event : Event input) (lawful : event.Lawful input) :
    Nonnegative input (event.after input) := by
  cases event with
  | birth claim => exact initial_nonnegative input claim
  | review claim receipt before remaining =>
      exact receipt.after_nonnegative input before remaining lawful.1 lawful.2.1

theorem boundary_sound {obligation : AdmittedObligation (vocabulary input)}
    (boundary : Boundary input obligation) (coherent : Coherent input obligation) :
    SlotSound input (boundaryDisposition input boundary).targetSlot := by
  unfold boundaryDisposition
  split
  · exact ⟨coherent, fun _ => le_refl 0⟩
  · exact ⟨coherent, boundary.event.after_nonnegative input boundary.lawful⟩

theorem boundary_claim {obligation : AdmittedObligation (vocabulary input)}
    (boundary : Boundary input obligation) :
    slotClaim input (boundaryDisposition input boundary).targetSlot = obligation.content := by
  unfold boundaryDisposition
  split <;> rfl

theorem boundary_balance {obligation : AdmittedObligation (vocabulary input)}
    (boundary : Boundary input obligation) :
    slotBalance input (boundaryDisposition input boundary).targetSlot = boundary.event.after input := by
  unfold boundaryDisposition
  split
  · rename_i cleared
    exact cleared.symm
  · rfl

theorem edge_sound {state : ResponsibilityState (vocabulary input)}
    (sound : Sound input state) (edge : (process input).Edge state) :
    Sound input edge.target := by
  intro slot member
  cases edge with
  | admit claim =>
      rcases List.mem_append.mp member with old | fresh
      · exact sound slot old
      · have same : slot = .live (admission input claim).toObligation := by
          simpa only [List.mem_singleton, process] using fresh
        subst slot
        exact ⟨admission_coherent input claim, initial_nonnegative input claim⟩
  | cross index obligation present boundary =>
      rcases List.mem_or_eq_of_mem_set member with old | changed
      · exact sound slot old
      · subst slot
        have original := sound (.live obligation) (present ▸ List.get_mem state.slots index)
        exact boundary_sound input boundary original.1
  | reopen _ _ _ impossible => exact impossible.elim

theorem generated_sound (state : (process input).GeneratedState) : Sound input state.current := by
  rcases state with ⟨state, generated⟩
  induction generated with
  | nil => exact fun _ member => (List.not_mem_nil member).elim
  | step prior edge ih => exact edge_sound input ih edge

theorem live_sound (state : (process input).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary input))
    (present : state.current.slots.get index = .live obligation) :
    Coherent input obligation ∧ Nonnegative input obligation.residual :=
  generated_sound input state (.live obligation) (present ▸ List.get_mem state.current.slots index)

theorem cross_length (state : (process input).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary input))
    (present : state.current.slots.get index = .live obligation)
    (boundary : Boundary input obligation) :
    (cross input state index obligation present boundary).current.slots.length =
      state.current.slots.length := List.length_set

theorem cross_retains_all_claims (state : (process input).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary input))
    (present : state.current.slots.get index = .live obligation)
    (boundary : Boundary input obligation) :
    (cross input state index obligation present boundary).current.slots.map (slotClaim input) =
      state.current.slots.map (slotClaim input) := by
  change (state.current.slots.set index (boundaryDisposition input boundary).targetSlot).map _ = _
  rw [List.map_set, boundary_claim]
  apply List.ext_getElem
  · simp
  · intro position left right
    rw [List.getElem_set]
    split
    · rename_i same
      subst position
      simpa only [List.getElem_map, List.get_eq_getElem, slotClaim, slotObligation]
        using (congrArg (slotClaim input) present).symm
    · rfl

theorem cross_keeps_history (state : (process input).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary input))
    (present : state.current.slots.get index = .live obligation)
    (boundary : Boundary input obligation) :
    state.current.history <+:
      (cross input state index obligation present boundary).current.history :=
  NativeResponsibilityProcess.Edge.history_prefix (process input) _

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial
