import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Allocation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial

open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def outstanding (state : ResponsibilityState (vocabulary input)) : ℚ :=
  (state.slots.map (fun slot => total input (slotBalance input slot))).sum

theorem admit_outstanding (state : (process input).GeneratedState) (claim : IssuedClaim input) :
    outstanding input (admit input state claim).current =
      outstanding input state.current + claim.quantity := by
  change ((state.current.slots ++ [ObligationSlot.live (admission input claim).toObligation]).map _).sum = _
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, slotBalance]
  exact congrArg (outstanding input state.current + ·) (initial_total input claim)

theorem cross_outstanding (state : (process input).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary input))
    (present : state.current.slots.get index = .live obligation)
    (boundary : Boundary input obligation) :
    outstanding input (cross input state index obligation present boundary).current =
      outstanding input state.current - total input obligation.residual +
        total input (boundary.event.after input) := by
  unfold outstanding
  change ((state.current.slots.set index (boundaryDisposition input boundary).targetSlot).map _).sum = _
  rw [List.map_set, List.sum_set']
  simp only [List.length_map, index.isLt, ↓reduceDIte, List.getElem_map]
  have row : state.current.slots[index.val] = .live obligation := present
  rw [row, boundary_balance]
  change _ + (-total input obligation.residual + total input (boundary.event.after input)) = _
  ring

theorem allocateLive_outstanding (state : (process input).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary input))
    (present : state.current.slots.get index = .live obligation)
    (receipt : Review input obligation.content) (available : ℚ) (nonnegative : 0 ≤ available) :
    outstanding input (allocateLive input state index obligation present receipt available nonnegative).after.current =
      outstanding input state.current -
        match receipt.kind with
        | .payment _ => (allocateLive input state index obligation present receipt available nonnegative).used input
        | .assignment _ _ => 0 := by
  let cap := min available receipt.quantity
  let sound := live_sound input state index obligation present
  let boundary := reviewBoundary input obligation sound.1 receipt cap sound.2
    (le_min nonnegative (receipt.quantity_nonnegative input)) (min_le_right _ _)
  change outstanding input (cross input state index obligation present boundary).current = _
  rw [cross_outstanding]
  change outstanding input state.current - total input obligation.residual +
      total input (receipt.after input obligation.residual cap) = _
  cases kind : receipt.kind with
  | payment holder =>
      simp only [Review.after, kind, pay_total, Allocation.used, allocateLive]
      ring
  | assignment sender recipient =>
      simp only [Review.after, kind, assign_total, sub_zero]
      ring

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial
