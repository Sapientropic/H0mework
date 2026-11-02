import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Migration

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Migration

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def received (event : Event input) (holder : Party) : ℚ := match event with
  | .birth _ => 0
  | .review _ receipt balance remaining => match receipt.kind with
      | .payment recipient => if holder = recipient then receipt.allocated input balance remaining else 0
      | .assignment .. => 0

def assigned (event : Event input) (holder : Party) : ℚ := match event with
  | .birth _ => 0
  | .review _ receipt balance remaining => match receipt.kind with
      | .payment _ => 0
      | .assignment sender recipient =>
          (if holder = recipient then receipt.allocated input balance remaining else 0) -
          (if holder = sender then receipt.allocated input balance remaining else 0)

omit [DecidableEq Port] in
theorem event_holder_conservation (event : Event input) (holder : Party) :
    event.after input holder + received input event holder =
      event.before input holder + assigned input event holder := by
  cases event with
  | birth => simp only [Event.after, Event.before, received, assigned, add_zero]
  | review claim receipt balance remaining =>
      cases kind : receipt.kind <;>
        simp only [Event.after, Event.before, received, assigned, Review.after, kind,
          pay_apply, assign_apply] <;> ring

omit [DecidableEq Port] in
theorem received_nonnegative (event : Event input) (lawful : event.Lawful input) (holder : Party) :
    0 ≤ received input event holder := by
  cases event with
  | birth => exact le_refl _
  | review claim receipt balance remaining =>
      cases kind : receipt.kind <;> simp only [received, kind]
      · split
        · exact receipt.allocated_nonnegative input balance remaining lawful.1 lawful.2.1
        · exact le_refl _
      · exact le_refl _

namespace Path

def receivedBy {first last} (path : Path input first last) (holder : Party) : ℚ :=
  ((path.events input).map (fun event => received input event holder)).sum

def assignedTo {first last} (path : Path input first last) (holder : Party) : ℚ :=
  ((path.events input).map (fun event => assigned input event holder)).sum

theorem holder_conservation {first last} (path : Path input first last) (holder : Party) :
    slotBalance input last holder + path.receivedBy input holder =
      slotBalance input first holder + path.assignedTo input holder := by
  induction path with
  | nil => simp only [receivedBy, assignedTo, events, List.map_nil, List.sum_nil, add_zero]
  | snoc prior boundary ih =>
      have step := event_holder_conservation input boundary.event holder
      rw [← boundary.before_eq] at step
      simp only [receivedBy, assignedTo, events, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [boundary_balance]
      change boundary.event.after input holder + (prior.receivedBy input holder + _) =
        slotBalance input first holder + (prior.assignedTo input holder + _)
      simp only [slotBalance] at ih ⊢
      linarith

theorem receivedBy_nonnegative {first last} (path : Path input first last) (holder : Party) :
    0 ≤ path.receivedBy input holder := by
  induction path with
  | nil => exact le_refl _
  | snoc prior boundary ih =>
      simp only [receivedBy, events, List.map_append, List.sum_append, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact add_nonneg ih (received_nonnegative input boundary.event boundary.lawful holder)

end Path
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Migration
