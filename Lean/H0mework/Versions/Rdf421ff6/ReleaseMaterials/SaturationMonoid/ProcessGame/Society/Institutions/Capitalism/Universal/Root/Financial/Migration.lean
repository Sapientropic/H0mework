import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.IssueTrace

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Migration

open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

/-- Erase only the mutable residual, retaining the complete dependent admission. -/
def identity (slot : ObligationSlot (vocabulary input)) : AdmittedObligation (vocabulary input) :=
  { slotObligation input slot with residual := 0 }

def sourceEvent : LifecycleEvent (vocabulary input) → Event input
  | .admitted _ payload => payload.sourceEvent
  | .carried _ _ source _ | .terminal _ _ source _
  | .superseded _ _ source _ | .bearerReleased _ _ source _ => source
  | .reopened _ _ payload => payload.sourceEvent

theorem boundary_identity {obligation : AdmittedObligation (vocabulary input)}
    (boundary : Boundary input obligation) :
    identity input (boundaryDisposition input boundary).targetSlot =
      identity input (.live obligation) := by
  unfold boundaryDisposition
  split <;> rfl

theorem cross_source {state : ResponsibilityState (vocabulary input)}
    (index : Fin state.slots.length) (obligation : AdmittedObligation (vocabulary input))
    (present : state.slots.get index = .live obligation) (boundary : Boundary input obligation) :
    sourceEvent input (NativeResponsibilityProcess.Edge.cross (P := process input) index obligation present boundary).lifecycleEvent =
      boundary.event := by
  dsimp only [NativeResponsibilityProcess.Edge.lifecycleEvent, process]
  unfold boundaryDisposition
  split <;> rfl

/-- The record is the complete dependent lifecycle event at the stable slot. -/
def record (index : Nat) {obligation : AdmittedObligation (vocabulary input)}
    (boundary : Boundary input obligation) : LifecycleEvent (vocabulary input) :=
  if cleared : boundary.event.after input = 0 then
    .terminal index obligation boundary.event (.fulfilled
      ⟨boundary.lawful, boundary.content_eq, boundary.scope_eq, cleared⟩)
  else .carried index obligation boundary.event (.progressed (boundary.event.after input)
    ⟨boundary.lawful, boundary.content_eq, boundary.before_eq, rfl⟩)

theorem record_source (index : Nat) {obligation : AdmittedObligation (vocabulary input)}
    (boundary : Boundary input obligation) : sourceEvent input (record input index boundary) = boundary.event := by
  unfold record
  split <;> rfl

theorem record_slot (index : Nat) {obligation : AdmittedObligation (vocabulary input)}
    (boundary : Boundary input obligation) : (record input index boundary).slot = index := by
  unfold record
  split <;> rfl

theorem cross_record {state : ResponsibilityState (vocabulary input)}
    (index : Fin state.slots.length) (obligation : AdmittedObligation (vocabulary input))
    (present : state.slots.get index = .live obligation) (boundary : Boundary input obligation) :
    (NativeResponsibilityProcess.Edge.cross (P := process input) index obligation present boundary).lifecycleEvent =
      record input index.val boundary := by
  dsimp only [NativeResponsibilityProcess.Edge.lifecycleEvent, process]
  unfold boundaryDisposition record
  split <;> rfl

/-- A dependent financial boundary computes its target. The public `Follow`
also certifies the full records against the supplied run. -/
inductive Path : ObligationSlot (vocabulary input) → ObligationSlot (vocabulary input) → Type
  | nil (slot) : Path slot slot
  | snoc {first} {obligation : AdmittedObligation (vocabulary input)}
      (prior : Path first (.live obligation)) (boundary : Boundary input obligation) :
      Path first (boundaryDisposition input boundary).targetSlot

namespace Path

def events {first last} : Path input first last → List (Event input)
  | .nil _ => []
  | .snoc prior boundary => prior.events ++ [boundary.event]

def records {first last} (index : Nat) : Path input first last → List (LifecycleEvent (vocabulary input))
  | .nil _ => []
  | .snoc prior boundary => prior.records index ++ [record input index boundary]

theorem records_sources {first last} (index : Nat) (path : Path input first last) :
    (path.records input index).map (sourceEvent input) = path.events input := by
  induction path with
  | nil => rfl
  | snoc prior boundary ih =>
      simp only [records, events, List.map_append, List.map_cons, List.map_nil, record_source, ih]

theorem preserves_identity {first last} (path : Path input first last) :
    identity input last = identity input first := by
  induction path with
  | nil => rfl
  | snoc prior boundary ih => exact (boundary_identity input boundary).trans ih

theorem terminal_is_unchanged {archive : TerminalArchive (vocabulary input)} {last}
    (path : Path input (.terminal archive) last) : last = .terminal archive := by
  have general {first last} (path : Path input first last) :
      ∀ archive, first = .terminal archive → last = .terminal archive := by
    induction path with
    | nil => intro archive same; exact same
    | snoc prior boundary ih =>
        intro archive same
        cases ih archive same
  exact general path archive rfl

end Path

structure Follow {first last : ResponsibilityState (vocabulary input)}
    (run : (process input).Run first last) (index : Nat) (original : ObligationSlot (vocabulary input)) where
  slot : ObligationSlot (vocabulary input)
  present : last.slots[index]? = some slot
  path : Path input original slot
  recorded : path.records input index = run.events.filter (fun event => event.slot == index)

theorem Follow.sourced {first last : ResponsibilityState (vocabulary input)}
    {run : (process input).Run first last} {index original}
    (result : Follow input run index original) :
    List.Sublist (result.path.events input) (run.events.map (sourceEvent input)) := by
  rw [← result.path.records_sources input index]
  apply List.Sublist.map
  rw [result.recorded]
  exact List.filter_sublist

def follow {first last : ResponsibilityState (vocabulary input)}
    (run : (process input).Run first last) (index : Nat) (original : ObligationSlot (vocabulary input))
    (present : first.slots[index]? = some original) : Follow input run index original :=
  match run with
  | .nil => ⟨original, present, .nil original, rfl⟩
  | .step prior edge => by
      rcases follow prior index original present with ⟨slot, atSlot, path, recorded⟩
      have inside := (List.getElem?_eq_some_iff.mp atSlot).choose
      cases edge with
      | admit claim =>
          refine ⟨slot, ?_, path, ?_⟩
          · exact (List.getElem?_append_left inside).trans atSlot
          · have different := Nat.ne_of_gt inside
            simpa only [NativeResponsibilityProcess.Run.events, List.filter_append,
              NativeResponsibilityProcess.Edge.lifecycleEvent, LifecycleEvent.slot,
              List.filter_cons, List.filter_nil, beq_iff_eq, different, if_false, List.append_nil] using recorded
      | cross changed obligation old boundary =>
          by_cases same : changed.val = index
          · have exactOld : slot = .live obligation := by
              have oldAt := congrArg some old
              have lookup := (List.getElem?_eq_getElem changed.isLt).trans oldAt
              rw [same] at lookup
              exact Option.some.inj (atSlot.symm.trans lookup)
            subst slot
            refine ⟨(boundaryDisposition input boundary).targetSlot, ?_, .snoc path boundary, ?_⟩
            · simpa only [same, process] using (process input).cross_target_slot changed obligation old boundary
            · simp only [Path.records, NativeResponsibilityProcess.Run.events, List.filter_append]
              rw [cross_record input changed obligation old boundary, same]
              simp only [List.filter_cons, List.filter_nil]
              rw [record_slot input index boundary]
              simp only [beq_self_eq_true, if_true]
              exact congrArg (fun records => records ++ [record input index boundary]) recorded
          · refine ⟨slot, ?_, path, ?_⟩
            · simp only [NativeResponsibilityProcess.Edge.target]
              rw [List.getElem?_set]
              simpa only [if_neg same] using atSlot
            · simp only [NativeResponsibilityProcess.Run.events, List.filter_append,
                List.filter_cons, List.filter_nil]
              rw [cross_record input changed obligation old boundary,
                record_slot input changed.val boundary]
              simpa only [beq_iff_eq, same, if_false, List.append_nil] using recorded
      | reopen _ _ _ impossible => exact impossible.elim

def retired : Event input → ℚ
  | .birth _ => 0
  | .review _ receipt balance remaining => match receipt.kind with
      | .payment _ => receipt.allocated input balance remaining
      | .assignment .. => 0

omit [DecidableEq Port] in
theorem event_conservation (event : Event input) :
    total input (event.after input) + retired input event = total input (event.before input) := by
  cases event with
  | birth => simp only [Event.after, Event.before, retired, add_zero]
  | review claim receipt balance remaining =>
      cases kind : receipt.kind <;>
        simp only [Event.after, Event.before, retired, Review.after, kind,
          pay_total, assign_total] <;> ring

omit [DecidableEq Port] in
theorem retired_nonnegative (event : Event input) (lawful : event.Lawful input) :
    0 ≤ retired input event := by
  cases event with
  | birth => exact le_refl _
  | review claim receipt balance remaining =>
      cases kind : receipt.kind with
      | payment holder =>
          simpa only [retired, kind] using receipt.allocated_nonnegative input balance remaining lawful.1 lawful.2.1
      | assignment => simp only [retired, kind, le_refl]

namespace Path

def paid {first last} (path : Path input first last) : ℚ := (path.events input).map (retired input) |>.sum

theorem conservation {first last} (path : Path input first last) :
    total input (slotBalance input last) + path.paid input = total input (slotBalance input first) := by
  induction path with
  | nil => simp only [paid, events, List.map_nil, List.sum_nil, add_zero]
  | snoc prior boundary ih =>
      have step := event_conservation input boundary.event
      rw [← boundary.before_eq] at step
      change total input (slotBalance input _) + _ = _
      rw [boundary_balance]
      simp only [paid, events, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
      change total input (boundary.event.after input) + (prior.paid input + _) = _
      rw [← ih]
      simp only [slotBalance]
      linarith

theorem paid_nonnegative {first last} (path : Path input first last) : 0 ≤ path.paid input := by
  induction path with
  | nil => exact le_refl _
  | snoc prior boundary ih =>
      change 0 ≤ ((prior.events input ++ [boundary.event]).map (retired input)).sum
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
      exact add_nonneg ih (retired_nonnegative input boundary.event boundary.lawful)

theorem receipts_are_lawful {first last} (path : Path input first last) :
    ∀ event ∈ path.events input, event.Lawful input := by
  induction path with
  | nil => simp only [events, List.not_mem_nil, false_implies, implies_true]
  | snoc prior boundary ih =>
      intro event member
      rcases List.mem_append.mp member with old | fresh
      · exact ih event old
      · have same : event = boundary.event := List.mem_singleton.mp fresh
        exact same ▸ boundary.lawful

theorem principal_does_not_increase {first last} (path : Path input first last) :
    total input (slotBalance input last) ≤ total input (slotBalance input first) := by
  have exactBalance := path.conservation input
  have nonnegative := path.paid_nonnegative input
  linarith

end Path

/-- The producer is the actual ordered native run. No correspondence,
admission-equality, or target residual is supplied as an input. -/
def actual (start later index : Nat) (slot : ObligationSlot (vocabulary input))
    (present : (accountAt input start).current.slots[index]? = some slot) :=
  follow input (BalanceConservation.fromActualCut input start later) index slot present

/-- Track this exact issue's stable slot through its own suffix and every
later actual visit. New admissions cannot replace the tracked slot. -/
def fromIssue (visit : Nat) (index : Fin (IssueTrace.inventory input visit).length)
    (claim : IssuedClaim input) (exactOrigin : claim.origin = IssueTrace.origin input visit index)
    (emitted : readIssue input (IssueTrace.origin input visit index) = .issued claim exactOrigin)
    (later : Nat) :=
  follow input ((IssueTrace.generate input visit index claim exactOrigin emitted).continuation later)
    (IssueTrace.before input visit index).current.slots.length
    (.live (admission input claim).toObligation)
    (IssueTrace.generate input visit index claim exactOrigin emitted).native_admission

theorem issued_principal_conservation (visit : Nat) (index : Fin (IssueTrace.inventory input visit).length)
    (claim : IssuedClaim input) (exactOrigin : claim.origin = IssueTrace.origin input visit index)
    (emitted : readIssue input (IssueTrace.origin input visit index) = .issued claim exactOrigin)
    (later : Nat) :
    let result := fromIssue input visit index claim exactOrigin emitted later
    total input (slotBalance input result.slot) + result.path.paid input = claim.quantity := by
  exact (fromIssue input visit index claim exactOrigin emitted later).path.conservation input |>.trans
    (initial_total input claim)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Migration
