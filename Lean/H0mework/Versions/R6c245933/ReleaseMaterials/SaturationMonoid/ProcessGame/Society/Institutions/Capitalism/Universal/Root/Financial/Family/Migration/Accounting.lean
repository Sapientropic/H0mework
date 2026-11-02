import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration

/-! Actual native allocations retire principal once per original slot.
An assignment changes holders while preserving that slot's total principal. -/
set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration

open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

def retired (event : Family.Event sources) : ℚ :=
  match event with
  | .birth _ => 0
  | .review _ receipt balance cap =>
      match receipt.kind with
      | .payment => min cap (balance receipt.sender)
      | .assignment => 0

omit [DecidableEq Port] in
theorem event_conservation (event : Family.Event sources) :
    Financial.total (sources event.claim.1) (event.after sources) + retired sources event =
      Financial.total (sources event.claim.1) (event.before) := by
  cases event with
  | birth claim => simp [Family.Event.after, Family.Event.before, retired]
  | review claim receipt balance cap =>
      cases kind : receipt.kind <;>
        simp [Family.Event.after, Family.Event.before, Family.Event.claim, retired,
          Family.Review.after, kind, Financial.pay_total, Financial.assign_total]

omit [DecidableEq Port] in
theorem retired_nonnegative (event : Family.Event sources) (lawful : event.Lawful sources) :
    0 ≤ retired sources event := by
  cases event with
  | birth => exact le_rfl
  | review claim receipt balance cap =>
      cases kind : receipt.kind with
      | payment =>
          simpa only [retired, kind] using le_min lawful.2.1 (lawful.1 receipt.sender)
      | assignment => simp [retired, kind]

def principal (slot : ObligationSlot (vocabulary sources)) : ℚ :=
  (slotBalance sources slot).sum (fun _ quantity => quantity)

namespace Path

def paid {first last} (path : Path sources first last) : ℚ :=
  ((path.events sources).map (retired sources)).sum

theorem preserves_claim {first last} (path : Path sources first last) :
    slotClaim sources last = slotClaim sources first := by
  have same := congrArg (fun obligation : AdmittedObligation (vocabulary sources) => obligation.content)
    (path.preserves_identity sources)
  simpa only [identity,slotClaim] using same

theorem conservation {first last} (path : Path sources first last) :
    principal sources last + path.paid sources = principal sources first := by
  induction path with
  | nil => simp only [paid,events,List.map_nil,List.sum_nil,add_zero]
  | @snoc obligation prior boundary ih =>
      have step := event_conservation sources (boundary.event sources)
      have afterEq : principal sources (Boundary.disposition sources boundary).targetSlot =
          ((boundary.event sources).after sources).sum (fun _ quantity => quantity) :=
        congrArg (fun balance => balance.sum (fun _ quantity => quantity)) (boundary_balance sources boundary)
      rw [afterEq]
      simp only [paid,events,List.map_append,List.sum_append,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero]
      change ((boundary.event sources).after sources).sum (fun _ quantity => quantity) +
        (prior.paid sources + retired sources (boundary.event sources)) = principal sources first
      change ((boundary.event sources).after sources).sum (fun _ quantity => quantity) +
        retired sources (boundary.event sources) = obligation.residual.sum (fun _ quantity => quantity) at step
      change obligation.residual.sum (fun _ quantity => quantity) + prior.paid sources = principal sources first at ih
      linarith

theorem paid_nonnegative {first last} (path : Path sources first last) : 0 ≤ path.paid sources := by
  induction path with
  | nil => exact le_rfl
  | snoc prior boundary ih =>
      change 0 ≤ ((prior.events sources ++ [boundary.event sources]).map (retired sources)).sum
      simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
      exact add_nonneg ih (retired_nonnegative sources (boundary.event sources)
        ⟨boundary.nonnegative,boundary.available,boundary.within⟩)

theorem receipts_are_lawful {first last} (path : Path sources first last) :
    ∀ event ∈ path.events sources, event.Lawful sources := by
  induction path with
  | nil => simp only [events,List.not_mem_nil,false_implies,implies_true]
  | snoc prior boundary ih =>
      intro event member
      rcases List.mem_append.mp member with old | fresh
      · exact ih event old
      · have same : event = boundary.event sources := List.mem_singleton.mp fresh
        subst event
        exact ⟨boundary.nonnegative,boundary.available,boundary.within⟩

theorem principal_does_not_increase {first last} (path : Path sources first last) :
    principal sources last ≤ principal sources first := by
  have exactBalance := path.conservation sources
  have positive := path.paid_nonnegative sources
  linarith

theorem positive_paid_iff_strict_progress {first last} (path : Path sources first last) :
    0 < path.paid sources ↔ principal sources last < principal sources first := by
  have exactBalance := path.conservation sources
  constructor <;> intro positive <;> linarith

theorem zero_paid_iff_principal_unchanged {first last} (path : Path sources first last) :
    path.paid sources = 0 ↔ principal sources last = principal sources first := by
  have exactBalance := path.conservation sources
  constructor <;> intro zero <;> linarith

theorem events_preserve_original_claim {first last} (path : Path sources first last) :
    ∀ event ∈ path.events sources, event.claim sources = slotClaim sources first := by
  induction path with
  | nil => simp only [events,List.not_mem_nil,false_implies,implies_true]
  | snoc prior boundary ih =>
      intro event member
      rcases List.mem_append.mp member with old | fresh
      · exact ih event old
      · have same : event = boundary.event sources := List.mem_singleton.mp fresh
        subst event
        exact prior.preserves_claim sources

theorem positive_paid_has_an_actual_payment {first last} (path : Path sources first last)
    (positive : 0 < path.paid sources) :
    ∃ event ∈ path.events sources, 0 < retired sources event := by
  induction path with
  | nil => exact False.elim (lt_irrefl 0 positive)
  | snoc prior boundary ih =>
      by_cases lastPaid : 0 < retired sources (boundary.event sources)
      · exact ⟨boundary.event sources,List.mem_append_right _ (List.mem_singleton_self _),lastPaid⟩
      · have amount : (Path.snoc prior boundary).paid sources = prior.paid sources + retired sources (boundary.event sources) := by
          simp only [paid,events,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
        have oldPaid : 0 < prior.paid sources := by rw [amount] at positive; linarith
        obtain ⟨event,member,paid⟩ := ih oldPaid
        exact ⟨event,List.mem_append_left _ member,paid⟩

end Path

theorem Follow.payment_is_exactly_the_actual_slot_records
    {first last : ResponsibilityState (vocabulary sources)}
    {run : (process sources).Run first last} {index original}
    (result : Follow sources run index original) :
    result.path.paid sources =
      ((run.events.filter (fun event => event.slot == index)).map
        (fun event => retired sources (sourceEvent sources event))).sum := by
  rw [Path.paid,← result.path.records_sources sources index,List.map_map,result.recorded]
  rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration
