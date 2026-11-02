import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Posting

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Posting.Balance

open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

/-- Debit positions are liabilities; credit positions are the current holder's
asset. Each original claim retains its own denomination. -/
def holding (claim : Claim sources) (shares : Shares (Party := Party))
    (side : Side) (party : Party) (good : Good) : ℚ :=
  match side with
  | .debit => if claim.2.debtor = party ∧ (sources claim.1).law.settlementUnit claim.2.instrument = good then
      Financial.total (sources claim.1) shares * (sources claim.1).law.settlementRate claim.2.instrument else 0
  | .credit => if (sources claim.1).law.settlementUnit claim.2.instrument = good then
      shares party * (sources claim.1).law.settlementRate claim.2.instrument else 0

def slot (entry : ObligationSlot (vocabulary sources)) (side : Side) (party : Party) (good : Good) :=
  holding sources (slotClaim sources entry) (slotBalance sources entry) side party good

def position (state : ResponsibilityState (vocabulary sources)) (side : Side) (party : Party) (good : Good) : ℚ :=
  (state.slots.map (fun entry => slot sources entry side party good)).sum

def issued (event : Family.Event sources) (side : Side) (party : Party) (good : Good) : ℚ :=
  match event with
  | .birth claim => holding sources claim (initialBalance (sources claim.1) claim.2) side party good
  | .review .. => 0

/-- Assignment transfers a financial asset, even though it is not a payment.
The debtor's total liability is unchanged. -/
def assigned (event : Family.Event sources) (side : Side) (party : Party) (good : Good) : ℚ :=
  match event, side with
  | .review claim review shares cap, .credit =>
      match review.kind with
      | .payment => 0
      | .assignment => if (sources claim.1).law.settlementUnit claim.2.instrument = good then
          ((if review.recipient = party then min cap (shares review.sender) else 0) -
            (if review.sender = party then min cap (shares review.sender) else 0)) *
              (sources claim.1).law.settlementRate claim.2.instrument else 0
  | _, _ => 0

def newIssues {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) (side : Side) (party : Party) (good : Good) : ℚ :=
  (run.events.map (fun event => issued sources (sourceEvent sources event) side party good)).sum

def assignments {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) (side : Side) (party : Party) (good : Good) : ℚ :=
  (run.events.map (fun event => assigned sources (sourceEvent sources event) side party good)).sum

omit [DecidableEq Port] in
theorem issued_debit (claim : Claim sources) (party : Party) (good : Good) :
    issued sources (.birth claim) .debit party good =
      if claim.2.debtor = party ∧ (sources claim.1).law.settlementUnit claim.2.instrument = good then
        claim.2.quantity * (sources claim.1).law.settlementRate claim.2.instrument else 0 := by
  simp only [issued, holding, Financial.initial_total]

omit [DecidableEq Port] in
theorem assignment_debit (event : Family.Event sources) (party : Party) (good : Good) :
    assigned sources event .debit party good = 0 := by
  cases event <;> rfl

omit [DecidableEq Port] in
theorem review_balance (claim : Claim sources) (review : Review sources claim)
    (shares : Shares (Party := Party)) (cap : ℚ) (side : Side) (party : Party) (good : Good) :
    holding sources claim (review.after sources shares cap) side party good +
        amount sources (.review claim review shares cap) side party good =
      holding sources claim shares side party good + assigned sources (.review claim review shares cap) side party good := by
  cases side with
  | debit =>
      have total := event_conservation sources (.review claim review shares cap)
      cases kind : review.kind with
      | payment =>
          simp only [Family.Event.after, Family.Event.before, Family.Event.claim, retired, kind] at total
          by_cases relevant : claim.2.debtor = party ∧ (sources claim.1).law.settlementUnit claim.2.instrument = good
          · simp only [holding, amount, kind, if_pos relevant, assigned, add_zero]
            exact (add_mul _ _ _).symm.trans (congrArg (fun q => q * (sources claim.1).law.settlementRate claim.2.instrument) total)
          · simp only [holding, amount, kind, if_neg relevant, assigned, add_zero]
      | assignment =>
          simp only [Family.Event.after, Family.Event.before, Family.Event.claim, retired, kind, add_zero] at total
          simp only [holding, amount, kind, assigned, add_zero]
          rw [total]
  | credit =>
      by_cases unit : (sources claim.1).law.settlementUnit claim.2.instrument = good
      · cases kind : review.kind with
        | payment =>
            have paid := Financial.BalanceConservation.shareAt_pay (sources claim.1) shares review.sender
              (min cap (shares review.sender)) party
            change (pay (sources claim.1) shares review.sender (min cap (shares review.sender))) party =
              shares party - if review.sender = party then min cap (shares review.sender) else 0 at paid
            simp only [holding, unit, ↓reduceIte, Review.after, kind, paid, amount, assigned, add_zero]
            by_cases actor : review.sender = party <;> simp [actor, sub_mul]
        | assignment =>
            have moved := Financial.BalanceConservation.shareAt_assign (sources claim.1) shares review.sender review.recipient
              (min cap (shares review.sender)) party
            change (assign (sources claim.1) shares review.sender review.recipient (min cap (shares review.sender))) party =
              shares party - (if review.sender = party then min cap (shares review.sender) else 0) +
                if review.recipient = party then min cap (shares review.sender) else 0 at moved
            simp only [holding, unit, ↓reduceIte, Review.after, kind, moved, amount, assigned, add_zero]
            ring
      · cases kind : review.kind <;> simp [holding, amount, assigned, kind, unit]

theorem boundary_balance_equation {obligation : AdmittedObligation (vocabulary sources)}
    (boundary : Boundary sources obligation) (side : Side) (party : Party) (good : Good) :
    slot sources (Boundary.disposition sources boundary).targetSlot side party good +
        amount sources (boundary.event sources) side party good =
      slot sources (.live obligation) side party good + assigned sources (boundary.event sources) side party good := by
  unfold slot
  rw [boundary_claim, boundary_balance]
  exact review_balance sources obligation.content boundary.receipt obligation.residual boundary.cap side party good

theorem edge_balance {first : ResponsibilityState (vocabulary sources)} (edge : (process sources).Edge first)
    (side : Side) (party : Party) (good : Good) :
    position sources edge.target side party good + amount sources (sourceEvent sources edge.lifecycleEvent) side party good =
      position sources first side party good + issued sources (sourceEvent sources edge.lifecycleEvent) side party good +
        assigned sources (sourceEvent sources edge.lifecycleEvent) side party good := by
  cases edge with
  | admit claim =>
      change ((first.slots ++ [ObligationSlot.live (admission sources claim).toObligation]).map
        (fun entry => slot sources entry side party good)).sum + 0 =
        position sources first side party good + holding sources claim (initialBalance (sources claim.1) claim.2) side party good + 0
      simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
      rfl
  | cross index obligation present boundary =>
      rw [Migration.cross_source sources index obligation present boundary]
      have localBalance := boundary_balance_equation sources boundary side party good
      change ((first.slots.set index (Boundary.disposition sources boundary).targetSlot).map
        (fun entry => slot sources entry side party good)).sum + _ = position sources first side party good + 0 + _
      rw [List.map_set, List.sum_set']
      simp only [List.length_map, index.isLt, ↓reduceDIte, List.getElem_map]
      have row : first.slots[index.val] = .live obligation := present
      rw [row]
      unfold position
      linarith
  | reopen _ _ _ impossible => exact impossible.elim

/-- Accrual includes every old position and every actual new issue. Payment
is counted once, and assignment changes holders without retiring principal. -/
theorem run_balance {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) (side : Side) (party : Party) (good : Good) :
    position sources last side party good + runAmount sources run side party good =
      position sources first side party good + newIssues sources run side party good + assignments sources run side party good := by
  induction run with
  | nil => simp only [runAmount, newIssues, assignments, NativeResponsibilityProcess.Run.events,
      List.map_nil, List.sum_nil, add_zero]
  | step prior edge ih =>
      have step := edge_balance sources edge side party good
      simp only [runAmount, newIssues, assignments, NativeResponsibilityProcess.Run.events,
        List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at ih ⊢
      linarith

theorem debtor_balance {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) (party : Party) (good : Good) :
    position sources last .debit party good - position sources first .debit party good =
      newIssues sources run .debit party good - runAmount sources run .debit party good := by
  have exactBalance := run_balance sources run .debit party good
  have zero : assignments sources run .debit party good = 0 := by
    unfold assignments
    simp only [assignment_debit, List.map_const', List.sum_replicate, nsmul_zero]
  rw [zero] at exactBalance
  linarith

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Posting.Balance
