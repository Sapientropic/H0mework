import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Accounting
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation.Execution
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.MarketReadout

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Posting

open ResponsibilityLifecycle Source.Program Family.BalanceConservation

inductive Side | debit | credit

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

/-- A payment is posted once in the original issue's denomination, to its
actual debtor or the actual creditor named by this payment review. -/
def amount (event : Family.Event sources) (side : Side) (party : Party) (good : Good) : ℚ :=
  match event with
  | .birth _ => 0
  | .review claim receipt balance cap =>
      match receipt.kind with
      | .assignment => 0
      | .payment =>
          let actor := match side with | .debit => claim.2.debtor | .credit => receipt.sender
          if actor = party ∧ (sources claim.1).law.settlementUnit claim.2.instrument = good then
            min cap (balance receipt.sender) * (sources claim.1).law.settlementRate claim.2.instrument
          else 0

def runAmount {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) (side : Side) (party : Party) (good : Good) : ℚ :=
  (run.events.map (fun event => amount sources (sourceEvent sources event) side party good)).sum

theorem run_append {first middle last : ResponsibilityState (vocabulary sources)}
    (left : (process sources).Run first middle) (right : (process sources).Run middle last)
    (side : Side) (party : Party) (good : Good) :
    runAmount sources (left.concatRuns _ right) side party good =
      runAmount sources left side party good + runAmount sources right side party good := by
  simp only [runAmount, NativeResponsibilityProcess.Run.events_concatRuns, List.map_append, List.sum_append]

theorem single_cross {state : ResponsibilityState (vocabulary sources)}
    (index : Fin state.slots.length) (obligation : AdmittedObligation (vocabulary sources))
    (present : state.slots.get index = .live obligation) (boundary : Boundary sources obligation)
    (side : Side) (party : Party) (good : Good) :
    runAmount sources (.step .nil (.cross index obligation present boundary)) side party good =
      amount sources (boundary.event sources) side party good := by
  simpa only [runAmount, NativeResponsibilityProcess.Run.events, List.nil_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using
    congrArg (fun event => amount sources event side party good)
      (Migration.cross_source sources index obligation present boundary)

def movementAmount {origin : Origin sources} (movement : Movement (sources origin.1) origin.2)
    (quantity : ℚ) (side : Side) (party : Party) (good : Good) : ℚ :=
  match movement.kind with
  | .assignment => 0
  | .payment =>
      let actor := match side with | .debit => movement.debtor | .credit => movement.sender
      if actor = party ∧ (sources origin.1).law.settlementUnit movement.instrument = good then
        quantity * (sources origin.1).law.settlementRate movement.instrument else 0

omit [DecidableEq Port] in
theorem movementAmount_add {origin : Origin sources} (movement : Movement (sources origin.1) origin.2)
    (left right : ℚ) (side : Side) (party : Party) (good : Good) :
    movementAmount sources movement (left + right) side party good =
      movementAmount sources movement left side party good + movementAmount sources movement right side party good := by
  cases payment : movement.kind with
  | assignment => simp only [movementAmount, payment, add_zero]
  | payment =>
      cases side <;> simp only [movementAmount, payment] <;> split_ifs <;> ring

omit [DecidableEq Port] in
theorem movementAmount_zero {origin : Origin sources} (movement : Movement (sources origin.1) origin.2)
    (side : Side) (party : Party) (good : Good) :
    movementAmount sources movement 0 side party good = 0 := by
  cases payment : movement.kind <;> cases side <;> simp [movementAmount, payment]

omit [DecidableEq Port] in
theorem selected_origin {origin : Origin sources} {claim : Claim sources}
    (review : Review sources claim) (selected : readReview sources claim origin = some review) :
    review.origin = origin := by
  unfold readReview at selected
  repeat' first | split at selected | contradiction
  cases Option.some.inj selected
  rfl

theorem allocateLive_amount {origin : Origin sources}
    (movement : Movement (sources origin.1) origin.2)
    (emitted : readMovement (sources origin.1) origin.2 = some movement)
    (state : (process sources).GeneratedState) (index : Fin state.current.slots.length)
    (obligation : AdmittedObligation (vocabulary sources)) (present : state.current.slots.get index = .live obligation)
    (review : Review sources obligation.content) (selected : readReview sources obligation.content origin = some review)
    (available : ℚ) (nonnegative : 0 ≤ available) (side : Side) (party : Party) (good : Good) :
    runAmount sources (allocateLive sources state index obligation present review available nonnegative).transition side party good =
      movementAmount sources movement
        ((allocateLive sources state index obligation present review available nonnegative).used sources) side party good := by
  obtain ⟨instrument, debtor, kind, sender, _, _⟩ := selected_review_keys sources movement emitted review selected
  have originEq := selected_origin sources review selected
  have unit := review.settlement_unit
  have rate := review.settlement_rate
  rw [originEq, instrument] at unit rate
  let cap := min available review.quantity
  have sound := live_sound sources state index obligation present
  let boundary := reviewBoundary sources obligation review cap sound.2
    (le_min nonnegative (review.quantity_nonnegative sources)) (min_le_right _ _) sound.1
  calc
    _ = amount sources (boundary.event sources) side party good :=
      single_cross sources index obligation present boundary side party good
    _ = _ := by
      change amount sources (.review obligation.content review obligation.residual cap) side party good =
        movementAmount sources movement
          (available - (available - min cap (obligation.residual review.sender))) side party good
      rw [sub_sub_cancel]
      cases side <;> cases payment : movement.kind <;>
        simp only [amount, movementAmount, kind, payment, debtor, sender, instrument, unit, rate]

theorem allocateAt_amount {origin : Origin sources}
    (movement : Movement (sources origin.1) origin.2)
    (emitted : readMovement (sources origin.1) origin.2 = some movement)
    (state : (process sources).GeneratedState) (position : Nat)
    (available : ℚ) (nonnegative : 0 ≤ available) (side : Side) (party : Party) (good : Good) :
    runAmount sources (allocateAt sources origin state position available nonnegative).transition side party good =
      movementAmount sources movement
        ((allocateAt sources origin state position available nonnegative).used sources) side party good := by
  let correct : Allocation sources state available → Prop := fun result =>
    runAmount sources result.transition side party good =
      movementAmount sources movement (result.used sources) side party good
  change correct (allocateAt sources origin state position available nonnegative)
  by_cases inRange : position < state.current.slots.length
  · cases present : state.current.slots.get ⟨position, inRange⟩ with
    | terminal archive =>
        have same : allocateAt sources origin state position available nonnegative =
            Allocation.idle sources state available nonnegative := by
          unfold allocateAt
          rw [dif_pos inRange]
          split
          next currentArchive currentPresent => rfl
          next currentObligation currentPresent =>
            have impossible := present.symm.trans currentPresent
            cases impossible
        exact (congrArg correct same).mpr (by
          change 0 = movementAmount sources movement (available - available) side party good
          rw [sub_self, movementAmount_zero])
    | live obligation =>
        cases selected : readReview sources obligation.content origin with
        | none =>
            have same : allocateAt sources origin state position available nonnegative =
                Allocation.idle sources state available nonnegative := by
              unfold allocateAt
              rw [dif_pos inRange]
              split
              next currentArchive currentPresent =>
                have impossible := present.symm.trans currentPresent
                cases impossible
              next currentObligation currentPresent =>
                have sameObligation := ObligationSlot.live.inj (present.symm.trans currentPresent)
                subst currentObligation
                simp only [selected]
            exact (congrArg correct same).mpr (by
              change 0 = movementAmount sources movement (available - available) side party good
              rw [sub_self, movementAmount_zero])
        | some review =>
            have same : allocateAt sources origin state position available nonnegative =
                allocateLive sources state ⟨position, inRange⟩ obligation present review available nonnegative := by
              unfold allocateAt
              rw [dif_pos inRange]
              split
              next currentArchive currentPresent =>
                have impossible := present.symm.trans currentPresent
                cases impossible
              next currentObligation currentPresent =>
                have sameObligation := ObligationSlot.live.inj (present.symm.trans currentPresent)
                subst currentObligation
                simp only [selected]
            exact (congrArg correct same).mpr
              (allocateLive_amount sources movement emitted state _ _ present review selected available nonnegative side party good)
  · have same : allocateAt sources origin state position available nonnegative =
        Allocation.idle sources state available nonnegative := by
      simp only [allocateAt, dif_neg inRange]
    exact (congrArg correct same).mpr (by
      change 0 = movementAmount sources movement (available - available) side party good
      rw [sub_self, movementAmount_zero])

theorem allocateFrom_amount {origin : Origin sources}
    (movement : Movement (sources origin.1) origin.2)
    (emitted : readMovement (sources origin.1) origin.2 = some movement)
    (fuel position : Nat) (state : (process sources).GeneratedState)
    (available : ℚ) (nonnegative : 0 ≤ available) (side : Side) (party : Party) (good : Good) :
    runAmount sources (allocateFrom sources origin position fuel state available nonnegative).transition side party good =
      movementAmount sources movement
        ((allocateFrom sources origin position fuel state available nonnegative).used sources) side party good := by
  induction fuel generalizing position state available with
  | zero => cases payment : movement.kind <;> simp [allocateFrom, Allocation.idle, Allocation.used, runAmount, NativeResponsibilityProcess.Run.events, movementAmount, payment]
  | succ fuel ih =>
      let first := allocateAt sources origin state position available nonnegative
      let rest := allocateFrom sources origin (position + 1) fuel first.after first.remaining first.remaining_nonnegative
      change runAmount sources (first.transition.concatRuns _ rest.transition) side party good =
        movementAmount sources movement ((first.append sources rest).used sources) side party good
      rw [run_append, Allocation.used_append, movementAmount_add,
        allocateAt_amount sources movement emitted state position available nonnegative side party good,
        ih (position + 1) first.after first.remaining first.remaining_nonnegative]

/-- Raw material is read from this same source item. Assignments retire no
principal and never enter either payment posting side. -/
def rawAmount (index : Index) (instruction : ExecutionItem Party Good Port Technology Instrument)
    (side : Side) (party : Party) (good : Good) : ℚ :=
  match instruction.request.operation with
  | .settle .. => flowAt (match side with
      | .debit => (sources index).law.actualDebit instruction.before instruction.request
      | .credit => (sources index).law.actualCredit instruction.before instruction.request) party good
  | _ => 0

omit [DecidableEq Port] in
theorem movement_raw {origin : Origin sources} (movement : Movement (sources origin.1) origin.2)
    (side : Side) (party : Party) (good : Good) :
    movementAmount sources movement movement.quantity side party good =
      rawAmount sources origin.1 movement.instruction side party good := by
  cases payment : movement.kind <;> cases side <;>
    simp [movementAmount, rawAmount, movement.operation_exact, payment,
      RawLaw.actualDebit, RawLaw.actualCredit, movement.accepted, RawLaw.debit, RawLaw.credit,
      flowAt, Source.Program.amount, locate, eq_comm]

theorem matched_allocation {origin : Origin sources}
    (movement : Movement (sources origin.1) origin.2)
    (emitted : readMovement (sources origin.1) origin.2 = some movement)
    (state : (process sources).GeneratedState)
    (compatible : Compatible sources origin.1 state.current)
    (matched : ledgerClaims sources state.current = movement.instruction.before.claims)
    (side : Side) (party : Party) (good : Good) :
    runAmount sources (allocate sources origin state movement.quantity (movement.quantity_nonnegative _)).transition side party good =
      rawAmount sources origin.1 movement.instruction side party good := by
  have allocated := allocateFrom_amount sources movement emitted state.current.slots.length 0 state
    movement.quantity (movement.quantity_nonnegative _) side party good
  change runAmount sources (allocate sources origin state movement.quantity (movement.quantity_nonnegative _)).transition side party good =
    movementAmount sources movement ((allocate sources origin state movement.quantity (movement.quantity_nonnegative _)).used sources) side party good at allocated
  rw [allocated]
  change movementAmount sources movement
    (movement.quantity - (allocate sources origin state movement.quantity (movement.quantity_nonnegative _)).remaining) side party good = _
  rw [matched_movement_quota_exhausted sources movement emitted state compatible matched, sub_zero]
  exact movement_raw sources movement side party good

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Posting
