import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.IssueTrace

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family

open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

def continueVisits (index : Index) (start : Nat) : Nat → (process sources).GeneratedState → (process sources).GeneratedState
  | 0, state => state
  | count + 1, state =>
      consumeVisit sources index (start + count) (continueVisits index start count state)

def continueVisits_run (index : Index) (start count : Nat) (state : (process sources).GeneratedState) :
    (process sources).Run state.current (continueVisits sources index start count state).current := by
  induction count with
  | zero => exact .nil
  | succ count ih => exact ih.concatRuns (process sources) (visitRun sources _ _ _)

theorem continueVisits_preserves_original_claims (index : Index) (start count : Nat)
    (state : (process sources).GeneratedState) :
    state.current.slots.map (slotClaim sources) <+:
      (continueVisits sources index start count state).current.slots.map (slotClaim sources) := by
  induction count with
  | zero => exact List.prefix_rfl
  | succ count ih => exact ih.trans (consumeOrigins_preserves_original_claims sources _ _)

omit [DecidableEq Port] in
private theorem local_claims (index : Index) (origins : List (InstructionOrigin (sources index))) :
    (origins.map (Sigma.mk index)).filterMap (originsClaim? sources) =
      (issuedClaims (sources index) origins).map (Sigma.mk index) := by
  induction origins with
  | nil => rfl
  | cons origin tail ih =>
      simp only [List.map_cons, issuedClaims, List.filterMap_cons, originsClaim?, issuedClaim?]
      simp only [issuedClaims] at ih
      cases readIssue (sources index) origin <;> simp only [List.map_cons]
      all_goals first | exact ih | exact congrArg (List.cons _) ih

theorem through_keeps_every_complete_original_claim (index : Index) (ordinal : Nat) :
    (through sources index ordinal).current.slots.map (slotClaim sources) =
      ((Financial.accountAt (sources index) ordinal).current.slots.map (Financial.slotClaim (sources index))).map (Sigma.mk index) := by
  rw [account_claims_are_exactly_the_source_issues]
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
      change (consumeOrigins sources (visitOrigins sources index ordinal) (through sources index ordinal)).current.slots.map _ = _
      have step : issuedBefore (sources index) (ordinal + 1) = issuedBefore (sources index) ordinal ++
          issuedClaims (sources index) (inventoryAt (sources index) (ProgrammeHistory.visitAt (sources index) ordinal)) := by
        rw [issuedBefore]
      rw [origins_exact_claims, ih, step, List.map_append]
      exact congrArg (List.append ((issuedBefore (sources index) ordinal).map (Sigma.mk index)))
        (local_claims sources index _)

def slotClaims (slot : ObligationSlot (vocabulary sources))
    (instrument : Instrument) (debtor holder : Party) : ℚ :=
  if (slotClaim sources slot).2.instrument = instrument ∧ (slotClaim sources slot).2.debtor = debtor then
    slotBalance sources slot holder else 0

def ledgerClaims (state : ResponsibilityState (vocabulary sources))
    (instrument : Instrument) (debtor holder : Party) : ℚ :=
  (state.slots.map (fun slot => slotClaims sources slot instrument debtor holder)).sum

theorem terminal_slots_cannot_supply_positive_shares (archive : TerminalArchive (vocabulary sources))
    (instrument : Instrument) (debtor holder : Party) :
    slotClaims sources (.terminal archive) instrument debtor holder = 0 := by
  simp [slotClaims, slotBalance]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family
