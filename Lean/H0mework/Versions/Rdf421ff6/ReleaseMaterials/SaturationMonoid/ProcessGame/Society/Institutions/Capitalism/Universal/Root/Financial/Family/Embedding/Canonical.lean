import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Embedding.Execution
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Generated

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Embedding

open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument) (index : Index)

def Realization.allocateAt (origin : InstructionOrigin (sources index))
    {original : (Financial.process (sources index)).GeneratedState}
    (realized : Realization sources index original) (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available) :
    Realization sources index (Financial.allocateAt (sources index) origin original position available nonnegative).after := by
  unfold Financial.allocateAt
  split
  · split
    · exact realized
    · split
      · exact realized
      · exact realized.allocateLive sources index _ _ _ _ available nonnegative
  · exact realized

def Realization.allocateFrom (origin : InstructionOrigin (sources index)) (position : Nat) :
    (fuel : Nat) → {original : (Financial.process (sources index)).GeneratedState} →
    (realized : Realization sources index original) → (available : ℚ) → (nonnegative : 0 ≤ available) →
      Realization sources index (Financial.allocateFrom (sources index) origin position fuel original available nonnegative).after
  | 0, _, realized, _, _ => realized
  | fuel + 1, original, realized, available, nonnegative =>
      let first := Financial.allocateAt (sources index) origin original position available nonnegative
      let next := realized.allocateAt sources index origin position available nonnegative
      Realization.allocateFrom origin (position + 1) fuel next first.remaining first.remaining_nonnegative

def Realization.consume (origin : InstructionOrigin (sources index))
    {original : (Financial.process (sources index)).GeneratedState} (realized : Realization sources index original) :
    Realization sources index ((Financial.consume (sources index) origin original).next (sources index)) := by
  unfold Financial.consume
  split
  · exact realized.admit sources index _
  · exact realized
  · exact realized
  · split
    · exact Realization.allocateFrom sources index origin 0 original.current.slots.length realized _ _
    · exact realized

def Realization.consumeOrigins : (origins : List (InstructionOrigin (sources index))) →
    {original : (Financial.process (sources index)).GeneratedState} →
    (realized : Realization sources index original) →
      Realization sources index (Financial.consumeOrigins (sources index) origins original)
  | [], _, realized => realized
  | origin :: tail, _, realized => Realization.consumeOrigins tail (realized.consume sources index origin)

/-- The original source's own instruction fold produces its common native account. -/
def accountAt : (ordinal : Nat) → Realization sources index (Financial.accountAt (sources index) ordinal)
  | 0 => .initial sources index
  | ordinal + 1 =>
      (accountAt ordinal).consumeOrigins sources index
        (Financial.inventoryAt (sources index) (ProgrammeHistory.visitAt (sources index) ordinal))

theorem accountAt_full_state (ordinal : Nat) :
    (accountAt sources index ordinal).account.current =
      state sources index (Financial.accountAt (sources index) ordinal).current :=
  (accountAt sources index ordinal).exact_state

theorem accountAt_full_history (ordinal : Nat) :
    (accountAt sources index ordinal).account.current.history =
      (Financial.accountAt (sources index) ordinal).current.history.map (record sources index) :=
  congrArg ResponsibilityState.history (accountAt_full_state sources index ordinal)

theorem slot_balance (original : ObligationSlot (Financial.vocabulary (sources index))) :
    slotBalance sources (slot sources index original) = Financial.slotBalance (sources index) original := by
  cases original <;> rfl

theorem slot_claim (original : ObligationSlot (Financial.vocabulary (sources index))) :
    slotClaim sources (slot sources index original) = ⟨index, Financial.slotClaim (sources index) original⟩ := by
  cases original <;> rfl

theorem accountAt_complete_claims (ordinal : Nat) :
    (accountAt sources index ordinal).account.current.slots.map (slotClaim sources) =
      ((Financial.accountAt (sources index) ordinal).current.slots.map (Financial.slotClaim (sources index))).map
        (Sigma.mk index) := by
  rw [accountAt_full_state]
  simp only [state, List.map_map, Function.comp_def, slot_claim]

theorem slot_matrix (original : ObligationSlot (Financial.vocabulary (sources index)))
    (instrument : Instrument) (debtor holder : Party) :
    slotClaims sources (slot sources index original) instrument debtor holder =
      BalanceConservation.slotClaims (sources index) original instrument debtor holder := by
  unfold slotClaims BalanceConservation.slotClaims
  rw [slot_claim, slot_balance]
  rfl

theorem state_matrix (original : ResponsibilityState (Financial.vocabulary (sources index))) :
    ledgerClaims sources (state sources index original) = BalanceConservation.ledgerClaims (sources index) original := by
  funext instrument debtor holder
  unfold ledgerClaims BalanceConservation.ledgerClaims
  change ((original.slots.map (slot sources index)).map _).sum = _
  simp only [List.map_map, Function.comp_def, slot_matrix]

theorem accountAt_actual_matrix (initialZero : (sources index).initial.claims = fun _ _ _ => 0) (ordinal : Nat) :
    ledgerClaims sources (accountAt sources index ordinal).account.current =
      (ProgrammeSource.rawCurrent (sources index) (ProgrammeHistory.visitAt (sources index) ordinal).current).claims := by
  rw [accountAt_full_state, state_matrix]
  exact BalanceConservation.generated_prefix_claims (sources index) initialZero ordinal

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Embedding
