import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation.Step
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.InventoryExact

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation

open ResponsibilityLifecycle Source.Program

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument) (sourceIndex : Index)

/-- Only literal decoded source instructions and the incoming ledger enter this fold. -/
theorem consumeOrigins_execute (origins : List (InstructionOrigin (sources sourceIndex)))
    (state : (process sources).GeneratedState) (current : RawCurrent Party Good Technology Instrument)
    (index : Nat) (event : RawEvent Party Good Port Technology Instrument)
    (sequence : origins.filterMap (InstructionOrigin.instruction? (sources sourceIndex)) =
      ((sources sourceIndex).law.execute current index event).items)
    (compatible : Compatible sources sourceIndex state.current)
    (matched : ledgerClaims sources state.current = current.claims) :
    ledgerClaims sources (consumeOrigins sources (origins.map (Sigma.mk sourceIndex)) state).current =
      ((sources sourceIndex).law.execute current index event).final.claims := by
  induction origins generalizing state current index event with
  | nil =>
      have lengthZero : event.length = 0 := by
        rw [← (sources sourceIndex).law.inventory_length current index event, ← sequence]
        rfl
      cases event with
      | nil => exact matched
      | cons request tail => simp at lengthZero
  | cons origin tail ih =>
      cases decoded : origin.instruction? (sources sourceIndex) with
      | none =>
          simp only [List.filterMap_cons, decoded] at sequence
          change ledgerClaims sources
            (consumeOrigins sources (tail.map (Sigma.mk sourceIndex)) ((consume sources ⟨sourceIndex, origin⟩ state).next sources)).current = _
          rw [consume_without_instruction sources ⟨sourceIndex, origin⟩ state decoded]
          exact ih state current index event sequence compatible matched
      | some instruction =>
          cases event with
          | nil => simp only [List.filterMap_cons, decoded, RawLaw.execute, List.cons_ne_nil] at sequence
          | cons request remaining =>
              have aligned : instruction :: tail.filterMap (InstructionOrigin.instruction? (sources sourceIndex)) =
                  ⟨index, current, request⟩ ::
                    ((sources sourceIndex).law.execute ((sources sourceIndex).law.step current request) (index + 1) remaining).items := by
                simpa only [List.filterMap_cons, decoded, RawLaw.execute] using sequence
              obtain ⟨same, after⟩ := List.cons.inj aligned
              have localMatch : ledgerClaims sources state.current = instruction.before.claims := by
                rw [same]
                exact matched
              have nextMatch := consume_claims_source_step sources ⟨sourceIndex, origin⟩ state instruction decoded compatible localMatch
              rw [same] at nextMatch
              exact ih ((consume sources ⟨sourceIndex, origin⟩ state).next sources)
                ((sources sourceIndex).law.step current request) (index + 1) remaining after
                (consume_compatible sources sourceIndex origin state compatible) nextMatch

theorem consumeOrigins_compatible (origins : List (InstructionOrigin (sources sourceIndex)))
    (state : (process sources).GeneratedState) (compatible : Compatible sources sourceIndex state.current) :
    Compatible sources sourceIndex (consumeOrigins sources (origins.map (Sigma.mk sourceIndex)) state).current := by
  induction origins generalizing state with
  | nil => exact compatible
  | cons origin tail ih => exact ih _ (consume_compatible sources sourceIndex origin state compatible)

theorem consumeVisit_claims_source_next (ordinal : Nat) (state : (process sources).GeneratedState)
    (compatible : Compatible sources sourceIndex state.current)
    (matched : ledgerClaims sources state.current =
      (ProgrammeSource.rawCurrent (sources sourceIndex) (ProgrammeHistory.visitAt (sources sourceIndex) ordinal).current).claims) :
    ledgerClaims sources (consumeVisit sources sourceIndex ordinal state).current =
      (ProgrammeSource.rawCurrent (sources sourceIndex) (ProgrammeHistory.visitAt (sources sourceIndex) (ordinal + 1)).current).claims := by
  change ledgerClaims sources (consumeVisit sources sourceIndex ordinal state).current =
    (ProgrammeSource.rawCurrent (sources sourceIndex) (ProgrammeSource.next (sources sourceIndex)
      (ProgrammeHistory.visitAt (sources sourceIndex) ordinal).current)).claims
  rw [ProgrammeSource.actual_raw_next]
  exact consumeOrigins_execute sources sourceIndex _ state _ 0 _
    (Financial.inventoryAt_instructions_exact _ _) compatible matched

theorem consumeVisit_compatible (ordinal : Nat) (state : (process sources).GeneratedState)
    (compatible : Compatible sources sourceIndex state.current) :
    Compatible sources sourceIndex (consumeVisit sources sourceIndex ordinal state).current :=
  consumeOrigins_compatible sources sourceIndex _ state compatible

theorem continueVisits_compatible (start count : Nat) (state : (process sources).GeneratedState)
    (compatible : Compatible sources sourceIndex state.current) :
    Compatible sources sourceIndex (continueVisits sources sourceIndex start count state).current := by
  induction count with
  | zero => exact compatible
  | succ count ih => exact consumeVisit_compatible sources sourceIndex _ _ ih

theorem continueVisits_claims_source (start count : Nat) (state : (process sources).GeneratedState)
    (compatible : Compatible sources sourceIndex state.current)
    (matched : ledgerClaims sources state.current =
      (ProgrammeSource.rawCurrent (sources sourceIndex) (ProgrammeHistory.visitAt (sources sourceIndex) start).current).claims) :
    ledgerClaims sources (continueVisits sources sourceIndex start count state).current =
      (ProgrammeSource.rawCurrent (sources sourceIndex) (ProgrammeHistory.visitAt (sources sourceIndex) (start + count)).current).claims := by
  induction count with
  | zero => exact matched
  | succ count ih =>
      exact consumeVisit_claims_source_next sources sourceIndex _ _
        (continueVisits_compatible sources sourceIndex start count state compatible) ih

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation
