import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Step
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Fold

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation

open ResponsibilityLifecycle Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

/-- The sequence premise identifies original emitted instructions, including
their computed intermediate states; it supplies no financial endpoint. -/
theorem consumeOrigins_execute (origins : List (InstructionOrigin input))
    (state : (process input).GeneratedState) (current : RawCurrent Party Good Technology Instrument)
    (index : Nat) (event : RawEvent Party Good Port Technology Instrument)
    (sequence : origins.filterMap (InstructionOrigin.instruction? input) =
      (input.law.execute current index event).items)
    (matched : ledgerClaims input state.current = current.claims) :
    ledgerClaims input (consumeOrigins input origins state).current =
      (input.law.execute current index event).final.claims := by
  induction origins generalizing state current index event with
  | nil =>
      have lengthZero : event.length = 0 := by
        rw [← input.law.inventory_length current index event, ← sequence]
        rfl
      cases event with
      | nil => exact matched
      | cons request tail => simp at lengthZero
  | cons origin tail ih =>
      cases decoded : origin.instruction? input with
      | none =>
          simp only [List.filterMap_cons, decoded] at sequence
          change ledgerClaims input
            (consumeOrigins input tail ((consume input origin state).next input)).current = _
          rw [consume_without_instruction input origin state decoded]
          exact ih state current index event sequence matched
      | some instruction =>
          cases event with
          | nil => simp only [List.filterMap_cons, decoded, RawLaw.execute, List.cons_ne_nil] at sequence
          | cons request remaining =>
              have aligned : instruction :: tail.filterMap (InstructionOrigin.instruction? input) =
                  ⟨index, current, request⟩ ::
                    (input.law.execute (input.law.step current request) (index + 1) remaining).items := by
                simpa only [List.filterMap_cons, decoded, RawLaw.execute] using sequence
              obtain ⟨same, after⟩ := List.cons.inj aligned
              have localMatch : ledgerClaims input state.current = instruction.before.claims := by
                rw [same]
                exact matched
              have nextMatch := consume_claims_source_step input origin state instruction decoded localMatch
              rw [same] at nextMatch
              exact ih ((consume input origin state).next input) (input.law.step current request)
                (index + 1) remaining after nextMatch

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation
