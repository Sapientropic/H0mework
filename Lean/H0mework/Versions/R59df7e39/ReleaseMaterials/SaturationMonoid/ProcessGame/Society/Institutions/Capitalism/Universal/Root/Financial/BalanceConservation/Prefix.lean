import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Execution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation

open ResponsibilityLifecycle Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

/-- The native prefix is matched to the next original intermediate state,
including administrative rows and rejected requests. -/
theorem prefix_claims_before_original (origins : List (InstructionOrigin input))
    (state : (process input).GeneratedState) (current : RawCurrent Party Good Technology Instrument)
    (index : Nat) (event : RawEvent Party Good Port Technology Instrument)
    (sequence : origins.filterMap (InstructionOrigin.instruction? input) =
      (input.law.execute current index event).items)
    (matched : ledgerClaims input state.current = current.claims)
    (position : Nat) (origin : InstructionOrigin input)
    (instruction : ExecutionItem Party Good Port Technology Instrument)
    (present : origins[position]? = some origin)
    (original : origin.instruction? input = some instruction) :
    ledgerClaims input (consumeOrigins input (origins.take position) state).current =
      instruction.before.claims := by
  induction origins generalizing state current index event position with
  | nil => simp at present
  | cons head tail ih =>
      cases position with
      | zero =>
          have sameOrigin : head = origin := by simpa using present
          rw [← sameOrigin] at original
          cases event with
          | nil => simp only [List.filterMap_cons, original, RawLaw.execute,
              List.cons_ne_nil] at sequence
          | cons request remaining =>
              have aligned : instruction :: tail.filterMap (InstructionOrigin.instruction? input) =
                  ⟨index, current, request⟩ ::
                    (input.law.execute (input.law.step current request) (index + 1) remaining).items := by
                simpa only [List.filterMap_cons, original, RawLaw.execute] using sequence
              have same := (List.cons.inj aligned).1
              change ledgerClaims input state.current = instruction.before.claims
              rw [same]
              exact matched
      | succ position =>
          have later : tail[position]? = some origin := by simpa using present
          change ledgerClaims input
            (consumeOrigins input (tail.take position) ((consume input head state).next input)).current = _
          cases decoded : head.instruction? input with
          | none =>
              simp only [List.filterMap_cons, decoded] at sequence
              rw [consume_without_instruction input head state decoded]
              exact ih state current index event sequence matched position later
          | some first =>
              cases event with
              | nil => simp only [List.filterMap_cons, decoded, RawLaw.execute,
                  List.cons_ne_nil] at sequence
              | cons request remaining =>
                  have aligned : first :: tail.filterMap (InstructionOrigin.instruction? input) =
                      ⟨index, current, request⟩ ::
                        (input.law.execute (input.law.step current request) (index + 1) remaining).items := by
                    simpa only [List.filterMap_cons, decoded, RawLaw.execute] using sequence
                  obtain ⟨same, after⟩ := List.cons.inj aligned
                  have localMatch : ledgerClaims input state.current = first.before.claims := by
                    rw [same]
                    exact matched
                  have nextMatch := consume_claims_source_step input head state first decoded localMatch
                  rw [same] at nextMatch
                  exact ih ((consume input head state).next input) (input.law.step current request)
                    (index + 1) remaining after nextMatch position later

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation
