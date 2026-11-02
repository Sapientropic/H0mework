import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Movement
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Parsing

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation

open ResponsibilityLifecycle Source.Program Source.ProgrammeFace

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

theorem consume_without_instruction (origin : InstructionOrigin input)
    (state : (process input).GeneratedState) (absent : origin.instruction? input = none) :
    (consume input origin state).next input = state := by
  simp only [consume, issue_readout_absent input origin absent,
    movement_readout_absent input origin absent, InstructionResult.next]

theorem consume_refused (origin : InstructionOrigin input)
    (state : (process input).GeneratedState)
    (instruction : ExecutionItem Party Good Port Technology Instrument)
    (original : origin.instruction? input = some instruction)
    (refused : ¬input.law.Valid instruction.before instruction.request) :
    (consume input origin state).next input = state := by
  unfold consume
  rw [movement_readout_refused input origin instruction original refused]
  split
  next claim sameOrigin emitted =>
    have actual := claim.instruction_exact
    rw [sameOrigin] at actual
    have same := Option.some.inj (actual.symm.trans original)
    have accepted := claim.accepted
    rw [same] at accepted
    exact (refused accepted).elim
  all_goals rfl

theorem issued_claims_source_step (claim : IssuedClaim input)
    (state : (process input).GeneratedState)
    (matched : ledgerClaims input state.current = claim.instruction.before.claims) :
    ledgerClaims input (admit input state claim).current =
      (input.law.step claim.instruction.before claim.instruction.request).claims := by
  funext instrument debtor creditor
  rw [admit_ledgerClaims, matched]
  simp only [RawLaw.step, if_pos claim.accepted, RawLaw.paidStep, RawLaw.nextClaims, claim.issue_exact]

theorem consume_claims_source_step (origin : InstructionOrigin input)
    (state : (process input).GeneratedState)
    (instruction : ExecutionItem Party Good Port Technology Instrument)
    (original : origin.instruction? input = some instruction)
    (matched : ledgerClaims input state.current = instruction.before.claims) :
    ledgerClaims input ((consume input origin state).next input).current =
      (input.law.step instruction.before instruction.request).claims := by
  by_cases accepted : input.law.Valid instruction.before instruction.request
  · have requested := original_request_mem_word input origin instruction original
    cases operation : instruction.request.operation
    case issue instrument debtor holder quantity =>
        obtain ⟨claim, sameOrigin, emitted, sameInstruction⟩ := issue_readout_issued input origin
          instruction original instrument debtor holder quantity operation accepted
        simp only [consume, emitted, InstructionResult.next]
        have sourceMatched : ledgerClaims input state.current = claim.instruction.before.claims := by
          rw [sameInstruction]
          exact matched
        simpa only [sameInstruction] using issued_claims_source_step input claim state sourceMatched
    case settle instrument debtor holder quantity =>
        have noIssue := issue_readout_nonissue input origin instruction original (by
          intro i d h q; simp [operation])
        obtain ⟨movement, emitted⟩ := payment_readout_exists input origin instruction original
          instrument debtor holder quantity operation accepted
        simp only [consume, noIssue, emitted, InstructionResult.next]
        have same := Option.some.inj (movement.original.symm.trans original)
        have sourceMatched : ledgerClaims input state.current = movement.instruction.before.claims := by
          rw [same]
          exact matched
        simpa only [same] using matched_movement_claims input movement state sourceMatched
    case assign instrument debtor sender recipient quantity =>
        have noIssue := issue_readout_nonissue input origin instruction original (by
          intro i d h q; simp [operation])
        obtain ⟨movement, emitted⟩ := assignment_readout_exists input origin instruction original
          instrument debtor sender recipient quantity operation accepted
        simp only [consume, noIssue, emitted, InstructionResult.next]
        have same := Option.some.inj (movement.original.symm.trans original)
        have sourceMatched : ledgerClaims input state.current = movement.instruction.before.claims := by
          rw [same]
          exact matched
        simpa only [same] using matched_movement_claims input movement state sourceMatched
    all_goals
      have noIssue := issue_readout_nonissue input origin instruction original (by
        intro i d h q; simp [operation])
      have noMovement := movement_readout_nonmovement input origin instruction original
        (by intro i d h q; simp [operation]) (by intro i d s r q; simp [operation])
      simp only [consume, noIssue, noMovement, InstructionResult.next]
      simpa only [RawLaw.step, if_pos accepted, RawLaw.paidStep, RawLaw.nextClaims, operation] using matched
  · rw [consume_refused input origin state instruction original accepted,
      input.law.rejected_preserves_current instruction.before instruction.request accepted]
    exact matched

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation
