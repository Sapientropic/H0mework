import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation.Movement
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Parsing

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation

open ResponsibilityLifecycle Source.Program Source.ProgrammeFace Financial.BalanceConservation

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

theorem consume_without_instruction (origin : Origin sources)
    (state : (process sources).GeneratedState) (absent : origin.2.instruction? (sources origin.1) = none) :
    (consume sources origin state).next sources = state := by
  simp only [consume, issue_readout_absent (sources origin.1) origin.2 absent,
    movement_readout_absent (sources origin.1) origin.2 absent, InstructionResult.next]

theorem consume_refused (origin : Origin sources)
    (state : (process sources).GeneratedState)
    (instruction : ExecutionItem Party Good Port Technology Instrument)
    (original : origin.2.instruction? (sources origin.1) = some instruction)
    (refused : ¬(sources origin.1).law.Valid instruction.before instruction.request) :
    (consume sources origin state).next sources = state := by
  unfold consume
  rw [movement_readout_refused (sources origin.1) origin.2 instruction original refused]
  split
  next claim sameOrigin emitted =>
    have actual := claim.instruction_exact
    rw [sameOrigin] at actual
    have same := Option.some.inj (actual.symm.trans original)
    have accepted := claim.accepted
    rw [same] at accepted
    exact (refused accepted).elim
  all_goals rfl

theorem issued_claims_source_step (claim : Claim sources)
    (state : (process sources).GeneratedState)
    (matched : ledgerClaims sources state.current = claim.2.instruction.before.claims) :
    ledgerClaims sources (admit sources state claim).current =
      ((sources claim.1).law.step claim.2.instruction.before claim.2.instruction.request).claims := by
  funext instrument debtor creditor
  rw [admit_ledgerClaims, matched]
  simp only [RawLaw.step, if_pos claim.2.accepted, RawLaw.paidStep, RawLaw.nextClaims, claim.2.issue_exact]

theorem consume_claims_source_step (origin : Origin sources)
    (state : (process sources).GeneratedState)
    (instruction : ExecutionItem Party Good Port Technology Instrument)
    (original : origin.2.instruction? (sources origin.1) = some instruction)
    (compatible : Compatible sources origin.1 state.current)
    (matched : ledgerClaims sources state.current = instruction.before.claims) :
    ledgerClaims sources ((consume sources origin state).next sources).current =
      ((sources origin.1).law.step instruction.before instruction.request).claims := by
  by_cases accepted : (sources origin.1).law.Valid instruction.before instruction.request
  · have requested := original_request_mem_word (sources origin.1) origin.2 instruction original
    cases operation : instruction.request.operation
    case issue instrument debtor holder quantity =>
        obtain ⟨claim, sameOrigin, emitted, sameInstruction⟩ := issue_readout_issued (sources origin.1) origin.2
          instruction original instrument debtor holder quantity operation accepted
        simp only [consume, emitted, InstructionResult.next]
        have sourceMatched : ledgerClaims sources state.current = claim.instruction.before.claims := by
          rw [sameInstruction]
          exact matched
        simpa only [sameInstruction] using issued_claims_source_step sources ⟨origin.1, claim⟩ state sourceMatched
    case settle instrument debtor holder quantity =>
        have noIssue := issue_readout_nonissue (sources origin.1) origin.2 instruction original (by
          intro i d h q; simp [operation])
        obtain ⟨movement, emitted⟩ := payment_readout_exists (sources origin.1) origin.2 instruction original
          instrument debtor holder quantity operation accepted
        simp only [consume, noIssue, emitted, InstructionResult.next]
        have same := Option.some.inj (movement.original.symm.trans original)
        have sourceMatched : ledgerClaims sources state.current = movement.instruction.before.claims := by
          rw [same]
          exact matched
        simpa only [same] using matched_movement_claims sources movement emitted state compatible sourceMatched
    case assign instrument debtor sender recipient quantity =>
        have noIssue := issue_readout_nonissue (sources origin.1) origin.2 instruction original (by
          intro i d h q; simp [operation])
        obtain ⟨movement, emitted⟩ := assignment_readout_exists (sources origin.1) origin.2 instruction original
          instrument debtor sender recipient quantity operation accepted
        simp only [consume, noIssue, emitted, InstructionResult.next]
        have same := Option.some.inj (movement.original.symm.trans original)
        have sourceMatched : ledgerClaims sources state.current = movement.instruction.before.claims := by
          rw [same]
          exact matched
        simpa only [same] using matched_movement_claims sources movement emitted state compatible sourceMatched
    all_goals
      have noIssue := issue_readout_nonissue (sources origin.1) origin.2 instruction original (by
        intro i d h q; simp [operation])
      have noMovement := movement_readout_nonmovement (sources origin.1) origin.2 instruction original
        (by intro i d h q; simp [operation]) (by intro i d s r q; simp [operation])
      simp only [consume, noIssue, noMovement, InstructionResult.next]
      simpa only [RawLaw.step, if_pos accepted, RawLaw.paidStep, RawLaw.nextClaims, operation] using matched
  · rw [consume_refused sources origin state instruction original accepted,
      (sources origin.1).law.rejected_preserves_current instruction.before instruction.request accepted]
    exact matched

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation
