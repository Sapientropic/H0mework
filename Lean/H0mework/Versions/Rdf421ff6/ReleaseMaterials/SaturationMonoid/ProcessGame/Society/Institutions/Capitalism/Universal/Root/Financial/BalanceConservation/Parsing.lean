import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.SourceFacts

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

theorem issue_readout_absent (origin : InstructionOrigin input)
    (absent : origin.instruction? input = none) : readIssue input origin = .nonfinancial := by
  unfold readIssue
  split
  · rfl
  next instruction original => rw [absent] at original; cases original

theorem movement_readout_absent (origin : InstructionOrigin input)
    (absent : origin.instruction? input = none) : readMovement input origin = none := by
  unfold readMovement
  split
  · rfl
  next instruction original => rw [absent] at original; cases original

theorem issue_readout_nonissue (origin : InstructionOrigin input)
    (instruction : ExecutionItem Party Good Port Technology Instrument)
    (original : origin.instruction? input = some instruction)
    (nonissue : ∀ instrument debtor holder quantity,
      instruction.request.operation ≠ .issue instrument debtor holder quantity) :
    readIssue input origin = .nonfinancial := by
  unfold readIssue
  split
  · rfl
  next actual actualEq =>
    have same := Option.some.inj (actualEq.symm.trans original)
    subst actual
    split
    next instrument debtor holder quantity operation => exact (nonissue _ _ _ _ operation).elim
    all_goals rfl

theorem movement_readout_refused (origin : InstructionOrigin input)
    (instruction : ExecutionItem Party Good Port Technology Instrument)
    (original : origin.instruction? input = some instruction)
    (refused : ¬input.law.Valid instruction.before instruction.request) :
    readMovement input origin = none := by
  unfold readMovement
  split
  · rfl
  next actual actualEq =>
    have same := Option.some.inj (actualEq.symm.trans original)
    subst actual
    rw [dif_neg refused]

theorem movement_readout_nonmovement (origin : InstructionOrigin input)
    (instruction : ExecutionItem Party Good Port Technology Instrument)
    (original : origin.instruction? input = some instruction)
    (nonpayment : ∀ instrument debtor holder quantity,
      instruction.request.operation ≠ .settle instrument debtor holder quantity)
    (nonassignment : ∀ instrument debtor sender recipient quantity,
      instruction.request.operation ≠ .assign instrument debtor sender recipient quantity) :
    readMovement input origin = none := by
  unfold readMovement
  split
  · rfl
  next actual actualEq =>
    have same := Option.some.inj (actualEq.symm.trans original)
    subst actual
    split
    · split
      next instrument debtor holder quantity operation => exact (nonpayment _ _ _ _ operation).elim
      next instrument debtor sender recipient quantity operation =>
        exact (nonassignment _ _ _ _ _ operation).elim
      all_goals rfl
    · rfl

theorem issue_readout_issued (origin : InstructionOrigin input)
    (instruction : ExecutionItem Party Good Port Technology Instrument)
    (original : origin.instruction? input = some instruction)
    (instrument : Instrument) (debtor holder : Party) (quantity : ℚ)
    (operation : instruction.request.operation = .issue instrument debtor holder quantity)
    (accepted : input.law.Valid instruction.before instruction.request) :
    ∃ (claim : IssuedClaim input) (sameOrigin : claim.origin = origin),
      readIssue input origin = .issued claim sameOrigin ∧ claim.instruction = instruction := by
  unfold readIssue
  split
  next absent => rw [original] at absent; cases absent
  next actual actualEq =>
    have same := Option.some.inj (actualEq.symm.trans original)
    subst actual
    split <;> rename_i branchEq
    all_goals cases (operation.symm.trans branchEq)
    rw [dif_pos accepted]
    exact ⟨_, rfl, rfl, rfl⟩

theorem payment_readout_exists (origin : InstructionOrigin input)
    (instruction : ExecutionItem Party Good Port Technology Instrument)
    (original : origin.instruction? input = some instruction)
    (instrument : Instrument) (debtor holder : Party) (quantity : ℚ)
    (operation : instruction.request.operation = .settle instrument debtor holder quantity)
    (accepted : input.law.Valid instruction.before instruction.request) :
    ∃ movement, readMovement input origin = some movement := by
  unfold readMovement
  split
  next absent => rw [original] at absent; cases absent
  next actual actualEq =>
    have same := Option.some.inj (actualEq.symm.trans original)
    subst actual
    rw [dif_pos accepted]
    split <;> rename_i branchEq
    all_goals cases (operation.symm.trans branchEq)
    exact ⟨_, rfl⟩

theorem assignment_readout_exists (origin : InstructionOrigin input)
    (instruction : ExecutionItem Party Good Port Technology Instrument)
    (original : origin.instruction? input = some instruction)
    (instrument : Instrument) (debtor sender recipient : Party) (quantity : ℚ)
    (operation : instruction.request.operation = .assign instrument debtor sender recipient quantity)
    (accepted : input.law.Valid instruction.before instruction.request) :
    ∃ movement, readMovement input origin = some movement := by
  unfold readMovement
  split
  next absent => rw [original] at absent; cases absent
  next actual actualEq =>
    have same := Option.some.inj (actualEq.symm.trans original)
    subst actual
    rw [dif_pos accepted]
    split <;> rename_i branchEq
    all_goals cases (operation.symm.trans branchEq)
    exact ⟨_, rfl⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation
