import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Coordinates

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

inductive ReviewKind
  | payment (holder : Holder input)
  | assignment (sender recipient : Holder input)

def reviewOperation (claim : IssuedClaim input) (kind : ReviewKind input) (quantity : ℚ) :
    Operation Party Good Technology Instrument :=
  match kind with
  | .payment holder => .settle claim.instrument claim.debtor (holderParty input holder) quantity
  | .assignment sender recipient =>
      .assign claim.instrument claim.debtor (holderParty input sender) (holderParty input recipient) quantity

structure Review (claim : IssuedClaim input) where
  private mk ::
  origin : InstructionOrigin input
  instruction : ExecutionItem Party Good Port Technology Instrument
  instruction_exact : origin.instruction? input = some instruction
  kind : ReviewKind input
  quantity : ℚ
  operation_exact : instruction.request.operation = reviewOperation input claim kind quantity
  accepted : input.law.Valid instruction.before instruction.request

namespace Review

def fromHolder {claim : IssuedClaim input} (review : Review input claim) : Holder input :=
  match review.kind with
  | .payment holder => holder
  | .assignment sender _ => sender

def toHolder {claim : IssuedClaim input} (review : Review input claim) : Holder input :=
  match review.kind with
  | .payment holder => holder
  | .assignment _ recipient => recipient

def senderBirth {claim : IssuedClaim input} (review : Review input claim) :
    Source.ProgrammeFace.ActualBirth.At input review.origin.visit
      (holderParty input (review.fromHolder input)) :=
  review.origin.participantBirth input review.instruction review.instruction_exact _ (by
    rw [review.operation_exact]
    cases kind : review.kind <;> simp [reviewOperation, fromHolder, kind,
      Source.ProgrammeFace.operationParties])

def recipientBirth {claim : IssuedClaim input} (review : Review input claim) :
    Source.ProgrammeFace.ActualBirth.At input review.origin.visit
      (holderParty input (review.toHolder input)) :=
  review.origin.participantBirth input review.instruction review.instruction_exact _ (by
    rw [review.operation_exact]
    cases kind : review.kind <;> simp [reviewOperation, toHolder, kind,
      Source.ProgrammeFace.operationParties])

def allocated {claim : IssuedClaim input} (review : Review input claim)
    (balance : Balance input) (remaining : ℚ) : ℚ :=
  min remaining (balance (review.fromHolder input))

def after {claim : IssuedClaim input} (review : Review input claim)
    (balance : Balance input) (remaining : ℚ) : Balance input :=
  let used := review.allocated input balance remaining
  match review.kind with
  | .payment holder => pay input balance holder used
  | .assignment sender recipient => assign input balance sender recipient used

omit [DecidableEq Port] in
theorem quantity_nonnegative {claim : IssuedClaim input} (review : Review input claim) :
    0 ≤ review.quantity := by
  have guarded := review.accepted.2.2.1
  unfold RawLaw.ClaimGuard at guarded
  rw [review.operation_exact] at guarded
  cases kind : review.kind <;>
    simp only [reviewOperation, kind] at guarded <;> exact guarded.1

omit [DecidableEq Port] in
theorem allocated_nonnegative {claim : IssuedClaim input} (review : Review input claim)
    (balance : Balance input) (remaining : ℚ)
    (balance_nonnegative : Nonnegative input balance) (available : 0 ≤ remaining) :
    0 ≤ review.allocated input balance remaining :=
  le_min available (balance_nonnegative _)

omit [DecidableEq Port] in
theorem allocated_le_available {claim : IssuedClaim input} (review : Review input claim)
    (balance : Balance input) (remaining : ℚ) :
    review.allocated input balance remaining ≤ remaining := min_le_left _ _

omit [DecidableEq Port] in
theorem allocated_le_old_share {claim : IssuedClaim input} (review : Review input claim)
    (balance : Balance input) (remaining : ℚ) :
    review.allocated input balance remaining ≤ balance (review.fromHolder input) := min_le_right _ _

omit [DecidableEq Port] in
theorem after_nonnegative {claim : IssuedClaim input} (review : Review input claim)
    (balance : Balance input) (remaining : ℚ)
    (balance_nonnegative : Nonnegative input balance) (available : 0 ≤ remaining) :
    Nonnegative input (review.after input balance remaining) := by
  have positive := review.allocated_nonnegative input balance remaining balance_nonnegative available
  have bounded := review.allocated_le_old_share input balance remaining
  cases kind : review.kind with
  | payment holder =>
      simp only [after, kind]
      exact pay_nonnegative input balance holder _ balance_nonnegative (by
        simpa only [fromHolder, kind] using bounded)
  | assignment sender recipient =>
      simp only [after, kind]
      exact assign_nonnegative input balance sender recipient _ balance_nonnegative positive (by
        simpa only [fromHolder, kind] using bounded)

end Review

def readReview (claim : IssuedClaim input) (origin : InstructionOrigin input) :
    Option (Review input claim) :=
  match original : origin.instruction? input with
  | none => none
  | some instruction =>
      if accepted : input.law.Valid instruction.before instruction.request then
        match operation : instruction.request.operation with
        | .settle instrument debtor holder quantity =>
            if instrument_eq : instrument = claim.instrument then
              if debtor_eq : debtor = claim.debtor then
                some ⟨origin, instruction, original, .payment (holderIndex input holder),
                  quantity, by
                    simpa only [reviewOperation, holderParty_index, ← instrument_eq, ← debtor_eq] using operation,
                  accepted⟩
              else none
            else none
        | .assign instrument debtor sender recipient quantity =>
            if instrument_eq : instrument = claim.instrument then
              if debtor_eq : debtor = claim.debtor then
                some ⟨origin, instruction, original,
                  .assignment (holderIndex input sender) (holderIndex input recipient),
                  quantity, by
                    simpa only [reviewOperation, holderParty_index, ← instrument_eq, ← debtor_eq] using operation,
                  accepted⟩
              else none
            else none
        | .produce _ | .transfer _ _ _ | .use _ _ _ | .issue _ _ _ _ | .revise _ _ | .present => none
      else none

omit [DecidableEq Port] in
theorem readReview_payment_complete (claim : IssuedClaim input) (origin : InstructionOrigin input)
    (instruction : ExecutionItem Party Good Port Technology Instrument)
    (original : origin.instruction? input = some instruction)
    (holder : Party) (quantity : ℚ)
    (operation : instruction.request.operation = .settle claim.instrument claim.debtor holder quantity)
    (accepted : input.law.Valid instruction.before instruction.request) :
    ∃ receipt, readReview input claim origin = some receipt ∧
      receipt.origin = origin ∧ receipt.kind = .payment (holderIndex input holder) ∧
      receipt.quantity = quantity := by
  unfold readReview
  split
  · rename_i absent
    have impossible := absent.symm.trans original
    cases impossible
  · rename_i actual actualEq
    have same := Option.some.inj (actualEq.symm.trans original)
    subst actual
    rw [dif_pos accepted]
    split <;> rename_i branchEq
    all_goals cases (operation.symm.trans branchEq)
    simp only
    exact ⟨_, rfl, rfl, rfl, rfl⟩

omit [DecidableEq Port] in
theorem readReview_assignment_complete (claim : IssuedClaim input) (origin : InstructionOrigin input)
    (instruction : ExecutionItem Party Good Port Technology Instrument)
    (original : origin.instruction? input = some instruction)
    (sender recipient : Party) (quantity : ℚ)
    (operation : instruction.request.operation = .assign claim.instrument claim.debtor sender recipient quantity)
    (accepted : input.law.Valid instruction.before instruction.request) :
    ∃ receipt, readReview input claim origin = some receipt ∧
      receipt.origin = origin ∧
      receipt.kind = .assignment (holderIndex input sender) (holderIndex input recipient) ∧
      receipt.quantity = quantity := by
  unfold readReview
  split
  · rename_i absent
    have impossible := absent.symm.trans original
    cases impossible
  · rename_i actual actualEq
    have same := Option.some.inj (actualEq.symm.trans original)
    subst actual
    rw [dif_pos accepted]
    split <;> rename_i branchEq
    all_goals cases (operation.symm.trans branchEq)
    simp only
    exact ⟨_, rfl, rfl, rfl, rfl⟩

omit [DecidableEq Port] in
theorem readReview_origin (claim : IssuedClaim input) (origin : InstructionOrigin input)
    (receipt : Review input claim) (returned : readReview input claim origin = some receipt) :
    receipt.origin = origin := by
  unfold readReview at returned
  repeat' first
    | rfl
    | contradiction
    | split at returned
    | (cases Option.some.inj returned; rfl)

namespace ReviewSource

/-- Source matching branches; instruction lookup, validity, equality and memory internals
    retain their primitive costs. -/
inductive Event where
  | cached (status : Fin 3)
  | originRead (present : Bool)
  | accepted (valid : Bool)
  | operation (kind : Fin 3)
  | instrument (matched : Bool)
  | debtor (matched : Bool)
  | assemble (assignment : Bool) (quantity : ℚ)
  deriving DecidableEq
private structure Part (α : Type) where
  value : α
  work : List Event
private def produce (claim : IssuedClaim input) (origin : InstructionOrigin input) :
    Part (Option (Review input claim)) :=
  match original : origin.instruction? input with
  | none => ⟨none,[.originRead false]⟩
  | some instruction =>
    if accepted : input.law.Valid instruction.before instruction.request then
      match operation : instruction.request.operation with
      | .settle instrument debtor holder quantity =>
        if instrument_eq : instrument = claim.instrument then
          if debtor_eq : debtor = claim.debtor then
            ⟨some ⟨origin,instruction,original,.payment (holderIndex input holder),quantity,by
              simpa only [reviewOperation,holderParty_index,← instrument_eq,← debtor_eq] using operation,accepted⟩,
              [.originRead true,.accepted true,.operation 0,.instrument true,.debtor true,.assemble false quantity]⟩
          else ⟨none,[.originRead true,.accepted true,.operation 0,.instrument true,.debtor false]⟩
        else ⟨none,[.originRead true,.accepted true,.operation 0,.instrument false]⟩
      | .assign instrument debtor sender recipient quantity =>
        if instrument_eq : instrument = claim.instrument then
          if debtor_eq : debtor = claim.debtor then
            ⟨some ⟨origin,instruction,original,.assignment (holderIndex input sender) (holderIndex input recipient),quantity,by
              simpa only [reviewOperation,holderParty_index,← instrument_eq,← debtor_eq] using operation,accepted⟩,
              [.originRead true,.accepted true,.operation 1,.instrument true,.debtor true,.assemble true quantity]⟩
          else ⟨none,[.originRead true,.accepted true,.operation 1,.instrument true,.debtor false]⟩
        else ⟨none,[.originRead true,.accepted true,.operation 1,.instrument false]⟩
      | .produce _ | .transfer _ _ _ | .use _ _ _ | .issue _ _ _ _ | .revise _ _ | .present =>
        ⟨none,[.originRead true,.accepted true,.operation 2]⟩
    else ⟨none,[.originRead true,.accepted false]⟩
omit [DecidableEq Port] in
private theorem produce_exact (claim : IssuedClaim input) (origin : InstructionOrigin input) :
    (produce input claim origin).value = readReview input claim origin := by
  unfold produce readReview
  repeat' first | split | rfl
omit [DecidableEq Port] in
private theorem produce_work (claim : IssuedClaim input) (origin : InstructionOrigin input) :
    (produce input claim origin).work.length ≤ 6 := by
  unfold produce
  repeat' first | split | (solve | simp)

structure Compilation (claim : IssuedClaim input) (origin : InstructionOrigin input) where
  private mk ::
  receipt : Option (Review input claim)
  work : List Event
  exact : receipt = readReview input claim origin
  private generated : receipt = (produce input claim origin).value ∧ work = (produce input claim origin).work

def compile (claim : IssuedClaim input) (origin : InstructionOrigin input) : Compilation input claim origin :=
  let made := produce input claim origin
  ⟨made.value,made.work,produce_exact input claim origin,⟨rfl,rfl⟩⟩
omit [DecidableEq Port] in
theorem work_bound (claim : IssuedClaim input) (origin : InstructionOrigin input) :
    (compile input claim origin).work.length ≤ 6 := produce_work input claim origin

omit [DecidableEq Port] in
theorem Compilation.origin_exact {claim : IssuedClaim input} {origin : InstructionOrigin input}
    (made : Compilation input claim origin) (review : Review input claim) (present : made.receipt = some review) :
    review.origin = origin := readReview_origin input claim origin review (made.exact.symm.trans present)

private def produceFrom (claim : IssuedClaim input) {origin : InstructionOrigin input}
    (source : InstructionSource.Compilation input origin) : Part (Option (Review input claim)) :=
  match source.decoded with
  | .absent _ => ⟨none,[.cached 0]⟩
  | .refused _ _ _ => ⟨none,[.cached 1]⟩
  | .accepted instruction original accepted =>
      match operation : instruction.request.operation with
      | .settle instrument debtor holder quantity =>
        if instrument_eq : instrument = claim.instrument then
          if debtor_eq : debtor = claim.debtor then
            ⟨some ⟨origin,instruction,original,.payment (holderIndex input holder),quantity,by
              simpa only [reviewOperation,holderParty_index,← instrument_eq,← debtor_eq] using operation,accepted⟩,
              [.cached 2,.operation 0,.instrument true,.debtor true,.assemble false quantity]⟩
          else ⟨none,[.cached 2,.operation 0,.instrument true,.debtor false]⟩
        else ⟨none,[.cached 2,.operation 0,.instrument false]⟩
      | .assign instrument debtor sender recipient quantity =>
        if instrument_eq : instrument = claim.instrument then
          if debtor_eq : debtor = claim.debtor then
            ⟨some ⟨origin,instruction,original,.assignment (holderIndex input sender) (holderIndex input recipient),quantity,by
              simpa only [reviewOperation,holderParty_index,← instrument_eq,← debtor_eq] using operation,accepted⟩,
              [.cached 2,.operation 1,.instrument true,.debtor true,.assemble true quantity]⟩
          else ⟨none,[.cached 2,.operation 1,.instrument true,.debtor false]⟩
        else ⟨none,[.cached 2,.operation 1,.instrument false]⟩
      | .produce _ | .transfer _ _ _ | .use _ _ _ | .issue _ _ _ _ | .revise _ _ | .present =>
        ⟨none,[.cached 2,.operation 2]⟩
omit [DecidableEq Port] in
private theorem from_exact (claim : IssuedClaim input) {origin : InstructionOrigin input}
    (source : InstructionSource.Compilation input origin) :
    (produceFrom input claim source).value = readReview input claim origin := by
  cases decoded : source.decoded <;> unfold produceFrom readReview <;> rw [decoded]
  all_goals
    dsimp only
    repeat' first | split | (solve | rfl | simp_all | grind)

omit [DecidableEq Port] in
private theorem from_work (claim : IssuedClaim input) {origin : InstructionOrigin input}
    (source : InstructionSource.Compilation input origin) :
    (produceFrom input claim source).work.length ≤ 5 := by
  unfold produceFrom
  repeat' first | split | (solve | simp)
structure FromCompilation (claim : IssuedClaim input) {origin : InstructionOrigin input}
    (source : InstructionSource.Compilation input origin) where
  private mk ::
  receipt : Option (Review input claim)
  work : List Event
  exact : receipt = readReview input claim origin
  private generated : receipt = (produceFrom input claim source).value ∧ work = (produceFrom input claim source).work

def compileFrom (claim : IssuedClaim input) {origin : InstructionOrigin input}
    (source : InstructionSource.Compilation input origin) : FromCompilation input claim source :=
  let made := produceFrom input claim source
  ⟨made.value,made.work,from_exact input claim source,⟨rfl,rfl⟩⟩
omit [DecidableEq Port] in
theorem from_work_bound (claim : IssuedClaim input) {origin : InstructionOrigin input}
    (source : InstructionSource.Compilation input origin) :
    (compileFrom input claim source).work.length ≤ 5 := from_work input claim source
end ReviewSource

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial
