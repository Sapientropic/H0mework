import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Allocation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial

open ResponsibilityLifecycle Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

inductive MovementKind
  | payment
  | assignment

structure Movement (origin : InstructionOrigin input) where
  private mk ::
  instruction : ExecutionItem Party Good Port Technology Instrument
  original : origin.instruction? input = some instruction
  kind : MovementKind
  instrument : Instrument
  debtor : Party
  sender : Party
  recipient : Party
  quantity : ℚ
  operation_exact : instruction.request.operation =
    match kind with
    | .payment => .settle instrument debtor sender quantity
    | .assignment => .assign instrument debtor sender recipient quantity
  accepted : input.law.Valid instruction.before instruction.request

omit [DecidableEq Port] in
theorem Movement.quantity_nonnegative {origin : InstructionOrigin input} (movement : Movement input origin) :
    0 ≤ movement.quantity := by
  have guard := movement.accepted.2.2.1
  unfold RawLaw.ClaimGuard at guard
  rw [movement.operation_exact] at guard
  cases kind : movement.kind <;> simp only [kind] at guard <;> exact guard.1

def readMovement (origin : InstructionOrigin input) : Option (Movement input origin) :=
  match original : origin.instruction? input with
  | none => none
  | some instruction =>
      if accepted : input.law.Valid instruction.before instruction.request then
        match operation : instruction.request.operation with
        | .settle instrument debtor sender quantity =>
            some ⟨instruction, original, .payment, instrument, debtor, sender, sender,
              quantity, operation, accepted⟩
        | .assign instrument debtor sender recipient quantity =>
            some ⟨instruction, original, .assignment, instrument, debtor, sender, recipient,
              quantity, operation, accepted⟩
        | .produce _ | .transfer _ _ _ | .use _ _ _ | .issue _ _ _ _ | .revise _ _ | .present => none
      else none

inductive InstructionResult (origin : InstructionOrigin input) (before : (process input).GeneratedState)
  | issued (claim : IssuedClaim input) (exactOrigin : claim.origin = origin)
  | movement (source : Movement input origin)
      (allocation : Allocation input before source.quantity)
  | retained
  | refused (instruction : ExecutionItem Party Good Port Technology Instrument)
      (original : origin.instruction? input = some instruction)
      (refused : ¬ input.law.Valid instruction.before instruction.request)
  | missingBirth (party : Party) (notBorn : party ∉ bornParties input)

namespace InstructionResult

def next {origin : InstructionOrigin input} {before : (process input).GeneratedState} :
    InstructionResult input origin before → (process input).GeneratedState
  | .issued claim _ => admit input before claim
  | .movement _ allocation => allocation.after
  | .retained | .refused .. | .missingBirth .. => before

def transition {origin : InstructionOrigin input} {before : (process input).GeneratedState}
    (result : InstructionResult input origin before) :
    (process input).Run before.current (result.next input).current := by
  cases result with
  | issued claim _ => exact .step .nil (.admit (P := process input) claim)
  | movement _ allocation => exact allocation.transition
  | retained => exact .nil
  | refused _ _ _ => exact .nil
  | missingBirth _ _ => exact .nil

theorem history_retained {origin : InstructionOrigin input} {before : (process input).GeneratedState}
    (result : InstructionResult input origin before) :
    before.current.history <+: (result.next input).current.history := by
  rw [(result.transition input).history_eq]
  exact List.prefix_append _ _

theorem original_claims_retained {origin : InstructionOrigin input} {before : (process input).GeneratedState}
    (result : InstructionResult input origin before) :
    before.current.slots.map (slotClaim input) <+:
      (result.next input).current.slots.map (slotClaim input) := by
  cases result with
  | issued claim exactOrigin =>
      change _ <+: (before.current.slots ++ _).map _
      rw [List.map_append]
      exact List.prefix_append _ _
  | movement _ allocation => rw [next, allocation.original_claims]
  | retained => exact List.prefix_rfl
  | refused _ _ _ => exact List.prefix_rfl
  | missingBirth _ _ => exact List.prefix_rfl

/-- A nonzero unmatched quota stays attached to this exact original row;
it is not reconstructed as a fresh financial origin. -/
def Unallocated {origin : InstructionOrigin input} {before : (process input).GeneratedState} :
    InstructionResult input origin before → Prop
  | .movement _ allocation => 0 < allocation.remaining
  | _ => False

end InstructionResult

def consume (origin : InstructionOrigin input) (before : (process input).GeneratedState) :
    InstructionResult input origin before :=
  match readIssue input origin with
  | .issued claim exactOrigin => .issued claim exactOrigin
  | .rejected instruction original refused => .refused instruction original refused
  | .missingBirth party notBorn => .missingBirth party notBorn
  | .nonfinancial =>
      match readMovement input origin with
      | some movement => .movement movement
          (allocate input origin before movement.quantity (movement.quantity_nonnegative input))
      | none => .retained

theorem issued_appends_actual_original_debt (origin : InstructionOrigin input)
    (before : (process input).GeneratedState) (claim : IssuedClaim input)
    (exactOrigin : claim.origin = origin)
    (emitted : readIssue input origin = .issued claim exactOrigin) :
    ((consume input origin before).next input).current.slots[before.current.slots.length]? =
      some (.live (admission input claim).toObligation) := by
  simp only [consume, emitted, InstructionResult.next]
  exact admit_keeps_original_bearer input before claim

namespace MovementSource
inductive Event where
  | cached (status : Fin 3)
  | operation (kind : Fin 3)
  | assemble
  deriving DecidableEq
private def produce {origin : InstructionOrigin input} (source : InstructionSource.Compilation input origin) :
    Option (Movement input origin) × List Event :=
  match source.decoded with
  | .absent _ => ⟨none,[.cached 0]⟩
  | .refused _ _ _ => ⟨none,[.cached 1]⟩
  | .accepted instruction original accepted =>
      match operation : instruction.request.operation with
      | .settle instrument debtor sender quantity =>
          ⟨some ⟨instruction,original,.payment,instrument,debtor,sender,sender,quantity,operation,accepted⟩,
            [.cached 2,.operation 0,.assemble]⟩
      | .assign instrument debtor sender recipient quantity =>
          ⟨some ⟨instruction,original,.assignment,instrument,debtor,sender,recipient,quantity,operation,accepted⟩,
            [.cached 2,.operation 1,.assemble]⟩
      | .produce _ | .transfer _ _ _ | .use _ _ _ | .issue _ _ _ _ | .revise _ _ | .present =>
          ⟨none,[.cached 2,.operation 2]⟩
omit [DecidableEq Port] in
private theorem produce_exact {origin : InstructionOrigin input} (source : InstructionSource.Compilation input origin) :
    (produce input source).1 = readMovement input origin := by
  cases decoded : source.decoded <;> unfold produce readMovement <;> rw [decoded]
  all_goals
    dsimp only
    repeat' first | split | (solve | rfl | simp_all | grind)

omit [DecidableEq Port] in
private theorem produce_work {origin : InstructionOrigin input} (source : InstructionSource.Compilation input origin) :
    (produce input source).2.length ≤ 3 := by
  unfold produce
  split
  · simp
  · simp
  · split <;> simp
structure Compilation {origin : InstructionOrigin input} (source : InstructionSource.Compilation input origin) where
  private mk ::
  receipt : Option (Movement input origin)
  work : List Event
  exact : receipt = readMovement input origin
  private generated : receipt = (produce input source).1 ∧ work = (produce input source).2

def compileFrom {origin : InstructionOrigin input} (source : InstructionSource.Compilation input origin) : Compilation input source :=
  let made := produce input source
  ⟨made.1,made.2,produce_exact input source,⟨rfl,rfl⟩⟩
omit [DecidableEq Port] in
theorem work_bound {origin : InstructionOrigin input} (source : InstructionSource.Compilation input origin) :
    (compileFrom input source).work.length ≤ 3 := produce_work input source
end MovementSource

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial
