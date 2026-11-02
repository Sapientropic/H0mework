import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.ActualBirth
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Validity

/-! Financial origins are restrictions of actual visits and their original
instruction trace.  Raw party keys remain coordinates; the debtor and
holder actors are the earliest original M0 births found by folding the
already generated history of this same programme. -/


set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Source Source.Program Source.ProgrammeFace

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

abbrev BirthActor := ActualBirth.Actor input

def bornParties : List Party := parties input.law ((Registered.reader input).raw (Registered.genesis input))

def actorOf (party : Party) (born : party ∈ bornParties input) : BirthActor input :=
  (ActualBirth.generate input (ProgrammeHistory.visitAt input 1) party born).actor input

structure InstructionOrigin where
  visit : RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot
  item : OpenResponsibilityAt (ProgrammeSource.N input)
    (ProgrammeSource.supportAt input visit.current)
  traceIndex? : Option Nat := none

namespace InstructionOrigin

def event (origin : InstructionOrigin input) :
    ContinuingEventAt (ProgrammeSource.ledgerSource input) origin.visit.current :=
  ⟨ProgrammeSource.emitted input origin.visit.current, rfl⟩

def instruction? (origin : InstructionOrigin input) :
    Option (ExecutionItem Party Good Port Technology Instrument) :=
  match origin.traceIndex? with
  | none => Registered.originalInstruction input (origin.event input) origin.item
  | some index =>
      match (show ProgrammeWorld.Row (ProgrammeSource.registrationSize input) from origin.item.1) with
      | .inherited => Registered.traceInstruction? input origin.visit.current index
      | .obstruction | .instruction _ => none

omit [DecidableEq Port] in
theorem instruction_mem (origin : InstructionOrigin input)
    (instruction : ExecutionItem Party Good Port Technology Instrument)
    (decoded : origin.instruction? input = some instruction) :
    instruction ∈ input.law.rawItems
      (ProgrammeSource.rawCurrent input origin.visit.current)
      (ProgrammeSource.rawEvent input origin.visit.current) := by
  unfold instruction? at decoded
  split at decoded
  · exact Registered.originalInstruction_mem input (origin.event input) origin.item instruction decoded
  · split at decoded
    · exact Registered.traceInstruction_mem input origin.visit.current _ instruction decoded
    · cases decoded
    · cases decoded

omit [DecidableEq Port] in
theorem participant_present (origin : InstructionOrigin input)
    (instruction : ExecutionItem Party Good Port Technology Instrument)
    (decoded : origin.instruction? input = some instruction) (party : Party)
    (participant : party ∈ operationParties instruction.request.operation) :
    ActualBirth.presentAt input origin.visit party := by
  change party ∈ parties input.law
    ⟨ProgrammeSource.rawCurrent input origin.visit.current, ProgrammeSource.rawEvent input origin.visit.current⟩
  unfold parties
  apply List.mem_dedup.mpr
  apply List.mem_flatMap.mpr
  exact ⟨instruction, origin.instruction_mem input instruction decoded,
    operation_party_mem_itemParties input.law instruction party participant⟩

def participantBirth (origin : InstructionOrigin input)
    (instruction : ExecutionItem Party Good Port Technology Instrument)
    (decoded : origin.instruction? input = some instruction) (party : Party)
    (participant : party ∈ operationParties instruction.request.operation) :
    ActualBirth.At input origin.visit party :=
  ActualBirth.generate input origin.visit party
    (origin.participant_present input instruction decoded party participant)

def row (origin : InstructionOrigin input) :
    OpenResponsibilityAt (ProgrammeSource.N input)
      (ProgrammeSource.supportAt input origin.visit.current) :=
  originalRow (origin.event input) origin.item

omit [DecidableEq Port] in
theorem exact_row (origin : InstructionOrigin input) : origin.row input = origin.item := rfl

def disposition (origin : InstructionOrigin input) :
    LedgerEntryDispositionAt (ProgrammeSource.N input) (origin.row input) :=
  ((ProgrammeSource.ledgerCompiler input).compile (origin.event input).val).entryDisposition origin.item

end InstructionOrigin

structure IssuedClaim where
  private mk ::
  origin : InstructionOrigin input
  instruction : ExecutionItem Party Good Port Technology Instrument
  instruction_exact : origin.instruction? input = some instruction
  instrument : Instrument
  debtor : Party
  holder : Party
  quantity : ℚ
  issue_exact : instruction.request.operation = .issue instrument debtor holder quantity
  accepted : input.law.Valid instruction.before instruction.request
  debtor_born : ActualBirth.At input origin.visit debtor
  holder_born : ActualBirth.At input origin.visit holder

namespace IssuedClaim

def debtorActor (claim : IssuedClaim input) : BirthActor input :=
  claim.debtor_born.actor input

def holderActor (claim : IssuedClaim input) : BirthActor input :=
  claim.holder_born.actor input

omit [DecidableEq Port] in
theorem debtor_is_actual_signer (claim : IssuedClaim input) :
    claim.instruction.request.signer = claim.debtor := by
  have signed := claim.accepted.1.1
  simpa only [RawLaw.SignerMatches, claim.issue_exact] using signed

omit [DecidableEq Port] in
theorem quantity_nonnegative (claim : IssuedClaim input) : 0 ≤ claim.quantity := by
  have guarded := claim.accepted.2.2.1
  simpa only [RawLaw.ClaimGuard, claim.issue_exact] using guarded

omit [DecidableEq Port] in
theorem original_inventory_provenance (claim : IssuedClaim input) :
    claim.instruction ∈ input.law.rawItems
      (ProgrammeSource.rawCurrent input claim.origin.visit.current)
      (ProgrammeSource.rawEvent input claim.origin.visit.current) :=
  claim.origin.instruction_mem input claim.instruction claim.instruction_exact

end IssuedClaim

inductive IssueReadout (origin : InstructionOrigin input)
  | issued (claim : IssuedClaim input) (origin_exact : claim.origin = origin)
  | nonfinancial
  | rejected (instruction : ExecutionItem Party Good Port Technology Instrument)
      (original : origin.instruction? input = some instruction)
      (refused : ¬ input.law.Valid instruction.before instruction.request)
  | missingBirth (party : Party) (notBorn : party ∉ bornParties input)

def readIssue (origin : InstructionOrigin input) : IssueReadout input origin :=
  match original : origin.instruction? input with
  | none => .nonfinancial
  | some instruction =>
      match operation : instruction.request.operation with
      | .issue instrument debtor holder quantity =>
          if accepted : input.law.Valid instruction.before instruction.request then
            .issued ⟨origin, instruction, original, instrument, debtor, holder, quantity,
              operation, accepted,
              origin.participantBirth input instruction original debtor (by
                rw [operation]; simp [operationParties]),
              origin.participantBirth input instruction original holder (by
                rw [operation]; simp [operationParties])⟩ rfl
          else .rejected instruction original accepted
      | .produce _ | .transfer _ _ _ | .use _ _ _ | .assign _ _ _ _ _ |
          .settle _ _ _ _ | .revise _ _ | .present => .nonfinancial

/- The sole instruction and validity decision for one actual origin. -/
namespace InstructionSource
inductive Decoded (origin : InstructionOrigin input) where
  | absent (original : origin.instruction? input = none)
  | refused (instruction : ExecutionItem Party Good Port Technology Instrument)
      (original : origin.instruction? input = some instruction)
      (refused : ¬ input.law.Valid instruction.before instruction.request)
  | accepted (instruction : ExecutionItem Party Good Port Technology Instrument)
      (original : origin.instruction? input = some instruction)
      (valid : input.law.Valid instruction.before instruction.request)
inductive Event where
  | originRead (present : Bool)
  | validity (accepted : Bool)
  | validityStep (event : RawLaw.ValiditySource.Event)
  deriving DecidableEq
private def produce (origin : InstructionOrigin input) : Decoded input origin × List Event :=
  match original : origin.instruction? input with
  | none => ⟨.absent original,[.originRead false]⟩
  | some instruction =>
      let checked := RawLaw.ValiditySource.compile input.law instruction.before instruction.request
      let work := [.originRead true]++checked.work.map Event.validityStep
      if accepted : checked.accepted = true then
        ⟨.accepted instruction original (checked.exact.mp accepted),work++[.validity true]⟩
      else ⟨.refused instruction original (fun valid => accepted (checked.exact.mpr valid)),work++[.validity false]⟩
def budget (origin : InstructionOrigin input) : Nat :=
  match origin.instruction? input with
  | none => 1
  | some instruction => RawLaw.ValiditySource.budget input.law instruction.before instruction.request+2
structure Compilation (origin : InstructionOrigin input) where
  private mk ::
  decoded : Decoded input origin
  work : List Event
  private generated : decoded = (produce input origin).1 ∧ work = (produce input origin).2

def compile (origin : InstructionOrigin input) : Compilation input origin :=
  let made := produce input origin
  ⟨made.1,made.2,⟨rfl,rfl⟩⟩
omit [DecidableEq Port] in
theorem work_bound (origin : InstructionOrigin input) :
    (compile input origin).work.length ≤ budget input origin := by
  change (produce input origin).2.length ≤ budget input origin
  unfold produce budget
  split
  · rename_i absent
    simp [absent]
  · rename_i instruction original
    simp only [original]
    have checked := RawLaw.ValiditySource.work_bound input.law instruction.before instruction.request
    split <;> simp only [List.length_append,List.length_cons,List.length_nil,List.length_map] <;> omega
end InstructionSource

namespace IssueSource
inductive Event where
  | cached (status : Fin 3)
  | operation (issue : Bool)
  | birth (holder : Bool)
  | assemble
  deriving DecidableEq
private def produce {origin : InstructionOrigin input} (source : InstructionSource.Compilation input origin) :
    IssueReadout input origin × List Event :=
  match source.decoded with
  | .absent _ => ⟨.nonfinancial,[.cached 0]⟩
  | .refused instruction original refused =>
      match instruction.request.operation with
      | .issue _ _ _ _ => ⟨.rejected instruction original refused,[.cached 1,.operation true]⟩
      | .produce _ | .transfer _ _ _ | .use _ _ _ | .assign _ _ _ _ _ |
          .settle _ _ _ _ | .revise _ _ | .present => ⟨.nonfinancial,[.cached 1,.operation false]⟩
  | .accepted instruction original valid =>
      match operation : instruction.request.operation with
      | .issue instrument debtor holder quantity =>
          ⟨.issued ⟨origin,instruction,original,instrument,debtor,holder,quantity,operation,valid,
            origin.participantBirth input instruction original debtor (by rw [operation]; simp [operationParties]),
            origin.participantBirth input instruction original holder (by rw [operation]; simp [operationParties])⟩ rfl,
            [.cached 2,.operation true,.birth false,.birth true,.assemble]⟩
      | .produce _ | .transfer _ _ _ | .use _ _ _ | .assign _ _ _ _ _ |
          .settle _ _ _ _ | .revise _ _ | .present => ⟨.nonfinancial,[.cached 2,.operation false]⟩
omit [DecidableEq Port] in
private theorem produce_exact {origin : InstructionOrigin input} (source : InstructionSource.Compilation input origin) :
    (produce input source).1 = readIssue input origin := by
  cases decoded : source.decoded <;> unfold produce readIssue <;> rw [decoded]
  all_goals
    dsimp only
    repeat' first | split | (solve | rfl | simp_all | grind)

omit [DecidableEq Port] in
private theorem produce_work {origin : InstructionOrigin input} (source : InstructionSource.Compilation input origin) :
    (produce input source).2.length ≤ 5 := by
  unfold produce
  split
  · simp
  · split <;> simp
  · split <;> simp
structure Compilation {origin : InstructionOrigin input} (source : InstructionSource.Compilation input origin) where
  private mk ::
  result : IssueReadout input origin
  work : List Event
  exact : result = readIssue input origin
  private generated : result = (produce input source).1 ∧ work = (produce input source).2

def compileFrom {origin : InstructionOrigin input} (source : InstructionSource.Compilation input origin) : Compilation input source :=
  let made := produce input source
  ⟨made.1,made.2,produce_exact input source,⟨rfl,rfl⟩⟩
omit [DecidableEq Port] in
theorem work_bound {origin : InstructionOrigin input} (source : InstructionSource.Compilation input origin) :
    (compileFrom input source).work.length ≤ 5 := produce_work input source
end IssueSource

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial
