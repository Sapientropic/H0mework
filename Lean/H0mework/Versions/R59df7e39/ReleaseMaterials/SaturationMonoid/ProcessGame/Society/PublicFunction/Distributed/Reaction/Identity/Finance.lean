import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Identity.Snapshot

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Identity

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

structure OccurrenceImage (Party Good Port Technology Instrument : Type) where
  visit : VisitImage Technology
  word : RawEvent Party Good Port Technology Instrument
  deriving DecidableEq

structure OriginImage (Party Good Port Technology Instrument : Type) where
  occurrence : OccurrenceImage Party Good Port Technology Instrument
  row : Nat
  traceIndex : Option Nat
  deriving DecidableEq

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def occurrenceImage (current : (ProgrammeSource.V input).Current) : OccurrenceImage Party Good Port Technology Instrument :=
  ⟨visitImage code current, ProgrammeSource.rawEvent input current⟩

def originImage (origin : Financial.InstructionOrigin input) : OriginImage Party Good Port Technology Instrument :=
  ⟨occurrenceImage code input origin.visit.current,
    match (show ProgrammeWorld.Row (ProgrammeSource.registrationSize input) from origin.item.1) with
    | .inherited => 0 | .obstruction => 1 | .instruction index => index.val + 2,
    origin.traceIndex?⟩

structure BirthImage (Party Good Port Technology Instrument : Type) where
  occurrence : OccurrenceImage Party Good Port Technology Instrument
  party : Party
  deriving DecidableEq

def birthImage (witness : Institutions.Capitalism.Universal.Source.ProgrammeFace.ActualBirth.Witness input) :
    BirthImage Party Good Port Technology Instrument :=
  ⟨occurrenceImage code input witness.visit.current, witness.party⟩

structure ActorImage (Party Good Port Technology Instrument : Type) where
  occurrence : OccurrenceImage Party Good Port Technology Instrument
  lineage : List Party
  deriving DecidableEq

def actorImage (actor : Financial.BirthActor input) : ActorImage Party Good Port Technology Instrument :=
  ⟨occurrenceImage code input actor.1.current, actor.2.val⟩

structure ClaimImage (Party Good Port Technology Instrument : Type) where
  origin : OriginImage Party Good Port Technology Instrument
  index : Nat
  before : Snapshot Technology
  request : Request Party Good Port Technology Instrument
  instrument : Instrument
  debtor : Party
  holder : Party
  quantity : ℚ
  debtorBirth : BirthImage Party Good Port Technology Instrument
  holderBirth : BirthImage Party Good Port Technology Instrument
  deriving DecidableEq

def claimImage (claim : Financial.IssuedClaim input) : ClaimImage Party Good Port Technology Instrument :=
  ⟨originImage code input claim.origin, claim.instruction.index, snapshot code claim.instruction.before,
    claim.instruction.request, claim.instrument, claim.debtor, claim.holder, claim.quantity,
    birthImage code input claim.debtor_born.original, birthImage code input claim.holder_born.original⟩

inductive EventImage (Party Good Port Technology Instrument : Type) where
  | birth (claim : ClaimImage Party Good Port Technology Instrument)
  | review (claim : ClaimImage Party Good Port Technology Instrument)
      (origin : OriginImage Party Good Port Technology Instrument) (index : Nat) (before : Snapshot Technology)
      (request : Request Party Good Port Technology Instrument) (sender recipient : Party)
      (quantity : ℚ) (balance : Party →₀ ℚ) (remaining : ℚ)
  deriving DecidableEq

def eventImage : Financial.Event input → EventImage Party Good Port Technology Instrument
  | .birth claim => .birth (claimImage code input claim)
  | .review claim receipt balance remaining => .review (claimImage code input claim)
      (originImage code input receipt.origin) receipt.instruction.index (snapshot code receipt.instruction.before)
      receipt.instruction.request (receipt.fromHolder input) (receipt.toHolder input) receipt.quantity balance remaining

structure DebtImage (Party Good Port Technology Instrument : Type) where
  claim : ClaimImage Party Good Port Technology Instrument
  beneficiary : ClaimImage Party Good Port Technology Instrument
  bearer : ActorImage Party Good Port Technology Instrument
  scope : OriginImage Party Good Port Technology Instrument
  admission : EventImage Party Good Port Technology Instrument
  admittedBearer : ActorImage Party Good Port Technology Instrument
  admittedScope : OriginImage Party Good Port Technology Instrument
  lineage : OriginImage Party Good Port Technology Instrument
  residual : Party →₀ ℚ
  balance : Party →₀ ℚ
  archive : Option (EventImage Party Good Port Technology Instrument)
  deriving DecidableEq

def debtImage (slot : ObligationSlot (Financial.vocabulary input)) : DebtImage Party Good Port Technology Instrument :=
  let obligation := Financial.slotObligation input slot
  ⟨claimImage code input obligation.content, claimImage code input obligation.beneficiary,
    actorImage code input obligation.bearer, originImage code input obligation.scope,
    eventImage code input obligation.admission.sourceEvent, actorImage code input obligation.admission.admittedBearer,
    originImage code input obligation.admission.admittedScope, originImage code input obligation.admission.lineage,
    obligation.residual, Financial.slotBalance input slot,
    match slot with | .live _ => none | .terminal archive => some (eventImage code input archive.sourceEvent)⟩

def financeImage (state : (Financial.process input).GeneratedState) :=
  state.current.slots.map (debtImage code input)

/-- Both endpoints remain the actual native slots of their own roots. The
finite equality is a comparison, never an identification of the roots. -/
structure DebtCorrespondence (other : ProgrammeSource.Input Party Good Port Technology Instrument)
    (old : ObligationSlot (Financial.vocabulary input)) (new : ObligationSlot (Financial.vocabulary other)) : Prop where
  image : debtImage code other new = debtImage code input old

omit [DecidableEq Technology] in
theorem equal_images_recover_each_original_native_debt
    (other : ProgrammeSource.Input Party Good Port Technology Instrument)
    (old : (Financial.process input).GeneratedState) (new : (Financial.process other).GeneratedState)
    (same : financeImage code other new = financeImage code input old) :
    ∀ index (inside : index < old.current.slots.length),
      ∃ replacement ∈ new.current.slots,
        DebtCorrespondence code input other old.current.slots[index] replacement := by
  intro index inside
  have lengths := congrArg List.length same
  simp only [financeImage, List.length_map] at lengths
  have bounded : index < new.current.slots.length := by omega
  refine ⟨new.current.slots[index], List.getElem_mem bounded, ?_⟩
  constructor
  have row := congrArg (fun rows => rows[index]?) same
  change (new.current.slots.map (debtImage code other))[index]? =
    (old.current.slots.map (debtImage code input))[index]? at row
  rw [List.getElem?_map, List.getElem?_map,
    List.getElem?_eq_getElem bounded, List.getElem?_eq_getElem inside] at row
  exact Option.some.inj row

omit [DecidableEq Technology] in
theorem correspondence_keeps_contract_shares_and_archive
    (other : ProgrammeSource.Input Party Good Port Technology Instrument)
    (old : ObligationSlot (Financial.vocabulary input)) (new : ObligationSlot (Financial.vocabulary other))
    (matched : DebtCorrespondence code input other old new) :
    claimImage code other (Financial.slotClaim other new) = claimImage code input (Financial.slotClaim input old) ∧
      Financial.slotBalance other new = Financial.slotBalance input old ∧
      (debtImage code other new).admission = (debtImage code input old).admission ∧
      (debtImage code other new).archive = (debtImage code input old).archive :=
  ⟨congrArg DebtImage.claim matched.image, congrArg DebtImage.balance matched.image,
    congrArg DebtImage.admission matched.image, congrArg DebtImage.archive matched.image⟩

omit [DecidableEq Technology] in
theorem correspondence_recovers_the_complete_issued_occurrence
    (other : ProgrammeSource.Input Party Good Port Technology Instrument)
    (old : ObligationSlot (Financial.vocabulary input)) (new : ObligationSlot (Financial.vocabulary other))
    (matched : DebtCorrespondence code input other old new) :
    let oldClaim := Financial.slotClaim input old
    let newClaim := Financial.slotClaim other new
    newClaim.origin.visit.current = oldClaim.origin.visit.current ∧
      ProgrammeSource.rawEvent other newClaim.origin.visit.current = ProgrammeSource.rawEvent input oldClaim.origin.visit.current ∧
      newClaim.instruction = oldClaim.instruction := by
  have claims := congrArg DebtImage.claim matched.image
  have origins := congrArg ClaimImage.origin claims
  have occurrences := congrArg OriginImage.occurrence origins
  refine ⟨visitImage_injective code (congrArg OccurrenceImage.visit occurrences),
    congrArg OccurrenceImage.word occurrences, ?_⟩
  have index := congrArg ClaimImage.index claims
  have before := snapshot_injective code (congrArg ClaimImage.before claims)
  have request := congrArg ClaimImage.request claims
  change (Financial.slotClaim other new).instruction.index = (Financial.slotClaim input old).instruction.index at index
  change (Financial.slotClaim other new).instruction.before = (Financial.slotClaim input old).instruction.before at before
  change (Financial.slotClaim other new).instruction.request = (Financial.slotClaim input old).instruction.request at request
  change ExecutionItem.mk _ _ _ = ExecutionItem.mk _ _ _
  rw [index, before, request]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Identity
