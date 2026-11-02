import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Coupling
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Prefix
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.InventoryExact

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Coupling.Causality

open Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def birthHistoryImage (ordinal : Nat) (party : Party) :=
  (ProgrammeFace.ActualBirth.lookup input (ProgrammeHistory.visitAt input ordinal) party).map
    (Identity.birthImage code input)

def birthHereImage (ordinal : Nat) (party : Party) :
    Option (Identity.BirthImage Party Good Port Technology Instrument) :=
  if ProgrammeFace.ActualBirth.presentAt input (ProgrammeHistory.visitAt input ordinal) party then
    some ⟨Identity.occurrenceImage code input (ProgrammeHistory.visitAt input ordinal).current, party⟩
  else none

omit [DecidableEq Port] [DecidableEq Technology] in
theorem birthHistoryImage_zero (party : Party) :
    birthHistoryImage code input 0 party = birthHereImage code input 0 party := by
  exact ProgrammeFace.ActualBirth.lookup_map_initial input
    (fun current key => (⟨Identity.occurrenceImage code input current, key⟩ : Identity.BirthImage Party Good Port Technology Instrument)) party

omit [DecidableEq Port] [DecidableEq Technology] in
theorem birthHistoryImage_succ (ordinal : Nat) (party : Party) :
    birthHistoryImage code input (ordinal + 1) party =
      (birthHistoryImage code input ordinal party).orElse
        (fun _ => birthHereImage code input (ordinal + 1) party) := by
  exact ProgrammeFace.ActualBirth.lookup_map_next input
    (fun current key => (⟨Identity.occurrenceImage code input current, key⟩ : Identity.BirthImage Party Good Port Technology Instrument))
    (ProgrammeHistory.visitAt input ordinal) rfl party

def issuedImage (origin : Financial.InstructionOrigin input) :=
  (Financial.issuedClaim? input origin).map (Identity.claimImage code input)

def canonicalIssueImage (origin : Identity.OriginImage Party Good Port Technology Instrument)
    (instruction : Option (Program.ExecutionItem Party Good Port Technology Instrument))
    (birth : Party → Option (Identity.BirthImage Party Good Port Technology Instrument)) :=
  instruction.bind fun item =>
    match item.request.operation with
    | .issue instrument debtor holder quantity =>
        if input.law.Valid item.before item.request then
          (birth debtor).bind fun debtorBirth =>
            (birth holder).bind fun holderBirth =>
              some (⟨origin, item.index, Identity.snapshot code item.before, item.request,
                instrument, debtor, holder, quantity, debtorBirth, holderBirth⟩ : Identity.ClaimImage Party Good Port Technology Instrument)
        else none
    | _ => none

omit [DecidableEq Port] [DecidableEq Technology] in
theorem canonical_issue_image_congr
    (other : ProgrammeSource.Input Party Good Port Technology Instrument) (law : other.law = input.law)
    (oldOrigin newOrigin : Identity.OriginImage Party Good Port Technology Instrument)
    (oldInstruction newInstruction : Option (Program.ExecutionItem Party Good Port Technology Instrument))
    (oldBirth newBirth : Party → Option (Identity.BirthImage Party Good Port Technology Instrument))
    (origins : newOrigin = oldOrigin) (decoded : newInstruction = oldInstruction) (births : newBirth = oldBirth) :
    canonicalIssueImage code other newOrigin newInstruction newBirth =
      canonicalIssueImage code input oldOrigin oldInstruction oldBirth := by
  unfold canonicalIssueImage
  rw [law, origins, decoded, births]

omit [DecidableEq Port] [DecidableEq Technology] in
theorem issued_image_is_canonical (ordinal : Nat) (origin : Financial.InstructionOrigin input)
    (actual : origin.visit = ProgrammeHistory.visitAt input ordinal) :
    issuedImage code input origin = canonicalIssueImage code input (Identity.originImage code input origin)
      (origin.instruction? input) (birthHistoryImage code input ordinal) := by
  unfold issuedImage Financial.issuedClaim?
  generalize produced : Financial.readIssue input origin = result
  unfold Financial.readIssue at produced
  split at produced
  next absent =>
    cases produced
    simp only [Option.map_none, canonicalIssueImage, absent, Option.bind_none]
  next item decoded =>
    split at produced
    next instrument debtor holder quantity operation =>
      split at produced
      next accepted =>
        cases produced
        let debtorBirth := origin.participantBirth input item decoded debtor (by
          rw [operation]; simp [ProgrammeFace.operationParties])
        let holderBirth := origin.participantBirth input item decoded holder (by
          rw [operation]; simp [ProgrammeFace.operationParties])
        have bornDebtor : birthHistoryImage code input ordinal debtor =
            some (Identity.birthImage code input debtorBirth.original) := by
          unfold birthHistoryImage
          rw [← actual, debtorBirth.generated]
          rfl
        have bornHolder : birthHistoryImage code input ordinal holder =
            some (Identity.birthImage code input holderBirth.original) := by
          unfold birthHistoryImage
          rw [← actual, holderBirth.generated]
          rfl
        simp only [Option.map_some, canonicalIssueImage, decoded, Option.bind_some,
          operation, if_pos accepted, bornDebtor, bornHolder]
        rfl
      next refused =>
        cases produced
        simp only [Option.map_none, canonicalIssueImage, decoded, Option.bind_some,
          operation, if_neg refused]
    all_goals
      cases produced
      simp only [Option.map_none, canonicalIssueImage, Option.bind_some, *]

omit [DecidableEq Port] [DecidableEq Technology] in
theorem issued_image_absent (origin : Financial.InstructionOrigin input)
    (absent : origin.instruction? input = none) : issuedImage code input origin = none := by
  unfold issuedImage Financial.issuedClaim?
  rw [Financial.BalanceConservation.issue_readout_absent input origin absent]
  rfl

omit [DecidableEq Port] [DecidableEq Technology] in
theorem administrative_issues_empty
    (visit : RootVisit (ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot)
    (emit : Program.RawCurrent Party Good Technology Instrument → Program.RawEvent Party Good Port Technology Instrument)
    (generated : input.emission? = some emit) :
    (Financial.administrativeInventoryAt input visit).filterMap (issuedImage code input) = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro origin member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  apply issued_image_absent code input
  exact ProgrammeFace.Registered.originalInstruction_generated_none input
    ((Financial.originAt input visit index).event input) (Financial.originAt input visit index).item emit generated

omit [DecidableEq Port] [DecidableEq Technology] in
theorem issued_images_are_native (origins : List (Financial.InstructionOrigin input)) :
    (Financial.issuedClaims input origins).map (Identity.claimImage code input) =
      origins.filterMap (issuedImage code input) := by
  simp only [Financial.issuedClaims, List.map_filterMap]
  rfl

variable (source : Machine Party Good Port Technology Instrument) (cut : Nat) (policy : source.code.Policy)

theorem prior_occurrence_image (ordinal : Nat) (bounded : ordinal < source.history.length + 2 + cut) :
    Identity.occurrenceImage source.code (source.atFeedbackCut cut policy).input
        (ProgrammeHistory.visitAt (source.atFeedbackCut cut policy).input ordinal).current =
      Identity.occurrenceImage source.code source.input (ProgrammeHistory.visitAt source.input ordinal).current := by
  have same := source.scheduled_policy_keeps_every_prior_occurrence cut policy ordinal bounded
  exact congrArg₂ Identity.OccurrenceImage.mk (congrArg (Identity.visitImage source.code) same.1) same.2

theorem prior_participation (ordinal : Nat) (bounded : ordinal < source.history.length + 2 + cut) (party : Party) :
    ProgrammeFace.ActualBirth.presentAt (source.atFeedbackCut cut policy).input
        (ProgrammeHistory.visitAt (source.atFeedbackCut cut policy).input ordinal) party =
      ProgrammeFace.ActualBirth.presentAt source.input (ProgrammeHistory.visitAt source.input ordinal) party := by
  have same := source.scheduled_policy_keeps_every_prior_occurrence cut policy ordinal bounded
  change (party ∈ ProgrammeFace.parties source.code.law
      (ProgrammeSource.rawCurrent (source.atFeedbackCut cut policy).input
        (ProgrammeHistory.visitAt (source.atFeedbackCut cut policy).input ordinal).current,
        ProgrammeSource.rawEvent (source.atFeedbackCut cut policy).input
          (ProgrammeHistory.visitAt (source.atFeedbackCut cut policy).input ordinal).current)) = _
  exact congrArg (fun event => party ∈ ProgrammeFace.parties source.code.law event)
    (congrArg₂ Prod.mk (congrArg (ProgrammeSource.rawCurrent source.input) same.1) same.2)

theorem prior_birth_here (ordinal : Nat) (bounded : ordinal < source.history.length + 2 + cut) (party : Party) :
    birthHereImage source.code (source.atFeedbackCut cut policy).input ordinal party =
      birthHereImage source.code source.input ordinal party := by
  unfold birthHereImage
  simp only [prior_participation source cut policy ordinal bounded party,
    prior_occurrence_image source cut policy ordinal bounded]

theorem prior_first_birth (ordinal : Nat) (bounded : ordinal < source.history.length + 2 + cut) (party : Party) :
    birthHistoryImage source.code (source.atFeedbackCut cut policy).input ordinal party =
      birthHistoryImage source.code source.input ordinal party := by
  induction ordinal with
  | zero =>
      rw [birthHistoryImage_zero, birthHistoryImage_zero]
      exact prior_birth_here source cut policy 0 bounded party
  | succ ordinal ih =>
      rw [birthHistoryImage_succ, birthHistoryImage_succ, ih (by omega),
        prior_birth_here source cut policy (ordinal + 1) bounded party]

private theorem list_get_congr {α : Type} (first second : List α) (same : second = first)
    (old : Fin first.length) (new : Fin second.length) (index : new.val = old.val) :
    second.get new = first.get old := by
  subst second
  have sameIndex : new = old := Fin.ext index
  cases sameIndex
  rfl

def partnerTraceIndex (ordinal : Nat) (bounded : ordinal < source.history.length + 2 + cut)
    (index : Fin (ProgrammeFace.Registered.traceItems source.input
      (ProgrammeHistory.visitAt source.input ordinal).current).length) :
    Fin (ProgrammeFace.Registered.traceItems (source.atFeedbackCut cut policy).input
      (ProgrammeHistory.visitAt (source.atFeedbackCut cut policy).input ordinal).current).length :=
  ⟨index.val, by
    rw [source.scheduled_policy_keeps_every_prior_instruction_trace cut policy ordinal bounded]
    exact index.isLt⟩

theorem prior_trace_origin_image (ordinal : Nat) (bounded : ordinal < source.history.length + 2 + cut)
    (index : Fin (ProgrammeFace.Registered.traceItems source.input
      (ProgrammeHistory.visitAt source.input ordinal).current).length) :
    Identity.originImage source.code (source.atFeedbackCut cut policy).input
        (Financial.traceOriginAt (source.atFeedbackCut cut policy).input
          (ProgrammeHistory.visitAt (source.atFeedbackCut cut policy).input ordinal)
          (partnerTraceIndex source cut policy ordinal bounded index)) =
      Identity.originImage source.code source.input
        (Financial.traceOriginAt source.input (ProgrammeHistory.visitAt source.input ordinal) index) := by
  simp only [Identity.originImage, Financial.traceOriginAt,
    ProgrammeFace.Registered.traceRow_is_original_interpreter]
  change Identity.OriginImage.mk _ 0 (some index.val) = Identity.OriginImage.mk _ 0 (some index.val)
  rw [prior_occurrence_image source cut policy ordinal bounded]

theorem prior_trace_origin_decodes_the_same_instruction (ordinal : Nat)
    (bounded : ordinal < source.history.length + 2 + cut)
    (index : Fin (ProgrammeFace.Registered.traceItems source.input
      (ProgrammeHistory.visitAt source.input ordinal).current).length) :
    (Financial.traceOriginAt (source.atFeedbackCut cut policy).input
        (ProgrammeHistory.visitAt (source.atFeedbackCut cut policy).input ordinal)
        (partnerTraceIndex source cut policy ordinal bounded index)).instruction? (source.atFeedbackCut cut policy).input =
      (Financial.traceOriginAt source.input (ProgrammeHistory.visitAt source.input ordinal) index).instruction? source.input := by
  exact (Financial.traceOriginAt_instruction (source.atFeedbackCut cut policy).input _
      (partnerTraceIndex source cut policy ordinal bounded index)).trans
    ((congrArg some (list_get_congr _ _
      (source.scheduled_policy_keeps_every_prior_instruction_trace cut policy ordinal bounded)
      index (partnerTraceIndex source cut policy ordinal bounded index) rfl)).trans
      (Financial.traceOriginAt_instruction source.input _ index).symm)

theorem prior_trace_issue_image (ordinal : Nat) (bounded : ordinal < source.history.length + 2 + cut)
    (index : Fin (ProgrammeFace.Registered.traceItems source.input
      (ProgrammeHistory.visitAt source.input ordinal).current).length) :
    issuedImage source.code (source.atFeedbackCut cut policy).input
        (Financial.traceOriginAt (source.atFeedbackCut cut policy).input
          (ProgrammeHistory.visitAt (source.atFeedbackCut cut policy).input ordinal)
          (partnerTraceIndex source cut policy ordinal bounded index)) =
      issuedImage source.code source.input
        (Financial.traceOriginAt source.input (ProgrammeHistory.visitAt source.input ordinal) index) := by
  exact (issued_image_is_canonical source.code (source.atFeedbackCut cut policy).input ordinal _ rfl).trans
    ((canonical_issue_image_congr source.code source.input (source.atFeedbackCut cut policy).input rfl _ _ _ _ _ _
      (prior_trace_origin_image source cut policy ordinal bounded index)
      (prior_trace_origin_decodes_the_same_instruction source cut policy ordinal bounded index)
      (funext (prior_first_birth source cut policy ordinal bounded))).trans
      (issued_image_is_canonical source.code source.input ordinal _ rfl).symm)

theorem prior_trace_issue_images (ordinal : Nat) (bounded : ordinal < source.history.length + 2 + cut) :
    (Financial.traceInventoryAt (source.atFeedbackCut cut policy).input
        (ProgrammeHistory.visitAt (source.atFeedbackCut cut policy).input ordinal)).map
        (issuedImage source.code (source.atFeedbackCut cut policy).input) =
      (Financial.traceInventoryAt source.input (ProgrammeHistory.visitAt source.input ordinal)).map
        (issuedImage source.code source.input) := by
  simp only [Financial.traceInventoryAt, List.map_ofFn]
  apply List.ext_getElem
  · simp only [List.length_ofFn]
    exact congrArg List.length (source.scheduled_policy_keeps_every_prior_instruction_trace cut policy ordinal bounded)
  · intro index newBound oldBound
    simp only [List.getElem_ofFn]
    exact prior_trace_issue_image source cut policy ordinal bounded ⟨index, by simpa using oldBound⟩

theorem prior_native_issue_inventory (ordinal : Nat) (bounded : ordinal < source.history.length + 2 + cut) :
    (Financial.issuedClaims (source.atFeedbackCut cut policy).input
        (Financial.inventoryAt (source.atFeedbackCut cut policy).input
          (ProgrammeHistory.visitAt (source.atFeedbackCut cut policy).input ordinal))).map
        (Identity.claimImage source.code (source.atFeedbackCut cut policy).input) =
      (Financial.issuedClaims source.input
        (Financial.inventoryAt source.input (ProgrammeHistory.visitAt source.input ordinal))).map
        (Identity.claimImage source.code source.input) := by
  rw [issued_images_are_native, issued_images_are_native]
  change ((Financial.administrativeInventoryAt (source.atFeedbackCut cut policy).input _ ++
      Financial.traceInventoryAt (source.atFeedbackCut cut policy).input _).filterMap _) =
    ((Financial.administrativeInventoryAt source.input _ ++ Financial.traceInventoryAt source.input _).filterMap _)
  rw [List.filterMap_append, List.filterMap_append,
    administrative_issues_empty source.code (source.atFeedbackCut cut policy).input _ _ rfl,
    administrative_issues_empty source.code source.input _ _ rfl,
    List.nil_append, List.nil_append]
  have images := congrArg (List.filterMap id) (prior_trace_issue_images source cut policy ordinal bounded)
  simpa only [List.filterMap_map, Function.comp_def, id_eq] using images

theorem prior_issued_before (ordinal : Nat) (bounded : ordinal ≤ source.history.length + 2 + cut) :
    (Financial.issuedBefore (source.atFeedbackCut cut policy).input ordinal).map
        (Identity.claimImage source.code (source.atFeedbackCut cut policy).input) =
      (Financial.issuedBefore source.input ordinal).map (Identity.claimImage source.code source.input) := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
      rw [Financial.issuedBefore, Financial.issuedBefore, List.map_append, List.map_append,
        ih (by omega), prior_native_issue_inventory source cut policy ordinal (by omega)]

theorem every_prior_original_claim_keeps_its_actual_source (ordinal : Nat)
    (bounded : ordinal ≤ source.history.length + 2 + cut) :
    ((Financial.accountAt (source.atFeedbackCut cut policy).input ordinal).current.slots.map
        (Financial.slotClaim (source.atFeedbackCut cut policy).input)).map
        (Identity.claimImage source.code (source.atFeedbackCut cut policy).input) =
      ((Financial.accountAt source.input ordinal).current.slots.map (Financial.slotClaim source.input)).map
        (Identity.claimImage source.code source.input) := by
  rw [Financial.account_claims_are_exactly_the_source_issues,
    Financial.account_claims_are_exactly_the_source_issues]
  exact prior_issued_before source cut policy ordinal bounded

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Coupling.Causality
