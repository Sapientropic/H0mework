import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Causality

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Coupling.State

open Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

structure ReviewData (Party Good Port Technology Instrument : Type) where
  instruction : ExecutionItem Party Good Port Technology Instrument
  assignment : Bool
  sender : Party
  recipient : Party
  quantity : ℚ

def reviewData {claim : Financial.IssuedClaim input} (review : Financial.Review input claim) :
    ReviewData Party Good Port Technology Instrument :=
  ⟨review.instruction, match review.kind with | .payment _ => false | .assignment .. => true,
    review.fromHolder input, review.toHolder input, review.quantity⟩

def canonicalReviewData (instrument : Instrument) (debtor : Party)
    (decoded : Option (ExecutionItem Party Good Port Technology Instrument)) :
    Option (ReviewData Party Good Port Technology Instrument) :=
  decoded.bind fun item =>
    if input.law.Valid item.before item.request then
      match item.request.operation with
      | .settle i d h q => if i = instrument ∧ d = debtor then some ⟨item, false, h, h, q⟩ else none
      | .assign i d s r q => if i = instrument ∧ d = debtor then some ⟨item, true, s, r, q⟩ else none
      | _ => none
    else none

omit [DecidableEq Port] [DecidableEq Technology] in
theorem review_data_is_canonical (claim : Financial.IssuedClaim input) (origin : Financial.InstructionOrigin input) :
    (Financial.readReview input claim origin).map (reviewData input) =
      canonicalReviewData input claim.instrument claim.debtor (origin.instruction? input) := by
  generalize produced : Financial.readReview input claim origin = result
  unfold Financial.readReview at produced
  split at produced
  next absent =>
    cases produced
    simp only [canonicalReviewData, absent, Option.bind_none, Option.map_none]
  next item decoded =>
    split at produced
    next accepted =>
      split at produced
      all_goals
        repeat' first
          | (split at produced)
          | (cases produced; simp_all only [canonicalReviewData, Option.bind_some, Option.map_some,
              Option.map_none, reviewData, Financial.Review.fromHolder, Financial.Review.toHolder,
              Financial.holderIndex, ↓reduceIte, and_self, true_and, false_and])
    next refused =>
      cases produced
      simp only [canonicalReviewData, decoded, Option.bind_some, if_neg refused, Option.map_none]

omit [DecidableEq Port] [DecidableEq Technology] in
theorem canonical_review_congr
    (other : ProgrammeSource.Input Party Good Port Technology Instrument) (law : other.law = input.law)
    (oldInstrument newInstrument : Instrument) (oldDebtor newDebtor : Party)
    (oldDecoded newDecoded : Option (ExecutionItem Party Good Port Technology Instrument))
    (instrument : newInstrument = oldInstrument) (debtor : newDebtor = oldDebtor) (decoded : newDecoded = oldDecoded) :
    canonicalReviewData other newInstrument newDebtor newDecoded =
      canonicalReviewData input oldInstrument oldDebtor oldDecoded := by
  unfold canonicalReviewData
  rw [law, instrument, debtor, decoded]

omit [DecidableEq Port] [DecidableEq Technology] in
theorem read_review_natural
    (other : ProgrammeSource.Input Party Good Port Technology Instrument) (law : other.law = input.law)
    (oldClaim : Financial.IssuedClaim input) (newClaim : Financial.IssuedClaim other)
    (oldOrigin : Financial.InstructionOrigin input) (newOrigin : Financial.InstructionOrigin other)
    (instrument : newClaim.instrument = oldClaim.instrument) (debtor : newClaim.debtor = oldClaim.debtor)
    (decoded : newOrigin.instruction? other = oldOrigin.instruction? input) :
    (Financial.readReview other newClaim newOrigin).map (reviewData other) =
      (Financial.readReview input oldClaim oldOrigin).map (reviewData input) :=
  (review_data_is_canonical other newClaim newOrigin).trans
    ((canonical_review_congr input other law _ _ _ _ _ _ instrument debtor decoded).trans
      (review_data_is_canonical input oldClaim oldOrigin).symm)

def afterData (data : ReviewData Party Good Port Technology Instrument) (balance : Party →₀ ℚ) (cap : ℚ) : Party →₀ ℚ :=
  let used := min cap (balance data.sender)
  if data.assignment then Financial.assign input balance data.sender data.recipient used
  else Financial.pay input balance data.sender used

omit [DecidableEq Port] [DecidableEq Technology] in
theorem review_after_is_canonical {claim : Financial.IssuedClaim input}
    (review : Financial.Review input claim) (balance : Financial.Balance input) (cap : ℚ) :
    review.after input balance cap = afterData input (reviewData input review) balance cap := by
  cases kind : review.kind <;>
    simp only [Financial.Review.after, Financial.Review.allocated, reviewData, Financial.Review.fromHolder,
      Financial.Review.toHolder, afterData, kind, Bool.false_eq_true, ↓reduceIte]

omit [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
theorem after_data_input_independent (other : ProgrammeSource.Input Party Good Port Technology Instrument)
    (data : ReviewData Party Good Port Technology Instrument) (balance : Party →₀ ℚ) (cap : ℚ) :
    afterData other data balance cap = afterData input data balance cap := rfl

def eventFromData (claim : Identity.ClaimImage Party Good Port Technology Instrument)
    (origin : Identity.OriginImage Party Good Port Technology Instrument)
    (data : ReviewData Party Good Port Technology Instrument) (balance : Party →₀ ℚ) (cap : ℚ) :=
  Identity.EventImage.review claim origin data.instruction.index (Identity.snapshot code data.instruction.before)
    data.instruction.request data.sender data.recipient data.quantity balance cap

omit [DecidableEq Port] [DecidableEq Technology] in
theorem review_event_is_canonical {claim : Financial.IssuedClaim input}
    (review : Financial.Review input claim) (balance : Party →₀ ℚ) (cap : ℚ) :
    Identity.eventImage code input (.review claim review balance cap) =
      eventFromData code (Identity.claimImage code input claim) (Identity.originImage code input review.origin)
        (reviewData input review) balance cap := by
  cases kind : review.kind <;> rfl

def nextDebt (old : Identity.DebtImage Party Good Port Technology Instrument)
    (source : Identity.EventImage Party Good Port Technology Instrument) (after : Party →₀ ℚ) :=
  if after = 0 then {old with balance := 0, archive := some source}
  else {old with residual := after, balance := after, archive := none}

def nextRecord (index : Nat) (old : Identity.DebtImage Party Good Port Technology Instrument)
    (source : Identity.EventImage Party Good Port Technology Instrument) (after : Party →₀ ℚ) :
    RecordImage Party Good Port Technology Instrument :=
  ⟨index, if after = 0 then .obligationTerminal else .progressed, some old,
    nextDebt old source after, source⟩

omit [DecidableEq Technology] in
theorem boundary_target_image {obligation : AdmittedObligation (Financial.vocabulary input)}
    (boundary : Financial.Boundary input obligation) :
    Identity.debtImage code input (Financial.boundaryDisposition input boundary).targetSlot =
      nextDebt (Identity.debtImage code input (.live obligation)) (Identity.eventImage code input boundary.event)
        (boundary.event.after input) := by
  unfold Financial.boundaryDisposition nextDebt
  split <;> rfl

omit [DecidableEq Technology] in
theorem boundary_record_image (index : Nat) {obligation : AdmittedObligation (Financial.vocabulary input)}
    (boundary : Financial.Boundary input obligation) :
    recordImage code input (Financial.Migration.record input index boundary) =
      nextRecord index (Identity.debtImage code input (.live obligation))
        (Identity.eventImage code input boundary.event) (boundary.event.after input) := by
  unfold Financial.Migration.record nextRecord nextDebt
  split <;> rfl

omit [DecidableEq Technology] in
theorem cross_slot_images (before : (Financial.process input).GeneratedState)
    (index : Fin before.current.slots.length) (obligation : AdmittedObligation (Financial.vocabulary input))
    (present : before.current.slots.get index = .live obligation) (boundary : Financial.Boundary input obligation) :
    Identity.financeImage code input (Financial.cross input before index obligation present boundary) =
      (Identity.financeImage code input before).set index.val
        (nextDebt (Identity.debtImage code input (.live obligation))
          (Identity.eventImage code input boundary.event) (boundary.event.after input)) := by
  change (before.current.slots.set index.val (Financial.boundaryDisposition input boundary).targetSlot).map
    (Identity.debtImage code input) = _
  rw [List.map_set, boundary_target_image]
  rfl

omit [DecidableEq Technology] in
theorem cross_record_images (before : (Financial.process input).GeneratedState)
    (index : Fin before.current.slots.length) (obligation : AdmittedObligation (Financial.vocabulary input))
    (present : before.current.slots.get index = .live obligation) (boundary : Financial.Boundary input obligation) :
    eventHistory code input (Financial.cross input before index obligation present boundary) =
      eventHistory code input before ++ [nextRecord index.val (Identity.debtImage code input (.live obligation))
        (Identity.eventImage code input boundary.event) (boundary.event.after input)] := by
  change (before.current.history ++ [(NativeResponsibilityProcess.Edge.cross
    (P := Financial.process input) index obligation present boundary).lifecycleEvent]).map _ = _
  rw [List.map_append, List.map_cons, List.map_nil, Financial.Migration.cross_record, boundary_record_image]
  rfl

variable (other : ProgrammeSource.Input Party Good Port Technology Instrument)

omit [DecidableEq Technology] in
theorem matched_slot_images (old : (Financial.process input).GeneratedState) (new : (Financial.process other).GeneratedState)
    (matched : Match code input other old new) (position : Nat)
    (oldBound : position < old.current.slots.length) (newBound : position < new.current.slots.length) :
    Identity.debtImage code other (new.current.slots.get ⟨position, newBound⟩) =
      Identity.debtImage code input (old.current.slots.get ⟨position, oldBound⟩) := by
  have row := congrArg (fun rows => rows[position]?) matched.slots
  simp only [Identity.financeImage, List.getElem?_map, List.getElem?_eq_getElem oldBound,
    List.getElem?_eq_getElem newBound, Option.map_some] at row
  exact Option.some.inj row

omit [DecidableEq Technology] in
theorem cross_natural (old : (Financial.process input).GeneratedState) (new : (Financial.process other).GeneratedState)
    (matched : Match code input other old new) (position : Nat)
    (oldBound : position < old.current.slots.length) (newBound : position < new.current.slots.length)
    (oldObligation : AdmittedObligation (Financial.vocabulary input))
    (newObligation : AdmittedObligation (Financial.vocabulary other))
    (oldPresent : old.current.slots.get ⟨position, oldBound⟩ = .live oldObligation)
    (newPresent : new.current.slots.get ⟨position, newBound⟩ = .live newObligation)
    (oldBoundary : Financial.Boundary input oldObligation) (newBoundary : Financial.Boundary other newObligation)
    (events : Identity.eventImage code other newBoundary.event = Identity.eventImage code input oldBoundary.event)
    (balances : newBoundary.event.after other = oldBoundary.event.after input) :
    Match code input other
      (Financial.cross input old ⟨position, oldBound⟩ oldObligation oldPresent oldBoundary)
      (Financial.cross other new ⟨position, newBound⟩ newObligation newPresent newBoundary) := by
  have rows := matched_slot_images code input other old new matched position oldBound newBound
  rw [oldPresent, newPresent] at rows
  constructor
  · rw [cross_slot_images, cross_slot_images, matched.slots, rows, events, balances]
  · rw [cross_record_images, cross_record_images, matched.events, rows, events, balances]

omit [DecidableEq Technology] in
theorem allocate_live_natural
    (old : (Financial.process input).GeneratedState) (new : (Financial.process other).GeneratedState)
    (matched : Match code input other old new) (position : Nat)
    (oldBound : position < old.current.slots.length) (newBound : position < new.current.slots.length)
    (oldObligation : AdmittedObligation (Financial.vocabulary input))
    (newObligation : AdmittedObligation (Financial.vocabulary other))
    (oldPresent : old.current.slots.get ⟨position, oldBound⟩ = .live oldObligation)
    (newPresent : new.current.slots.get ⟨position, newBound⟩ = .live newObligation)
    (oldReview : Financial.Review input oldObligation.content) (newReview : Financial.Review other newObligation.content)
    (reviews : reviewData other newReview = reviewData input oldReview)
    (origins : Identity.originImage code other newReview.origin = Identity.originImage code input oldReview.origin)
    (available : ℚ) (nonnegative : 0 ≤ available) :
    Match code input other
      (Financial.allocateLive input old ⟨position, oldBound⟩ oldObligation oldPresent oldReview available nonnegative).after
      (Financial.allocateLive other new ⟨position, newBound⟩ newObligation newPresent newReview available nonnegative).after ∧
      (Financial.allocateLive other new ⟨position, newBound⟩ newObligation newPresent newReview available nonnegative).remaining =
        (Financial.allocateLive input old ⟨position, oldBound⟩ oldObligation oldPresent oldReview available nonnegative).remaining := by
  have rows := matched_slot_images code input other old new matched position oldBound newBound
  rw [oldPresent, newPresent] at rows
  have claims : Identity.claimImage code other newObligation.content =
      Identity.claimImage code input oldObligation.content := congrArg Identity.DebtImage.claim rows
  have balances : newObligation.residual = oldObligation.residual := congrArg Identity.DebtImage.residual rows
  have quantities : newReview.quantity = oldReview.quantity := congrArg ReviewData.quantity reviews
  have afters : newReview.after other newObligation.residual (min available newReview.quantity) =
      oldReview.after input oldObligation.residual (min available oldReview.quantity) := by
    rw [review_after_is_canonical, review_after_is_canonical, after_data_input_independent input other,
      reviews, balances, quantities]
  have events : Identity.eventImage code other
        (.review newObligation.content newReview newObligation.residual (min available newReview.quantity)) =
      Identity.eventImage code input
        (.review oldObligation.content oldReview oldObligation.residual (min available oldReview.quantity)) := by
    rw [review_event_is_canonical, review_event_is_canonical, claims, origins, reviews, balances, quantities]
  constructor
  · exact cross_natural code input other old new matched position oldBound newBound oldObligation newObligation
      oldPresent newPresent _ _ events afters
  · change available - min (min available newReview.quantity) (newObligation.residual (newReview.fromHolder other)) =
      available - min (min available oldReview.quantity) (oldObligation.residual (oldReview.fromHolder input))
    have senders : newReview.fromHolder other = oldReview.fromHolder input := congrArg ReviewData.sender reviews
    rw [balances, quantities, senders]

omit [DecidableEq Technology] in
private theorem allocate_at_terminal (origin : Financial.InstructionOrigin input)
    (before : (Financial.process input).GeneratedState) (position : Nat)
    (bounded : position < before.current.slots.length) (archive : TerminalArchive (Financial.vocabulary input))
    (present : before.current.slots.get ⟨position, bounded⟩ = .terminal archive)
    (available : ℚ) (nonnegative : 0 ≤ available) :
    Financial.allocateAt input origin before position available nonnegative =
      Financial.Allocation.idle input before available nonnegative := by
  unfold Financial.allocateAt
  rw [dif_pos bounded]
  split
  · rfl
  next obligation actual => cases (actual.symm.trans present)

omit [DecidableEq Technology] in
private theorem allocate_at_live (origin : Financial.InstructionOrigin input)
    (before : (Financial.process input).GeneratedState) (position : Nat)
    (bounded : position < before.current.slots.length) (obligation : AdmittedObligation (Financial.vocabulary input))
    (present : before.current.slots.get ⟨position, bounded⟩ = .live obligation)
    (review : Financial.Review input obligation.content) (selected : Financial.readReview input obligation.content origin = some review)
    (available : ℚ) (nonnegative : 0 ≤ available) :
    Financial.allocateAt input origin before position available nonnegative =
      Financial.allocateLive input before ⟨position, bounded⟩ obligation present review available nonnegative := by
  unfold Financial.allocateAt
  rw [dif_pos bounded]
  split
  next archive actual => cases (actual.symm.trans present)
  next actualObligation actual =>
    have same := ObligationSlot.live.inj (actual.symm.trans present)
    subst actualObligation
    rw [selected]

omit [DecidableEq Technology] in
private theorem allocate_at_no_review (origin : Financial.InstructionOrigin input)
    (before : (Financial.process input).GeneratedState) (position : Nat)
    (bounded : position < before.current.slots.length) (obligation : AdmittedObligation (Financial.vocabulary input))
    (present : before.current.slots.get ⟨position, bounded⟩ = .live obligation)
    (selected : Financial.readReview input obligation.content origin = none)
    (available : ℚ) (nonnegative : 0 ≤ available) :
    Financial.allocateAt input origin before position available nonnegative =
      Financial.Allocation.idle input before available nonnegative := by
  unfold Financial.allocateAt
  rw [dif_pos bounded]
  split
  next archive actual => cases (actual.symm.trans present)
  next actualObligation actual =>
    have same := ObligationSlot.live.inj (actual.symm.trans present)
    subst actualObligation
    rw [selected]

omit [DecidableEq Technology] in
theorem allocate_at_natural
    (law : other.law = input.law) (oldOrigin : Financial.InstructionOrigin input) (newOrigin : Financial.InstructionOrigin other)
    (origins : Identity.originImage code other newOrigin = Identity.originImage code input oldOrigin)
    (decoded : newOrigin.instruction? other = oldOrigin.instruction? input)
    (old : (Financial.process input).GeneratedState) (new : (Financial.process other).GeneratedState)
    (matched : Match code input other old new) (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available) :
    Match code input other (Financial.allocateAt input oldOrigin old position available nonnegative).after
        (Financial.allocateAt other newOrigin new position available nonnegative).after ∧
      (Financial.allocateAt other newOrigin new position available nonnegative).remaining =
        (Financial.allocateAt input oldOrigin old position available nonnegative).remaining := by
  have lengths : new.current.slots.length = old.current.slots.length := by
    simpa only [Identity.financeImage, List.length_map] using congrArg List.length matched.slots
  by_cases oldBound : position < old.current.slots.length
  · have newBound : position < new.current.slots.length := by omega
    have rows := matched_slot_images code input other old new matched position oldBound newBound
    cases oldPresent : old.current.slots.get ⟨position, oldBound⟩ with
    | terminal oldArchive =>
      cases newPresent : new.current.slots.get ⟨position, newBound⟩ with
      | terminal newArchive =>
        rw [allocate_at_terminal input oldOrigin old position oldBound oldArchive oldPresent,
          allocate_at_terminal other newOrigin new position newBound newArchive newPresent]
        exact ⟨matched, rfl⟩
      | live newObligation =>
        rw [oldPresent, newPresent] at rows
        have impossible := congrArg Identity.DebtImage.archive rows
        cases impossible
    | live oldObligation =>
      cases newPresent : new.current.slots.get ⟨position, newBound⟩ with
      | terminal newArchive =>
        rw [oldPresent, newPresent] at rows
        have impossible := congrArg Identity.DebtImage.archive rows
        cases impossible
      | live newObligation =>
        rw [oldPresent, newPresent] at rows
        have sameReviews := read_review_natural input other law oldObligation.content newObligation.content
          oldOrigin newOrigin (congrArg (fun debt => debt.claim.instrument) rows)
          (congrArg (fun debt => debt.claim.debtor) rows) decoded
        cases oldSelected : Financial.readReview input oldObligation.content oldOrigin with
        | none =>
          have newNone : Financial.readReview other newObligation.content newOrigin = none := by
            rw [oldSelected, Option.map_none] at sameReviews
            exact Option.map_eq_none_iff.mp sameReviews
          rw [allocate_at_no_review input oldOrigin old position oldBound oldObligation oldPresent oldSelected,
            allocate_at_no_review other newOrigin new position newBound newObligation newPresent newNone]
          exact ⟨matched, rfl⟩
        | some oldReview =>
          cases newSelected : Financial.readReview other newObligation.content newOrigin with
          | none => simp only [oldSelected, newSelected, Option.map_none, Option.map_some] at sameReviews; cases sameReviews
          | some newReview =>
            have reviews : reviewData other newReview = reviewData input oldReview := by
              simpa only [oldSelected, newSelected, Option.map_some, Option.some.injEq] using sameReviews
            have reviewOrigins : Identity.originImage code other newReview.origin =
                Identity.originImage code input oldReview.origin := by
              rw [Financial.readReview_origin other newObligation.content newOrigin newReview newSelected,
                Financial.readReview_origin input oldObligation.content oldOrigin oldReview oldSelected]
              exact origins
            rw [allocate_at_live input oldOrigin old position oldBound oldObligation oldPresent oldReview oldSelected,
              allocate_at_live other newOrigin new position newBound newObligation newPresent newReview newSelected]
            exact allocate_live_natural code input other old new matched position oldBound newBound
              oldObligation newObligation oldPresent newPresent oldReview newReview reviews reviewOrigins available nonnegative
  · have newBound : ¬ position < new.current.slots.length := by omega
    simp only [Financial.allocateAt, dif_neg oldBound, dif_neg newBound]
    exact ⟨matched, rfl⟩

omit [DecidableEq Technology] in
theorem allocate_from_natural
    (law : other.law = input.law) (oldOrigin : Financial.InstructionOrigin input) (newOrigin : Financial.InstructionOrigin other)
    (origins : Identity.originImage code other newOrigin = Identity.originImage code input oldOrigin)
    (decoded : newOrigin.instruction? other = oldOrigin.instruction? input)
    (fuel position : Nat) (old : (Financial.process input).GeneratedState) (new : (Financial.process other).GeneratedState)
    (matched : Match code input other old new) (oldAvailable newAvailable : ℚ)
    (quantities : newAvailable = oldAvailable) (oldNonnegative : 0 ≤ oldAvailable) (newNonnegative : 0 ≤ newAvailable) :
    Match code input other
        (Financial.allocateFrom input oldOrigin position fuel old oldAvailable oldNonnegative).after
        (Financial.allocateFrom other newOrigin position fuel new newAvailable newNonnegative).after ∧
      (Financial.allocateFrom other newOrigin position fuel new newAvailable newNonnegative).remaining =
        (Financial.allocateFrom input oldOrigin position fuel old oldAvailable oldNonnegative).remaining := by
  induction fuel generalizing position old new oldAvailable newAvailable with
  | zero => exact ⟨matched, quantities⟩
  | succ fuel ih =>
    subst newAvailable
    let oldFirst := Financial.allocateAt input oldOrigin old position oldAvailable oldNonnegative
    let newFirst := Financial.allocateAt other newOrigin new position oldAvailable newNonnegative
    have first := allocate_at_natural code input other law oldOrigin newOrigin origins decoded
      old new matched position oldAvailable oldNonnegative
    have rest := ih (position + 1) oldFirst.after newFirst.after first.1 oldFirst.remaining newFirst.remaining
      first.2 oldFirst.remaining_nonnegative newFirst.remaining_nonnegative
    exact rest

omit [DecidableEq Technology] in
theorem allocate_natural
    (law : other.law = input.law) (oldOrigin : Financial.InstructionOrigin input) (newOrigin : Financial.InstructionOrigin other)
    (origins : Identity.originImage code other newOrigin = Identity.originImage code input oldOrigin)
    (decoded : newOrigin.instruction? other = oldOrigin.instruction? input)
    (old : (Financial.process input).GeneratedState) (new : (Financial.process other).GeneratedState)
    (matched : Match code input other old new) (oldAvailable newAvailable : ℚ)
    (quantities : newAvailable = oldAvailable) (oldNonnegative : 0 ≤ oldAvailable) (newNonnegative : 0 ≤ newAvailable) :
    Match code input other (Financial.allocate input oldOrigin old oldAvailable oldNonnegative).after
        (Financial.allocate other newOrigin new newAvailable newNonnegative).after ∧
      (Financial.allocate other newOrigin new newAvailable newNonnegative).remaining =
        (Financial.allocate input oldOrigin old oldAvailable oldNonnegative).remaining := by
  have lengths : new.current.slots.length = old.current.slots.length := by
    simpa only [Identity.financeImage, List.length_map] using congrArg List.length matched.slots
  unfold Financial.allocate
  rw [lengths]
  exact allocate_from_natural code input other law oldOrigin newOrigin origins decoded _ 0 old new matched
    oldAvailable newAvailable quantities oldNonnegative newNonnegative


omit [DecidableEq Technology] in
theorem birth_actor_natural (law : other.law = input.law) (initial : other.initial = input.initial)
    (old : Institutions.Capitalism.Universal.Source.ProgrammeFace.ActualBirth.Witness input)
    (new : Institutions.Capitalism.Universal.Source.ProgrammeFace.ActualBirth.Witness other)
    (same : Identity.birthImage code other new = Identity.birthImage code input old) :
    Identity.actorImage code other (new.actor other) = Identity.actorImage code input (old.actor input) := by
  have occurrences : Identity.occurrenceImage code other new.visit.current =
      Identity.occurrenceImage code input old.visit.current := congrArg Identity.BirthImage.occurrence same
  have visits := Identity.visitImage_injective code (congrArg Identity.OccurrenceImage.visit occurrences)
  have words : ProgrammeSource.rawEvent other new.visit.current = ProgrammeSource.rawEvent input old.visit.current :=
    congrArg Identity.OccurrenceImage.word occurrences
  have parties : new.party = old.party := congrArg Identity.BirthImage.party same
  have currents : ProgrammeSource.rawCurrent other new.visit.current = ProgrammeSource.rawCurrent input old.visit.current := by
    rw [visits]
    cases old.visit.current <;> first | exact initial | rfl
  change Identity.ActorImage.mk (Identity.occurrenceImage code other new.visit.current)
      (Institutions.Capitalism.Universal.Source.ProgrammeFace.actorLineage other.law
        (ProgrammeSource.rawCurrent other new.visit.current, ProgrammeSource.rawEvent other new.visit.current) new.party) =
    Identity.ActorImage.mk (Identity.occurrenceImage code input old.visit.current)
      (Institutions.Capitalism.Universal.Source.ProgrammeFace.actorLineage input.law
        (ProgrammeSource.rawCurrent input old.visit.current, ProgrammeSource.rawEvent input old.visit.current) old.party)
  rw [show Identity.occurrenceImage code other new.visit.current = Identity.occurrenceImage code input old.visit.current from occurrences,
    law, currents, words, parties]

omit [DecidableEq Technology] in
theorem admission_debt_natural (law : other.law = input.law) (initial : other.initial = input.initial)
    (old : Financial.IssuedClaim input) (new : Financial.IssuedClaim other)
    (claims : Identity.claimImage code other new = Identity.claimImage code input old) :
    Identity.debtImage code other (.live (Financial.admission other new).toObligation) =
      Identity.debtImage code input (.live (Financial.admission input old).toObligation) := by
  have origins : Identity.originImage code other new.origin = Identity.originImage code input old.origin :=
    congrArg Identity.ClaimImage.origin claims
  have actors := birth_actor_natural code input other law initial old.debtor_born.original new.debtor_born.original
    (congrArg Identity.ClaimImage.debtorBirth claims)
  have holders : new.holder = old.holder := congrArg Identity.ClaimImage.holder claims
  have quantities : new.quantity = old.quantity := congrArg Identity.ClaimImage.quantity claims
  have balances : Financial.initialBalance other new = Financial.initialBalance input old := by
    change Financial.initialShare other new.holder new.quantity = Financial.initialShare input old.holder old.quantity
    rw [Financial.initialShare_eq_single, Financial.initialShare_eq_single, holders, quantities]
  change Identity.DebtImage.mk (Identity.claimImage code other new) (Identity.claimImage code other new)
      (Identity.actorImage code other (new.debtorActor other)) (Identity.originImage code other new.origin)
      (.birth (Identity.claimImage code other new)) (Identity.actorImage code other (new.debtorActor other))
      (Identity.originImage code other new.origin) (Identity.originImage code other new.origin)
      (Financial.initialBalance other new) (Financial.initialBalance other new) none = _
  change Identity.DebtImage.mk (Identity.claimImage code other new) (Identity.claimImage code other new)
      (Identity.actorImage code other (new.debtorActor other)) (Identity.originImage code other new.origin)
      (.birth (Identity.claimImage code other new)) (Identity.actorImage code other (new.debtorActor other))
      (Identity.originImage code other new.origin) (Identity.originImage code other new.origin)
      (Financial.initialBalance other new) (Financial.initialBalance other new) none =
    Identity.DebtImage.mk (Identity.claimImage code input old) (Identity.claimImage code input old)
      (Identity.actorImage code input (old.debtorActor input)) (Identity.originImage code input old.origin)
      (.birth (Identity.claimImage code input old)) (Identity.actorImage code input (old.debtorActor input))
      (Identity.originImage code input old.origin) (Identity.originImage code input old.origin)
      (Financial.initialBalance input old) (Financial.initialBalance input old) none
  rw [claims, origins, balances]
  change Identity.DebtImage.mk _ _ (Identity.actorImage code other (new.debtor_born.original.actor other)) _ _
      (Identity.actorImage code other (new.debtor_born.original.actor other)) _ _ _ _ _ = _
  rw [actors]
  rfl

omit [DecidableEq Technology] in
theorem admit_natural (law : other.law = input.law) (initial : other.initial = input.initial)
    (old : (Financial.process input).GeneratedState) (new : (Financial.process other).GeneratedState)
    (matched : Match code input other old new) (oldClaim : Financial.IssuedClaim input) (newClaim : Financial.IssuedClaim other)
    (claims : Identity.claimImage code other newClaim = Identity.claimImage code input oldClaim) :
    Match code input other (Financial.admit input old oldClaim) (Financial.admit other new newClaim) := by
  have debts := admission_debt_natural code input other law initial oldClaim newClaim claims
  have lengths : new.current.slots.length = old.current.slots.length := by
    simpa only [Identity.financeImage, List.length_map] using congrArg List.length matched.slots
  constructor
  · change (new.current.slots ++ [ObligationSlot.live (Financial.admission other newClaim).toObligation]).map _ =
      (old.current.slots ++ [ObligationSlot.live (Financial.admission input oldClaim).toObligation]).map _
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [show new.current.slots.map (Identity.debtImage code other) = old.current.slots.map (Identity.debtImage code input) from matched.slots, debts]
  · change (new.current.history ++ [LifecycleEvent.admitted new.current.slots.length (Financial.admission other newClaim)]).map _ =
      (old.current.history ++ [LifecycleEvent.admitted old.current.slots.length (Financial.admission input oldClaim)]).map _
    simp only [List.map_append, List.map_cons, List.map_nil, recordImage]
    rw [show new.current.history.map (recordImage code other) = old.current.history.map (recordImage code input) from matched.events,
      lengths, debts, show Identity.eventImage code other (Financial.admission other newClaim).sourceEvent =
        Identity.eventImage code input (Financial.admission input oldClaim).sourceEvent from congrArg Identity.EventImage.birth claims]


def movementQuantity (origin : Financial.InstructionOrigin input) :=
  (Financial.readMovement input origin).map (fun movement => movement.quantity)

def canonicalMovementQuantity (decoded : Option (ExecutionItem Party Good Port Technology Instrument)) : Option ℚ :=
  decoded.bind fun item => if input.law.Valid item.before item.request then
    match item.request.operation with | .settle _ _ _ q | .assign _ _ _ _ q => some q | _ => none
  else none

omit [DecidableEq Port] [DecidableEq Technology] in
theorem movement_quantity_is_canonical (origin : Financial.InstructionOrigin input) :
    movementQuantity input origin = canonicalMovementQuantity input (origin.instruction? input) := by
  unfold movementQuantity
  generalize produced : Financial.readMovement input origin = result
  unfold Financial.readMovement at produced
  split at produced
  next absent =>
    cases produced
    simp only [canonicalMovementQuantity, absent, Option.bind_none, Option.map_none]
  next item decoded =>
    split at produced
    next accepted =>
      split at produced <;> cases produced <;>
        simp_all only [canonicalMovementQuantity, Option.bind_some, Option.map_some, Option.map_none, ↓reduceIte]
    next refused =>
      cases produced
      simp only [canonicalMovementQuantity, decoded, Option.bind_some, if_neg refused, Option.map_none]

omit [DecidableEq Port] [DecidableEq Technology] in
theorem movement_quantity_natural (law : other.law = input.law)
    (oldOrigin : Financial.InstructionOrigin input) (newOrigin : Financial.InstructionOrigin other)
    (decoded : newOrigin.instruction? other = oldOrigin.instruction? input) :
    movementQuantity other newOrigin = movementQuantity input oldOrigin := by
  rw [movement_quantity_is_canonical, movement_quantity_is_canonical]
  unfold canonicalMovementQuantity
  rw [law, decoded]


omit [DecidableEq Technology] in
theorem consume_next_shape (origin : Financial.InstructionOrigin input) (before : (Financial.process input).GeneratedState) :
    (Financial.consume input origin before).next input =
      match Financial.issuedClaim? input origin with
      | some claim => Financial.admit input before claim
      | none => match Financial.readMovement input origin with
        | some movement => (Financial.allocate input origin before movement.quantity (movement.quantity_nonnegative input)).after
        | none => before := by
  cases produced : Financial.readIssue input origin with
  | issued claim exactOrigin => simp only [Financial.consume, Financial.issuedClaim?, produced, Financial.InstructionResult.next]
  | nonfinancial =>
    simp only [Financial.consume, Financial.issuedClaim?, produced]
    cases Financial.readMovement input origin <;> rfl
  | rejected instruction original refused =>
    simp only [Financial.consume, Financial.issuedClaim?, produced,
      Financial.BalanceConservation.movement_readout_refused input origin instruction original refused,
      Financial.InstructionResult.next]
  | missingBirth party notBorn =>
    have impossible : False := by
      unfold Financial.readIssue at produced
      repeat' first | contradiction | split at produced
    exact impossible.elim


omit [DecidableEq Technology] in
theorem consume_natural (law : other.law = input.law) (initial : other.initial = input.initial)
    (oldOrigin : Financial.InstructionOrigin input) (newOrigin : Financial.InstructionOrigin other)
    (origins : Identity.originImage code other newOrigin = Identity.originImage code input oldOrigin)
    (decoded : newOrigin.instruction? other = oldOrigin.instruction? input)
    (issues : Causality.issuedImage code other newOrigin = Causality.issuedImage code input oldOrigin)
    (old : (Financial.process input).GeneratedState) (new : (Financial.process other).GeneratedState)
    (matched : Match code input other old new) :
    Match code input other ((Financial.consume input oldOrigin old).next input)
      ((Financial.consume other newOrigin new).next other) := by
  rw [consume_next_shape, consume_next_shape]
  unfold Causality.issuedImage at issues
  cases oldIssue : Financial.issuedClaim? input oldOrigin with
  | some oldClaim =>
    cases newIssue : Financial.issuedClaim? other newOrigin with
    | none => simp only [oldIssue, newIssue, Option.map_some, Option.map_none] at issues; cases issues
    | some newClaim =>
      have claims : Identity.claimImage code other newClaim = Identity.claimImage code input oldClaim := by
        simpa only [oldIssue, newIssue, Option.map_some, Option.some.injEq] using issues
      exact admit_natural code input other law initial old new matched oldClaim newClaim claims
  | none =>
    cases newIssue : Financial.issuedClaim? other newOrigin with
    | some newClaim => simp only [oldIssue, newIssue, Option.map_some, Option.map_none] at issues; cases issues
    | none =>
      have movements := movement_quantity_natural input other law oldOrigin newOrigin decoded
      unfold movementQuantity at movements
      cases oldSelected : Financial.readMovement input oldOrigin with
      | none =>
        have newNone : Financial.readMovement other newOrigin = none := by
          rw [oldSelected, Option.map_none] at movements
          exact Option.map_eq_none_iff.mp movements
        rw [newNone]
        exact matched
      | some oldMovement =>
        cases newSelected : Financial.readMovement other newOrigin with
        | none => simp only [oldSelected, newSelected, Option.map_some, Option.map_none] at movements; cases movements
        | some newMovement =>
          have quantities : newMovement.quantity = oldMovement.quantity := by
            simpa only [oldSelected, newSelected, Option.map_some, Option.some.injEq] using movements
          exact (allocate_natural code input other law oldOrigin newOrigin origins decoded old new matched
            oldMovement.quantity newMovement.quantity quantities (oldMovement.quantity_nonnegative input)
            (newMovement.quantity_nonnegative other)).1

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Coupling.State
