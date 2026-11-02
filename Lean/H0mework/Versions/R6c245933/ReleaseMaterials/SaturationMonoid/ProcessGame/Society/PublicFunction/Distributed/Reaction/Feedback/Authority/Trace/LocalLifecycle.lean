import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.GrantJoint

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.LocalLifecycle

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Mandate.Challenge

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port (Mandate.State Party Technology) Instrument)
  {base : RawLaw Party Good Port Technology Instrument} {scope : Mandate.Scope}
  {Index : Type} (family : ProgrammeFamily base scope Index)
  {inputs nextInputs : Index} {oldOriginal : Claim family inputs} {newOriginal : Claim family nextInputs}

def pendingImage {atInput : Index} {original : Claim family atInput} : Mandate.Challenge.History family atInput original →
    Option (ChallengeImage Party Good Port Technology Instrument)
  | .pending target _ _ => some (challengeImage code family atInput (target.claim family atInput))
  | .closed .. => none

structure Match (old : Mandate.Challenge.History family inputs oldOriginal) (new : Mandate.Challenge.History family nextInputs newOriginal) : Prop where
  original : challengeImage code family nextInputs newOriginal = challengeImage code family inputs oldOriginal
  state : challengeStateImage code family nextInputs new.state.current = challengeStateImage code family inputs old.state.current
  pending : pendingImage code family new = pendingImage code family old

private theorem claim_coordinates (old : Claim family inputs) (new : Claim family nextInputs)
    (same : challengeImage code family nextInputs new = challengeImage code family inputs old) :
    new.position.ordinal = old.position.ordinal ∧ new.position.index.val = old.position.index.val := by
  have indices := congrArg (fun image => image.position.origin.traceIndex) same
  change some new.position.index.val = some old.position.index.val at indices
  exact ⟨congrArg (fun image => image.position.ordinal) same, Option.some.inj indices⟩

private theorem claim_items (old : Claim family inputs) (new : Claim family nextInputs)
    (same : challengeImage code family nextInputs new = challengeImage code family inputs old) :
    new.position.item family nextInputs = old.position.item family inputs :=
  itemImage_injective code (congrArg (fun image => image.position.item) same)

private theorem tracked_images
    (oldTarget : Target family inputs oldOriginal) (newTarget : Target family nextInputs newOriginal)
    (original : challengeImage code family nextInputs newOriginal = challengeImage code family inputs oldOriginal)
    (target : challengeImage code family nextInputs (newTarget.claim family nextInputs) =
      challengeImage code family inputs (oldTarget.claim family inputs)) :
    challengeObligationImage code family nextInputs (tracked family nextInputs newOriginal newTarget) =
      challengeObligationImage code family inputs (tracked family inputs oldOriginal oldTarget) := by
  have snapshot := congrArg (fun item => item.before.technology)
    (claim_items code family _ _ target)
  change (newTarget.claim family nextInputs).snapshot family nextInputs = (oldTarget.claim family inputs).snapshot family inputs at snapshot
  change ChallengeObligationImage.mk (.birth (challengeImage code family nextInputs newOriginal))
      (challengeImage code family nextInputs newOriginal).actor (challengeImage code family nextInputs newOriginal).position.origin
      (challengeImage code family nextInputs newOriginal) ((newTarget.claim family nextInputs).snapshot family nextInputs) (challengeImage code family nextInputs newOriginal).actor
      (taskImage scope.task) (challengeImage code family nextInputs newOriginal).position.origin
      (challengeImage code family nextInputs newOriginal).position.origin =
    ChallengeObligationImage.mk (.birth (challengeImage code family inputs oldOriginal))
      (challengeImage code family inputs oldOriginal).actor (challengeImage code family inputs oldOriginal).position.origin
      (challengeImage code family inputs oldOriginal) ((oldTarget.claim family inputs).snapshot family inputs)
      (challengeImage code family inputs oldOriginal).actor (taskImage scope.task)
      (challengeImage code family inputs oldOriginal).position.origin (challengeImage code family inputs oldOriginal).position.origin
  rw [original, snapshot]

theorem initial_match (same : challengeImage code family nextInputs newOriginal = challengeImage code family inputs oldOriginal) :
    Match code family (Mandate.Challenge.History.initial family inputs oldOriginal) (Mandate.Challenge.History.initial family nextInputs newOriginal) := by
  have admissionImage := tracked_images code family (.initial : Target family inputs oldOriginal)
    (.initial : Target family nextInputs newOriginal) same same
  refine ⟨same, ?_, congrArg some same⟩
  change ChallengeStateImage.mk [.live (challengeObligationImage code family nextInputs (obligation family nextInputs newOriginal))]
      [⟨0, .admitted, none, .live (challengeObligationImage code family nextInputs (obligation family nextInputs newOriginal)),
        .birth (challengeImage code family nextInputs newOriginal)⟩] = _
  change challengeObligationImage code family nextInputs (Mandate.Challenge.obligation family nextInputs newOriginal) =
    challengeObligationImage code family inputs (Mandate.Challenge.obligation family inputs oldOriginal) at admissionImage
  rw [admissionImage, same]
  rfl

def readSources {atInput : Index} {original : Claim family atInput}
    (history : Mandate.Challenge.History family atInput original) (position : Position family atInput) :=
  match history with
  | .pending target _ _ =>
      ((readReconfirmation family atInput original position).map fun receipt =>
          challengeEventImage code family atInput (.reaffirm original target receipt),
        (readAttempt family atInput (target.claim family atInput) position).map fun receipt =>
          challengeEventImage code family atInput (.attempt original target receipt))
  | .closed .. => (none, none)

private theorem later_congr (oldFirst oldLast : Claim family inputs) (newFirst newLast : Claim family nextInputs)
    (first : challengeImage code family nextInputs newFirst = challengeImage code family inputs oldFirst)
    (last : challengeImage code family nextInputs newLast = challengeImage code family inputs oldLast) :
    Later family nextInputs newFirst.position newLast.position ↔ Later family inputs oldFirst.position oldLast.position := by
  have a := claim_coordinates code family oldFirst newFirst first
  have b := claim_coordinates code family oldLast newLast last
  simp only [Later, a.1, a.2, b.1, b.2]

private theorem reconfirmation_sources
    (oldTarget : Target family inputs oldOriginal) (newTarget : Target family nextInputs newOriginal)
    (oldPosition : Position family inputs) (newPosition : Position family nextInputs)
    (original : challengeImage code family nextInputs newOriginal = challengeImage code family inputs oldOriginal)
    (target : challengeImage code family nextInputs (newTarget.claim family nextInputs) =
      challengeImage code family inputs (oldTarget.claim family inputs))
    (reads : (read family nextInputs newPosition).map (challengeImage code family nextInputs) =
      (read family inputs oldPosition).map (challengeImage code family inputs)) :
    (readReconfirmation family nextInputs newOriginal newPosition).map (fun receipt =>
        challengeEventImage code family nextInputs (.reaffirm newOriginal newTarget receipt)) =
      (readReconfirmation family inputs oldOriginal oldPosition).map (fun receipt =>
        challengeEventImage code family inputs (.reaffirm oldOriginal oldTarget receipt)) := by
  unfold readReconfirmation
  cases oldRead : read family inputs oldPosition <;> cases newRead : read family nextInputs newPosition <;>
    simp only [oldRead, newRead, Option.map_none, Option.map_some] at reads ⊢
  · cases reads
  · cases reads
  · rename_i oldClaim newClaim
    have claim := Option.some.inj reads
    have order := later_congr code family oldOriginal oldClaim newOriginal newClaim original claim
    have signer := congrArg (fun item => item.request.signer) (claim_items code family oldClaim newClaim claim)
    have firstSigner := congrArg (fun item => item.request.signer) (claim_items code family oldOriginal newOriginal original)
    change newClaim.signer family nextInputs = oldClaim.signer family inputs at signer
    change newOriginal.signer family nextInputs = oldOriginal.signer family inputs at firstSigner
    have valid : (Later family nextInputs newOriginal.position newClaim.position ∧
        newClaim.signer family nextInputs = newOriginal.signer family nextInputs) ↔
      (Later family inputs oldOriginal.position oldClaim.position ∧ oldClaim.signer family inputs = oldOriginal.signer family inputs) := by
      rw [order, signer, firstSigner]
    by_cases checked : Later family inputs oldOriginal.position oldClaim.position ∧ oldClaim.signer family inputs = oldOriginal.signer family inputs
    · rw [dif_pos checked, dif_pos (valid.mpr checked)]
      simp only [Option.map_some, challengeEventImage]
      rw [original, target, claim]
    · rw [dif_neg checked, dif_neg (fun accepted => checked (valid.mp accepted))]
      rfl

private theorem attempt_sources
    (oldTarget : Target family inputs oldOriginal) (newTarget : Target family nextInputs newOriginal)
    (oldPosition : Position family inputs) (newPosition : Position family nextInputs)
    (original : challengeImage code family nextInputs newOriginal = challengeImage code family inputs oldOriginal)
    (target : challengeImage code family nextInputs (newTarget.claim family nextInputs) =
      challengeImage code family inputs (oldTarget.claim family inputs))
    (position : positionImage code family nextInputs newPosition = positionImage code family inputs oldPosition) :
    (readAttempt family nextInputs (newTarget.claim family nextInputs) newPosition).map (fun receipt =>
        challengeEventImage code family nextInputs (.attempt newOriginal newTarget receipt)) =
      (readAttempt family inputs (oldTarget.claim family inputs) oldPosition).map (fun receipt =>
        challengeEventImage code family inputs (.attempt oldOriginal oldTarget receipt)) := by
  have coordinates := claim_coordinates code family _ _ target
  have positionOrdinal := congrArg PositionImage.ordinal position
  change newPosition.ordinal = oldPosition.ordinal at positionOrdinal
  have positionIndex := congrArg (fun image => image.origin.traceIndex) position
  change some newPosition.index.val = some oldPosition.index.val at positionIndex
  have index := Option.some.inj positionIndex
  have item := (equal_position_images_recover_the_actual_item code family inputs nextInputs oldPosition newPosition position).2
  have snapshot := congrArg (fun item => item.before.technology) (claim_items code family _ _ target)
  have valid : (Later family nextInputs (newTarget.claim family nextInputs).position newPosition ∧
      Withdrawal (scope := scope) (newPosition.item family nextInputs).before (newPosition.item family nextInputs).request ∧
      (newPosition.item family nextInputs).before.technology = (newTarget.claim family nextInputs).snapshot family nextInputs) ↔
    (Later family inputs (oldTarget.claim family inputs).position oldPosition ∧
      Withdrawal (scope := scope) (oldPosition.item family inputs).before (oldPosition.item family inputs).request ∧
      (oldPosition.item family inputs).before.technology = (oldTarget.claim family inputs).snapshot family inputs) := by
    simp only [Later, Claim.snapshot, coordinates.1, coordinates.2, positionOrdinal, index, item, snapshot]
  unfold readAttempt
  by_cases checked : Later family inputs (oldTarget.claim family inputs).position oldPosition ∧
      Withdrawal (scope := scope) (oldPosition.item family inputs).before (oldPosition.item family inputs).request ∧
      (oldPosition.item family inputs).before.technology = (oldTarget.claim family inputs).snapshot family inputs
  · rw [dif_pos checked, dif_pos (valid.mpr checked)]
    simp only [Option.map_some, challengeEventImage]
    rw [original, target, position, item]
  · rw [dif_neg checked, dif_neg (fun accepted => checked (valid.mp accepted))]
    rfl

private theorem cross_image {atInput : Index} {original : Claim family atInput}
    (state : (process family atInput original).GeneratedState)
    (slot : Fin state.current.slots.length) (obligation : AdmittedObligation (V family atInput))
    (present : state.current.slots.get slot = .live obligation) (event : Boundary family atInput original obligation) :
    challengeStateImage code family atInput
        (state.step (process family atInput original) (.cross slot obligation present event)).current =
      ⟨(challengeStateImage code family atInput state.current).slots.set slot.val
          (challengeSlotImage code family atInput (disposition family atInput original event).targetSlot),
        (challengeStateImage code family atInput state.current).history ++
          [challengeRecordImage code family atInput ((NativeResponsibilityProcess.Edge.cross (P := process family atInput original) slot obligation present event).lifecycleEvent)]⟩ := by
  change ChallengeStateImage.mk ((state.current.slots.set slot.val _).map _) ((state.current.history ++ [_]).map _) = _
  rw [List.map_set, List.map_append, List.map_cons, List.map_nil]
  rfl

private theorem reaffirm_boundary_images
    (old : Target family inputs oldOriginal) (new : Target family nextInputs newOriginal)
    (oldReceipt : Reconfirmation family inputs oldOriginal) (newReceipt : Reconfirmation family nextInputs newOriginal)
    (oldLater : Later family inputs (old.claim family inputs).position oldReceipt.target.position)
    (newLater : Later family nextInputs (new.claim family nextInputs).position newReceipt.target.position)
    (oldState : ResponsibilityState (V family inputs)) (newState : ResponsibilityState (V family nextInputs))
    (oldSlot : Fin oldState.slots.length) (newSlot : Fin newState.slots.length)
    (sameSlot : newSlot.val = oldSlot.val)
    (oldPresent : oldState.slots.get oldSlot = .live (tracked family inputs oldOriginal old))
    (newPresent : newState.slots.get newSlot = .live (tracked family nextInputs newOriginal new))
    (same : challengeEventImage code family nextInputs (.reaffirm newOriginal new newReceipt) =
      challengeEventImage code family inputs (.reaffirm oldOriginal old oldReceipt)) :
    challengeSlotImage code family nextInputs (disposition family nextInputs newOriginal (.reaffirm new newReceipt newLater rfl)).targetSlot =
        challengeSlotImage code family inputs (disposition family inputs oldOriginal (.reaffirm old oldReceipt oldLater rfl)).targetSlot ∧
      challengeRecordImage code family nextInputs ((NativeResponsibilityProcess.Edge.cross (P := process family nextInputs newOriginal) newSlot (tracked family nextInputs newOriginal new) newPresent (.reaffirm new newReceipt newLater rfl)).lifecycleEvent) =
      challengeRecordImage code family inputs ((NativeResponsibilityProcess.Edge.cross (P := process family inputs oldOriginal) oldSlot (tracked family inputs oldOriginal old) oldPresent (.reaffirm old oldReceipt oldLater rfl)).lifecycleEvent) := by
  have parts := ChallengeEventImage.reaffirm.inj same
  have previous := tracked_images code family old new parts.2.1 parts.2.2.1
  have next := tracked_images code family (.renewed oldReceipt) (.renewed newReceipt) parts.2.1 parts.2.2.2
  change ChallengeSlotImage.live (challengeObligationImage code family nextInputs (tracked family nextInputs newOriginal (.renewed newReceipt))) =
        ChallengeSlotImage.live (challengeObligationImage code family inputs (tracked family inputs oldOriginal (.renewed oldReceipt))) ∧
      ChallengeRecordImage.mk newSlot.val .progressed
        (some (.live (challengeObligationImage code family nextInputs (tracked family nextInputs newOriginal new))))
        (.live (challengeObligationImage code family nextInputs (tracked family nextInputs newOriginal (.renewed newReceipt))))
        (challengeEventImage code family nextInputs (.reaffirm newOriginal new newReceipt)) =
      ChallengeRecordImage.mk oldSlot.val .progressed
        (some (.live (challengeObligationImage code family inputs (tracked family inputs oldOriginal old))))
        (.live (challengeObligationImage code family inputs (tracked family inputs oldOriginal (.renewed oldReceipt))))
        (challengeEventImage code family inputs (.reaffirm oldOriginal old oldReceipt))
  rw [sameSlot, previous, next, same]
  exact ⟨rfl, rfl⟩

private theorem attempt_items
    (old : Target family inputs oldOriginal) (new : Target family nextInputs newOriginal)
    (oldReceipt : Attempt family inputs (old.claim family inputs)) (newReceipt : Attempt family nextInputs (new.claim family nextInputs))
    (same : challengeEventImage code family nextInputs (.attempt newOriginal new newReceipt) =
      challengeEventImage code family inputs (.attempt oldOriginal old oldReceipt)) :
    newReceipt.position.item family nextInputs = oldReceipt.position.item family inputs := by
  have parts := ChallengeEventImage.attempt.inj same
  exact (equal_position_images_recover_the_actual_item code family inputs nextInputs _ _ parts.2.2.2.1).2

private theorem attempt_boundary_images
    (old : Target family inputs oldOriginal) (new : Target family nextInputs newOriginal)
    (oldReceipt : Attempt family inputs (old.claim family inputs)) (newReceipt : Attempt family nextInputs (new.claim family nextInputs))
    (oldState : ResponsibilityState (V family inputs)) (newState : ResponsibilityState (V family nextInputs))
    (oldSlot : Fin oldState.slots.length) (newSlot : Fin newState.slots.length)
    (sameSlot : newSlot.val = oldSlot.val)
    (oldPresent : oldState.slots.get oldSlot = .live (tracked family inputs oldOriginal old))
    (newPresent : newState.slots.get newSlot = .live (tracked family nextInputs newOriginal new))
    (same : challengeEventImage code family nextInputs (.attempt newOriginal new newReceipt) =
      challengeEventImage code family inputs (.attempt oldOriginal old oldReceipt)) :
    challengeSlotImage code family nextInputs (disposition family nextInputs newOriginal (.attempt new newReceipt rfl)).targetSlot =
        challengeSlotImage code family inputs (disposition family inputs oldOriginal (.attempt old oldReceipt rfl)).targetSlot ∧
      challengeRecordImage code family nextInputs ((NativeResponsibilityProcess.Edge.cross (P := process family nextInputs newOriginal) newSlot (tracked family nextInputs newOriginal new) newPresent (.attempt new newReceipt rfl)).lifecycleEvent) =
      challengeRecordImage code family inputs ((NativeResponsibilityProcess.Edge.cross (P := process family inputs oldOriginal) oldSlot (tracked family inputs oldOriginal old) oldPresent (.attempt old oldReceipt rfl)).lifecycleEvent) := by
  have parts := ChallengeEventImage.attempt.inj same
  have previous := tracked_images code family old new parts.2.1 parts.2.2.1
  have item := attempt_items code family old new oldReceipt newReceipt same
  by_cases accepted : (Mandate.law base scope).Valid (oldReceipt.position.item family inputs).before (oldReceipt.position.item family inputs).request
  · have nextAccepted : (Mandate.law base scope).Valid (newReceipt.position.item family nextInputs).before (newReceipt.position.item family nextInputs).request := by rw [item]; exact accepted
    simp only [NativeResponsibilityProcess.Edge.lifecycleEvent, process, disposition, dif_pos accepted, dif_pos nextAccepted]
    change ChallengeSlotImage.terminal (challengeObligationImage code family nextInputs (tracked family nextInputs newOriginal new))
          (challengeEventImage code family nextInputs (.attempt newOriginal new newReceipt)) =
        ChallengeSlotImage.terminal (challengeObligationImage code family inputs (tracked family inputs oldOriginal old))
          (challengeEventImage code family inputs (.attempt oldOriginal old oldReceipt)) ∧
      ChallengeRecordImage.mk newSlot.val .obligationTerminal
        (some (.live (challengeObligationImage code family nextInputs (tracked family nextInputs newOriginal new))))
        (.terminal (challengeObligationImage code family nextInputs (tracked family nextInputs newOriginal new))
          (challengeEventImage code family nextInputs (.attempt newOriginal new newReceipt)))
        (challengeEventImage code family nextInputs (.attempt newOriginal new newReceipt)) =
      ChallengeRecordImage.mk oldSlot.val .obligationTerminal
        (some (.live (challengeObligationImage code family inputs (tracked family inputs oldOriginal old))))
        (.terminal (challengeObligationImage code family inputs (tracked family inputs oldOriginal old))
          (challengeEventImage code family inputs (.attempt oldOriginal old oldReceipt)))
        (challengeEventImage code family inputs (.attempt oldOriginal old oldReceipt))
    rw [sameSlot, previous, same]
    exact ⟨rfl, rfl⟩
  · have nextRefused : ¬(Mandate.law base scope).Valid (newReceipt.position.item family nextInputs).before (newReceipt.position.item family nextInputs).request := by rw [item]; exact accepted
    simp only [NativeResponsibilityProcess.Edge.lifecycleEvent, process, disposition, dif_neg accepted, dif_neg nextRefused]
    change ChallengeSlotImage.live (challengeObligationImage code family nextInputs (tracked family nextInputs newOriginal new)) =
        ChallengeSlotImage.live (challengeObligationImage code family inputs (tracked family inputs oldOriginal old)) ∧
      ChallengeRecordImage.mk newSlot.val .deferred
        (some (.live (challengeObligationImage code family nextInputs (tracked family nextInputs newOriginal new))))
        (.live (challengeObligationImage code family nextInputs (tracked family nextInputs newOriginal new)))
        (challengeEventImage code family nextInputs (.attempt newOriginal new newReceipt)) =
      ChallengeRecordImage.mk oldSlot.val .deferred
        (some (.live (challengeObligationImage code family inputs (tracked family inputs oldOriginal old))))
        (.live (challengeObligationImage code family inputs (tracked family inputs oldOriginal old)))
        (challengeEventImage code family inputs (.attempt oldOriginal old oldReceipt))
    rw [sameSlot, previous, same]
    exact ⟨rfl, rfl⟩

private theorem cross_state_images
    (old : (process family inputs oldOriginal).GeneratedState) (new : (process family nextInputs newOriginal).GeneratedState)
    (oldSlot : Fin old.current.slots.length) (newSlot : Fin new.current.slots.length)
    (oldObligation : AdmittedObligation (V family inputs)) (newObligation : AdmittedObligation (V family nextInputs))
    (oldPresent : old.current.slots.get oldSlot = .live oldObligation)
    (newPresent : new.current.slots.get newSlot = .live newObligation)
    (oldEvent : Boundary family inputs oldOriginal oldObligation) (newEvent : Boundary family nextInputs newOriginal newObligation)
    (before : challengeStateImage code family nextInputs new.current = challengeStateImage code family inputs old.current)
    (sameSlot : newSlot.val = oldSlot.val)
    (target : challengeSlotImage code family nextInputs (disposition family nextInputs newOriginal newEvent).targetSlot =
      challengeSlotImage code family inputs (disposition family inputs oldOriginal oldEvent).targetSlot)
    (record : challengeRecordImage code family nextInputs
        ((NativeResponsibilityProcess.Edge.cross (P := process family nextInputs newOriginal) newSlot newObligation newPresent newEvent).lifecycleEvent) =
      challengeRecordImage code family inputs
        ((NativeResponsibilityProcess.Edge.cross (P := process family inputs oldOriginal) oldSlot oldObligation oldPresent oldEvent).lifecycleEvent)) :
    challengeStateImage code family nextInputs (new.step (process family nextInputs newOriginal) (.cross newSlot newObligation newPresent newEvent)).current =
      challengeStateImage code family inputs (old.step (process family inputs oldOriginal) (.cross oldSlot oldObligation oldPresent oldEvent)).current := by
  rw [cross_image, cross_image, target, record, before, sameSlot]

theorem receive_match (old : Mandate.Challenge.History family inputs oldOriginal)
    (new : Mandate.Challenge.History family nextInputs newOriginal)
    (oldPosition : Position family inputs) (newPosition : Position family nextInputs)
    (matched : Match code family old new)
    (sources : readSources code family new newPosition = readSources code family old oldPosition) :
    Match code family (old.receive family inputs oldPosition) (new.receive family nextInputs newPosition) := by
  cases old with
  | closed oldState oldArchive oldSlots =>
    cases new with
    | closed newState newArchive newSlots => exact matched
    | pending newTarget newState newSlots => cases matched.pending
  | pending oldTarget oldState oldSlots =>
    cases new with
    | closed newState newArchive newSlots => cases matched.pending
    | pending newTarget newState newSlots =>
      have reaffirm := congrArg Prod.fst sources
      have attempt := congrArg Prod.snd sources
      dsimp only [readSources] at reaffirm attempt
      cases oldRead : readReconfirmation family inputs oldOriginal oldPosition <;>
        cases newRead : readReconfirmation family nextInputs newOriginal newPosition <;>
        (try rw [oldRead] at reaffirm) <;> (try rw [newRead] at reaffirm) <;>
        dsimp only [Option.map] at reaffirm
      · cases oldAttempt : readAttempt family inputs (oldTarget.claim family inputs) oldPosition <;>
          cases newAttempt : readAttempt family nextInputs (newTarget.claim family nextInputs) newPosition <;>
          (try rw [oldAttempt] at attempt) <;> (try rw [newAttempt] at attempt) <;>
          dsimp only [Option.map] at attempt
        · simpa only [Mandate.Challenge.History.receive, oldRead, newRead, oldAttempt, newAttempt] using matched
        · cases attempt
        · cases attempt
        · rename_i oldReceipt newReceipt
          have same := Option.some.inj attempt
          have item := attempt_items code family oldTarget newTarget oldReceipt newReceipt same
          let oldAddress : Fin oldState.current.slots.length := ⟨0, by rw [oldSlots]; exact Nat.zero_lt_succ 0⟩
          let newAddress : Fin newState.current.slots.length := ⟨0, by rw [newSlots]; exact Nat.zero_lt_succ 0⟩
          have oldPresent : oldState.current.slots.get oldAddress = .live (tracked family inputs oldOriginal oldTarget) := by simp [oldSlots, oldAddress]
          have newPresent : newState.current.slots.get newAddress = .live (tracked family nextInputs newOriginal newTarget) := by simp [newSlots, newAddress]
          have boundary := attempt_boundary_images code family oldTarget newTarget oldReceipt newReceipt
            oldState.current newState.current oldAddress newAddress rfl oldPresent newPresent same
          have after := cross_state_images code family oldState newState oldAddress newAddress _ _ oldPresent newPresent
            (.attempt oldTarget oldReceipt rfl) (.attempt newTarget newReceipt rfl) matched.state rfl boundary.1 boundary.2
          by_cases accepted : (Mandate.law base scope).Valid (oldReceipt.position.item family inputs).before (oldReceipt.position.item family inputs).request
          · have nextAccepted : (Mandate.law base scope).Valid (newReceipt.position.item family nextInputs).before (newReceipt.position.item family nextInputs).request := by rw [item]; exact accepted
            simp only [Mandate.Challenge.History.receive, oldRead, newRead, oldAttempt, newAttempt, dif_pos accepted, dif_pos nextAccepted]
            exact ⟨matched.original, after, rfl⟩
          · have nextRefused : ¬(Mandate.law base scope).Valid (newReceipt.position.item family nextInputs).before (newReceipt.position.item family nextInputs).request := by rw [item]; exact accepted
            simp only [Mandate.Challenge.History.receive, oldRead, newRead, oldAttempt, newAttempt, dif_neg accepted, dif_neg nextRefused]
            exact ⟨matched.original, after, matched.pending⟩
      · cases reaffirm
      · cases reaffirm
      · rename_i oldReceipt newReceipt
        have same := Option.some.inj reaffirm
        have parts := ChallengeEventImage.reaffirm.inj same
        have order := later_congr code family (oldTarget.claim family inputs) oldReceipt.target
          (newTarget.claim family nextInputs) newReceipt.target parts.2.2.1 parts.2.2.2
        by_cases later : Later family inputs (oldTarget.claim family inputs).position oldReceipt.target.position
        · have nextLater := order.mpr later
          let oldAddress : Fin oldState.current.slots.length := ⟨0, by rw [oldSlots]; exact Nat.zero_lt_succ 0⟩
          let newAddress : Fin newState.current.slots.length := ⟨0, by rw [newSlots]; exact Nat.zero_lt_succ 0⟩
          have oldPresent : oldState.current.slots.get oldAddress = .live (tracked family inputs oldOriginal oldTarget) := by simp [oldSlots, oldAddress]
          have newPresent : newState.current.slots.get newAddress = .live (tracked family nextInputs newOriginal newTarget) := by simp [newSlots, newAddress]
          have boundary := reaffirm_boundary_images code family oldTarget newTarget oldReceipt newReceipt later nextLater
            oldState.current newState.current oldAddress newAddress rfl oldPresent newPresent same
          have after := cross_state_images code family oldState newState oldAddress newAddress _ _ oldPresent newPresent
            (.reaffirm oldTarget oldReceipt later rfl) (.reaffirm newTarget newReceipt nextLater rfl) matched.state rfl boundary.1 boundary.2
          simp only [Mandate.Challenge.History.receive, oldRead, newRead, dif_pos later, dif_pos nextLater]
          exact ⟨matched.original, after, congrArg some parts.2.2.2⟩
        · have nextNotLater : ¬Later family nextInputs (newTarget.claim family nextInputs).position newReceipt.target.position :=
            fun nextLater => later (order.mp nextLater)
          simpa only [Mandate.Challenge.History.receive, oldRead, newRead, dif_neg later, dif_neg nextNotLater] using matched

variable (limit : Nat)
  (initial : (I family nextInputs).initial = (I family inputs).initial)
  (events : ∀ ordinal < limit,
    ProgrammeSource.rawEvent (I family nextInputs) (ProgrammeHistory.visitAt (I family inputs) ordinal).current =
      ProgrammeSource.rawEvent (I family inputs) (ProgrammeHistory.visitAt (I family inputs) ordinal).current)

include initial events in
theorem receive_from_prefix (old : Mandate.Challenge.History family inputs oldOriginal)
    (new : Mandate.Challenge.History family nextInputs newOriginal)
    (matched : Match code family old new) (oldPosition : Position family inputs) (newPosition : Position family nextInputs)
    (ordinal : newPosition.ordinal = oldPosition.ordinal) (index : newPosition.index.val = oldPosition.index.val)
    (inside : oldPosition.ordinal < limit) :
    Match code family (old.receive family inputs oldPosition) (new.receive family nextInputs newPosition) := by
  apply receive_match code family old new oldPosition newPosition matched
  have reads := ChallengeTransport.read_images code family limit initial events oldPosition newPosition ordinal index inside
  have position := ChallengeTransport.position_image_congr code family limit initial events oldPosition newPosition ordinal index inside
  cases old with
  | closed oldState oldArchive oldSlots =>
    cases new with
    | closed newState newArchive newSlots => rfl
    | pending newTarget newState newSlots => cases matched.pending
  | pending oldTarget oldState oldSlots =>
    cases new with
    | closed newState newArchive newSlots => cases matched.pending
    | pending newTarget newState newSlots =>
      exact Prod.ext (reconfirmation_sources code family oldTarget newTarget oldPosition newPosition
          matched.original (Option.some.inj matched.pending) reads)
        (attempt_sources code family oldTarget newTarget oldPosition newPosition
          matched.original (Option.some.inj matched.pending) position)

include initial events in
theorem positions_match (oldPositions : List (Position family inputs)) (newPositions : List (Position family nextInputs))
    (pairs : List.Forall₂ (fun old new => new.ordinal = old.ordinal ∧ new.index.val = old.index.val ∧ old.ordinal < limit) oldPositions newPositions)
    (old : Mandate.Challenge.History family inputs oldOriginal) (new : Mandate.Challenge.History family nextInputs newOriginal)
    (matched : Match code family old new) :
    Match code family (oldPositions.foldl (Mandate.Challenge.History.receive family inputs) old)
      (newPositions.foldl (Mandate.Challenge.History.receive family nextInputs) new) := by
  induction pairs generalizing old new with
  | nil => exact matched
  | cons positionPair pairs ih =>
    exact ih (old.receive family inputs _) (new.receive family nextInputs _)
      (receive_from_prefix code family limit initial events old new matched _ _ positionPair.1 positionPair.2.1 positionPair.2.2)

private theorem positions_coordinates (atInput : Index) (ordinal index : Nat)
    (inside : index < (positionsAt family atInput ordinal).length) :
    ((positionsAt family atInput ordinal)[index]).ordinal = ordinal ∧
      ((positionsAt family atInput ordinal)[index]).index.val = index := by
  have actual := List.getElem_map
    (l := List.finRange (Institutions.Capitalism.Universal.Source.ProgrammeFace.Registered.traceItems
      (I family atInput) (ProgrammeHistory.visitAt (I family atInput) ordinal).current).length)
    (i := index) (h := inside) (fun key => (⟨ordinal, key⟩ : Position family atInput))
  refine ⟨congrArg Position.ordinal actual, ?_⟩
  simpa only [positionsAt, List.getElem_finRange, Fin.val_cast] using congrArg (fun position => position.index.val) actual

include initial events in
private theorem visit_positions (ordinal : Nat) (inside : ordinal < limit) :
    List.Forall₂ (fun old new => new.ordinal = old.ordinal ∧ new.index.val = old.index.val ∧ old.ordinal < limit)
      (positionsAt family inputs ordinal) (positionsAt family nextInputs ordinal) := by
  apply List.forall₂_of_length_eq_of_get
  · simpa only [positionsAt, List.length_map, List.length_finRange] using
      (congrArg List.length (ChallengeTransport.items family limit initial events ordinal inside)).symm
  · intro index oldBound newBound
    have old := positions_coordinates family inputs ordinal index oldBound
    have new := positions_coordinates family nextInputs ordinal index newBound
    refine ⟨new.1.trans old.1.symm, new.2.trans old.2.symm, ?_⟩
    simpa only [List.get_eq_getElem] using (show ((positionsAt family inputs ordinal)[index]).ordinal < limit by rw [old.1]; exact inside)

include initial events in
theorem through_match (count : Nat) (bounded : count ≤ limit)
    (original : challengeImage code family nextInputs newOriginal = challengeImage code family inputs oldOriginal) :
    Match code family (Mandate.Challenge.through family inputs oldOriginal count)
      (Mandate.Challenge.through family nextInputs newOriginal count) := by
  induction count with
  | zero => exact initial_match code family original
  | succ count ih =>
    exact positions_match code family limit initial events _ _ (visit_positions family limit initial events count (by omega))
      _ _ (ih (by omega))

include initial events in
private theorem rows_of_claim_images (count : Nat) (bounded : count ≤ limit)
    (oldClaims : List (Claim family inputs)) (newClaims : List (Claim family nextInputs))
    (same : newClaims.map (challengeImage code family nextInputs) = oldClaims.map (challengeImage code family inputs)) :
    newClaims.map (fun claim => (challengeImage code family nextInputs claim,
        challengeStateImage code family nextInputs (Mandate.Challenge.through family nextInputs claim count).state.current)) =
      oldClaims.map (fun claim => (challengeImage code family inputs claim,
        challengeStateImage code family inputs (Mandate.Challenge.through family inputs claim count).state.current)) := by
  induction oldClaims generalizing newClaims with
  | nil =>
    cases newClaims with
    | nil => rfl
    | cons => cases same
  | cons old rest ih =>
    cases newClaims with
    | nil => cases same
    | cons new later =>
      have parts := List.cons.inj same
      exact congrArg₂ List.cons (Prod.ext parts.1 (through_match code family limit initial events count bounded parts.1).state)
        (ih later parts.2)

include initial events in
theorem census_images (count : Nat) (bounded : count ≤ limit) :
    (Mandate.Challenge.recordsAt family nextInputs count).map (fun record =>
        (challengeImage code family nextInputs record.1, challengeStateImage code family nextInputs record.2.state.current)) =
      (Mandate.Challenge.recordsAt family inputs count).map (fun record =>
        (challengeImage code family inputs record.1, challengeStateImage code family inputs record.2.state.current)) := by
  simp only [Mandate.Challenge.recordsAt, List.map_flatMap, List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro ordinal member
  exact rows_of_claim_images code family limit initial events count bounded _ _
    (ChallengeTransport.claims_images code family limit initial events ordinal (Nat.lt_of_lt_of_le (List.mem_range.mp member) bounded))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.LocalLifecycle
