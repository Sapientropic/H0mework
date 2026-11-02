import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.LocalLifecycle

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.CrossMigration

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Mandate.Challenge

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port (Mandate.State Party Technology) Instrument)
  {base : RawLaw Party Good Port Technology Instrument} {scope : Mandate.Scope}
  {Index : Type} (family : ProgrammeFamily base scope Index)
  {oldOrigin newOrigin inputs nextInputs : Index}
  {oldOriginal : Claim family oldOrigin} {newOriginal : Claim family newOrigin}

structure Match (old : Cross.History family oldOriginal inputs) (new : Cross.History family newOriginal nextInputs) : Prop where
  original : challengeImage code family newOrigin newOriginal = challengeImage code family oldOrigin oldOriginal
  state : challengeStateImage code family newOrigin new.state.current = challengeStateImage code family oldOrigin old.state.current
  pending : ChallengeLifecycle.pendingImage code family new = ChallengeLifecycle.pendingImage code family old

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
    (oldTarget : Cross.Target family oldOriginal inputs) (newTarget : Cross.Target family newOriginal nextInputs)
    (original : challengeImage code family newOrigin newOriginal = challengeImage code family oldOrigin oldOriginal)
    (target : challengeImage code family nextInputs newTarget.claim =
      challengeImage code family inputs oldTarget.claim) :
    challengeObligationImage code family newOrigin (Cross.tracked family newTarget) =
      challengeObligationImage code family oldOrigin (Cross.tracked family oldTarget) := by
  have snapshot := congrArg (fun item => item.before.technology)
    (claim_items code family _ _ target)
  change newTarget.claim.snapshot family nextInputs = oldTarget.claim.snapshot family inputs at snapshot
  change ChallengeObligationImage.mk (.birth (challengeImage code family newOrigin newOriginal))
      (challengeImage code family newOrigin newOriginal).actor (challengeImage code family newOrigin newOriginal).position.origin
      (challengeImage code family newOrigin newOriginal) (newTarget.claim.snapshot family nextInputs) (challengeImage code family newOrigin newOriginal).actor
      (taskImage scope.task) (challengeImage code family newOrigin newOriginal).position.origin
      (challengeImage code family newOrigin newOriginal).position.origin =
    ChallengeObligationImage.mk (.birth (challengeImage code family oldOrigin oldOriginal))
      (challengeImage code family oldOrigin oldOriginal).actor (challengeImage code family oldOrigin oldOriginal).position.origin
      (challengeImage code family oldOrigin oldOriginal) (oldTarget.claim.snapshot family inputs)
      (challengeImage code family oldOrigin oldOriginal).actor (taskImage scope.task)
      (challengeImage code family oldOrigin oldOriginal).position.origin (challengeImage code family oldOrigin oldOriginal).position.origin
  rw [original, snapshot]

private theorem cross_image {originInputs : Index} {original : Claim family originInputs} (state : (Cross.process family original).GeneratedState)
    (slot : Fin state.current.slots.length) (obligation : AdmittedObligation (V family originInputs))
    (present : state.current.slots.get slot = .live obligation) (event : Cross.Boundary family original obligation) :
    challengeStateImage code family originInputs
        (state.step (Cross.process family original) (.cross slot obligation present event)).current =
      ⟨(challengeStateImage code family originInputs state.current).slots.set slot.val
          (challengeSlotImage code family originInputs (Cross.disposition family original event).targetSlot),
        (challengeStateImage code family originInputs state.current).history ++
          [challengeRecordImage code family originInputs ((NativeResponsibilityProcess.Edge.cross (P := Cross.process family original) slot obligation present event).lifecycleEvent)]⟩ := by
  change ChallengeStateImage.mk ((state.current.slots.set slot.val _).map _) ((state.current.history ++ [_]).map _) = _
  rw [List.map_set, List.map_append, List.map_cons, List.map_nil]
  rfl

private theorem later_congr (oldFirst oldLast : Claim family inputs) (newFirst newLast : Claim family nextInputs)
    (first : challengeImage code family nextInputs newFirst = challengeImage code family inputs oldFirst)
    (last : challengeImage code family nextInputs newLast = challengeImage code family inputs oldLast) :
    Later family nextInputs newFirst.position newLast.position ↔ Later family inputs oldFirst.position oldLast.position := by
  have a := claim_coordinates code family oldFirst newFirst first
  have b := claim_coordinates code family oldLast newLast last
  simp only [Later, a.1, a.2, b.1, b.2]

private theorem reconfirmation_sources
    (oldTarget : Cross.Target family oldOriginal inputs) (newTarget : Cross.Target family newOriginal nextInputs)
    (oldPosition : Position family inputs) (newPosition : Position family nextInputs)
    (original : challengeImage code family newOrigin newOriginal = challengeImage code family oldOrigin oldOriginal)
    (target : challengeImage code family nextInputs newTarget.claim =
      challengeImage code family inputs oldTarget.claim)
    (reads : (read family nextInputs newPosition).map (challengeImage code family nextInputs) =
      (read family inputs oldPosition).map (challengeImage code family inputs)) :
    (Cross.readReconfirmation family newTarget newPosition).map (fun receipt =>
        challengeEventImage code family newOrigin (.remoteReaffirm newOriginal nextInputs newTarget receipt)) =
      (Cross.readReconfirmation family oldTarget oldPosition).map (fun receipt =>
        challengeEventImage code family oldOrigin (.remoteReaffirm oldOriginal inputs oldTarget receipt)) := by
  unfold Cross.readReconfirmation
  cases oldRead : read family inputs oldPosition <;> cases newRead : read family nextInputs newPosition <;>
    simp only [oldRead, newRead, Option.map_none, Option.map_some] at reads ⊢
  · cases reads
  · cases reads
  · rename_i oldClaim newClaim
    have claim := Option.some.inj reads
    have order := later_congr code family oldTarget.claim oldClaim newTarget.claim newClaim target claim
    have signer := congrArg (fun item => item.request.signer) (claim_items code family oldClaim newClaim claim)
    have firstSigner := congrArg (fun item => item.request.signer) (claim_items code family oldTarget.claim newTarget.claim target)
    change newClaim.signer family nextInputs = oldClaim.signer family inputs at signer
    change newTarget.claim.signer family nextInputs = oldTarget.claim.signer family inputs at firstSigner
    have valid : (Later family nextInputs newTarget.claim.position newClaim.position ∧
        newClaim.signer family nextInputs = newTarget.claim.signer family nextInputs) ↔
      (Later family inputs oldTarget.claim.position oldClaim.position ∧ oldClaim.signer family inputs = oldTarget.claim.signer family inputs) := by
      rw [order, signer, firstSigner]
    by_cases checked : Later family inputs oldTarget.claim.position oldClaim.position ∧ oldClaim.signer family inputs = oldTarget.claim.signer family inputs
    · rw [dif_pos checked, dif_pos (valid.mpr checked)]
      simp only [Option.map_some, challengeEventImage]
      rw [original, target, claim]
    · rw [dif_neg checked, dif_neg (fun accepted => checked (valid.mp accepted))]
      rfl

private theorem attempt_sources
    (oldTarget : Cross.Target family oldOriginal inputs) (newTarget : Cross.Target family newOriginal nextInputs)
    (oldPosition : Position family inputs) (newPosition : Position family nextInputs)
    (original : challengeImage code family newOrigin newOriginal = challengeImage code family oldOrigin oldOriginal)
    (target : challengeImage code family nextInputs newTarget.claim =
      challengeImage code family inputs oldTarget.claim)
    (position : positionImage code family nextInputs newPosition = positionImage code family inputs oldPosition) :
    (readAttempt family nextInputs newTarget.claim newPosition).map (fun receipt =>
        challengeEventImage code family newOrigin (.remoteAttempt newOriginal nextInputs newTarget receipt)) =
      (readAttempt family inputs oldTarget.claim oldPosition).map (fun receipt =>
        challengeEventImage code family oldOrigin (.remoteAttempt oldOriginal inputs oldTarget receipt)) := by
  have coordinates := claim_coordinates code family _ _ target
  have positionOrdinal := congrArg PositionImage.ordinal position
  change newPosition.ordinal = oldPosition.ordinal at positionOrdinal
  have positionIndex := congrArg (fun image => image.origin.traceIndex) position
  change some newPosition.index.val = some oldPosition.index.val at positionIndex
  have index := Option.some.inj positionIndex
  have item := (equal_position_images_recover_the_actual_item code family inputs nextInputs oldPosition newPosition position).2
  have snapshot := congrArg (fun item => item.before.technology) (claim_items code family _ _ target)
  have valid : (Later family nextInputs newTarget.claim.position newPosition ∧
      Withdrawal (scope := scope) (newPosition.item family nextInputs).before (newPosition.item family nextInputs).request ∧
      (newPosition.item family nextInputs).before.technology = newTarget.claim.snapshot family nextInputs) ↔
    (Later family inputs oldTarget.claim.position oldPosition ∧
      Withdrawal (scope := scope) (oldPosition.item family inputs).before (oldPosition.item family inputs).request ∧
      (oldPosition.item family inputs).before.technology = oldTarget.claim.snapshot family inputs) := by
    simp only [Later, Claim.snapshot, coordinates.1, coordinates.2, positionOrdinal, index, item, snapshot]
  unfold readAttempt
  by_cases checked : Later family inputs oldTarget.claim.position oldPosition ∧
      Withdrawal (scope := scope) (oldPosition.item family inputs).before (oldPosition.item family inputs).request ∧
      (oldPosition.item family inputs).before.technology = oldTarget.claim.snapshot family inputs
  · rw [dif_pos checked, dif_pos (valid.mpr checked)]
    simp only [Option.map_some, challengeEventImage]
    rw [original, target, position, item]
  · rw [dif_neg checked, dif_neg (fun accepted => checked (valid.mp accepted))]
    rfl

private theorem reaffirm_boundary_images
    (old : Cross.Target family oldOriginal inputs) (new : Cross.Target family newOriginal nextInputs)
    (oldReceipt : Cross.Reconfirmation family old) (newReceipt : Cross.Reconfirmation family new)
    (oldState : ResponsibilityState (V family oldOrigin)) (newState : ResponsibilityState (V family newOrigin))
    (oldSlot : Fin oldState.slots.length) (newSlot : Fin newState.slots.length)
    (sameSlot : newSlot.val = oldSlot.val)
    (oldPresent : oldState.slots.get oldSlot = .live (Cross.tracked family old))
    (newPresent : newState.slots.get newSlot = .live (Cross.tracked family new))
    (same : challengeEventImage code family newOrigin (.remoteReaffirm newOriginal nextInputs new newReceipt) =
      challengeEventImage code family oldOrigin (.remoteReaffirm oldOriginal inputs old oldReceipt)) :
    challengeSlotImage code family newOrigin (Cross.disposition family newOriginal (.reaffirm new newReceipt rfl)).targetSlot =
        challengeSlotImage code family oldOrigin (Cross.disposition family oldOriginal (.reaffirm old oldReceipt rfl)).targetSlot ∧
      challengeRecordImage code family newOrigin ((NativeResponsibilityProcess.Edge.cross (P := Cross.process family newOriginal) newSlot (Cross.tracked family new) newPresent (.reaffirm new newReceipt rfl)).lifecycleEvent) =
      challengeRecordImage code family oldOrigin ((NativeResponsibilityProcess.Edge.cross (P := Cross.process family oldOriginal) oldSlot (Cross.tracked family old) oldPresent (.reaffirm old oldReceipt rfl)).lifecycleEvent) := by
  have parts := ChallengeEventImage.reaffirm.inj same
  have previous := tracked_images code family old new parts.2.1 parts.2.2.1
  have next := tracked_images code family (oldReceipt.target family) (newReceipt.target family) parts.2.1 parts.2.2.2
  change ChallengeSlotImage.live (challengeObligationImage code family newOrigin (Cross.tracked family (newReceipt.target family))) =
        ChallengeSlotImage.live (challengeObligationImage code family oldOrigin (Cross.tracked family (oldReceipt.target family))) ∧
      ChallengeRecordImage.mk newSlot.val .progressed
        (some (.live (challengeObligationImage code family newOrigin (Cross.tracked family new))))
        (.live (challengeObligationImage code family newOrigin (Cross.tracked family (newReceipt.target family))))
        (challengeEventImage code family newOrigin (.remoteReaffirm newOriginal nextInputs new newReceipt)) =
      ChallengeRecordImage.mk oldSlot.val .progressed
        (some (.live (challengeObligationImage code family oldOrigin (Cross.tracked family old))))
        (.live (challengeObligationImage code family oldOrigin (Cross.tracked family (oldReceipt.target family))))
        (challengeEventImage code family oldOrigin (.remoteReaffirm oldOriginal inputs old oldReceipt))
  rw [sameSlot, previous, next, same]
  exact ⟨rfl, rfl⟩

private theorem attempt_items (old : Cross.Target family oldOriginal inputs) (new : Cross.Target family newOriginal nextInputs)
    (oldReceipt : Attempt family inputs old.claim) (newReceipt : Attempt family nextInputs new.claim)
    (same : challengeEventImage code family newOrigin (.remoteAttempt newOriginal nextInputs new newReceipt) =
      challengeEventImage code family oldOrigin (.remoteAttempt oldOriginal inputs old oldReceipt)) :
    newReceipt.position.item family nextInputs = oldReceipt.position.item family inputs := by
  have parts := ChallengeEventImage.attempt.inj same
  exact (equal_position_images_recover_the_actual_item code family inputs nextInputs _ _ parts.2.2.2.1).2

private theorem attempt_boundary_images
    (old : Cross.Target family oldOriginal inputs) (new : Cross.Target family newOriginal nextInputs)
    (oldReceipt : Attempt family inputs old.claim) (newReceipt : Attempt family nextInputs new.claim)
    (oldState : ResponsibilityState (V family oldOrigin)) (newState : ResponsibilityState (V family newOrigin))
    (oldSlot : Fin oldState.slots.length) (newSlot : Fin newState.slots.length)
    (sameSlot : newSlot.val = oldSlot.val)
    (oldPresent : oldState.slots.get oldSlot = .live (Cross.tracked family old))
    (newPresent : newState.slots.get newSlot = .live (Cross.tracked family new))
    (same : challengeEventImage code family newOrigin (.remoteAttempt newOriginal nextInputs new newReceipt) =
      challengeEventImage code family oldOrigin (.remoteAttempt oldOriginal inputs old oldReceipt)) :
    challengeSlotImage code family newOrigin (Cross.disposition family newOriginal (.attempt new newReceipt rfl)).targetSlot =
        challengeSlotImage code family oldOrigin (Cross.disposition family oldOriginal (.attempt old oldReceipt rfl)).targetSlot ∧
      challengeRecordImage code family newOrigin ((NativeResponsibilityProcess.Edge.cross (P := Cross.process family newOriginal) newSlot (Cross.tracked family new) newPresent (.attempt new newReceipt rfl)).lifecycleEvent) =
      challengeRecordImage code family oldOrigin ((NativeResponsibilityProcess.Edge.cross (P := Cross.process family oldOriginal) oldSlot (Cross.tracked family old) oldPresent (.attempt old oldReceipt rfl)).lifecycleEvent) := by
  have parts := ChallengeEventImage.attempt.inj same
  have previous := tracked_images code family old new parts.2.1 parts.2.2.1
  have item := attempt_items code family old new oldReceipt newReceipt same
  unfold Cross.disposition
  by_cases accepted : (Mandate.law base scope).Valid (oldReceipt.position.item family inputs).before (oldReceipt.position.item family inputs).request
  · have nextAccepted : (Mandate.law base scope).Valid (newReceipt.position.item family nextInputs).before (newReceipt.position.item family nextInputs).request := by rw [item]; exact accepted
    simp only [NativeResponsibilityProcess.Edge.lifecycleEvent, Cross.process, Cross.disposition, dif_pos accepted, dif_pos nextAccepted]
    change ChallengeSlotImage.terminal (challengeObligationImage code family newOrigin (Cross.tracked family new))
          (challengeEventImage code family newOrigin (.remoteAttempt newOriginal nextInputs new newReceipt)) =
        ChallengeSlotImage.terminal (challengeObligationImage code family oldOrigin (Cross.tracked family old))
          (challengeEventImage code family oldOrigin (.remoteAttempt oldOriginal inputs old oldReceipt)) ∧
      ChallengeRecordImage.mk newSlot.val .obligationTerminal
        (some (.live (challengeObligationImage code family newOrigin (Cross.tracked family new))))
        (.terminal (challengeObligationImage code family newOrigin (Cross.tracked family new))
          (challengeEventImage code family newOrigin (.remoteAttempt newOriginal nextInputs new newReceipt)))
        (challengeEventImage code family newOrigin (.remoteAttempt newOriginal nextInputs new newReceipt)) =
      ChallengeRecordImage.mk oldSlot.val .obligationTerminal
        (some (.live (challengeObligationImage code family oldOrigin (Cross.tracked family old))))
        (.terminal (challengeObligationImage code family oldOrigin (Cross.tracked family old))
          (challengeEventImage code family oldOrigin (.remoteAttempt oldOriginal inputs old oldReceipt)))
        (challengeEventImage code family oldOrigin (.remoteAttempt oldOriginal inputs old oldReceipt))
    rw [sameSlot, previous, same]
    exact ⟨rfl, rfl⟩
  · have nextRefused : ¬(Mandate.law base scope).Valid (newReceipt.position.item family nextInputs).before (newReceipt.position.item family nextInputs).request := by rw [item]; exact accepted
    simp only [NativeResponsibilityProcess.Edge.lifecycleEvent, Cross.process, Cross.disposition, dif_neg accepted, dif_neg nextRefused]
    change ChallengeSlotImage.live (challengeObligationImage code family newOrigin (Cross.tracked family new)) =
        ChallengeSlotImage.live (challengeObligationImage code family oldOrigin (Cross.tracked family old)) ∧
      ChallengeRecordImage.mk newSlot.val .deferred
        (some (.live (challengeObligationImage code family newOrigin (Cross.tracked family new))))
        (.live (challengeObligationImage code family newOrigin (Cross.tracked family new)))
        (challengeEventImage code family newOrigin (.remoteAttempt newOriginal nextInputs new newReceipt)) =
      ChallengeRecordImage.mk oldSlot.val .deferred
        (some (.live (challengeObligationImage code family oldOrigin (Cross.tracked family old))))
        (.live (challengeObligationImage code family oldOrigin (Cross.tracked family old)))
        (challengeEventImage code family oldOrigin (.remoteAttempt oldOriginal inputs old oldReceipt))
    rw [sameSlot, previous, same]
    exact ⟨rfl, rfl⟩

private theorem cross_state_image
    (old : (Cross.process family oldOriginal).GeneratedState) (new : (Cross.process family newOriginal).GeneratedState)
    (oldSlot : Fin old.current.slots.length) (newSlot : Fin new.current.slots.length)
    (oldObligation : AdmittedObligation (V family oldOrigin)) (newObligation : AdmittedObligation (V family newOrigin))
    (oldPresent : old.current.slots.get oldSlot = .live oldObligation)
    (newPresent : new.current.slots.get newSlot = .live newObligation)
    (oldEvent : Cross.Boundary family oldOriginal oldObligation) (newEvent : Cross.Boundary family newOriginal newObligation)
    (before : challengeStateImage code family newOrigin new.current = challengeStateImage code family oldOrigin old.current)
    (sameSlot : newSlot.val = oldSlot.val)
    (target : challengeSlotImage code family newOrigin (Cross.disposition family newOriginal newEvent).targetSlot =
      challengeSlotImage code family oldOrigin (Cross.disposition family oldOriginal oldEvent).targetSlot)
    (record : challengeRecordImage code family newOrigin
        ((NativeResponsibilityProcess.Edge.cross (P := Cross.process family newOriginal) newSlot newObligation newPresent newEvent).lifecycleEvent) =
      challengeRecordImage code family oldOrigin
        ((NativeResponsibilityProcess.Edge.cross (P := Cross.process family oldOriginal) oldSlot oldObligation oldPresent oldEvent).lifecycleEvent)) :
    challengeStateImage code family newOrigin (new.step (Cross.process family newOriginal) (.cross newSlot newObligation newPresent newEvent)).current =
      challengeStateImage code family oldOrigin (old.step (Cross.process family oldOriginal) (.cross oldSlot oldObligation oldPresent oldEvent)).current := by
  rw [cross_image, cross_image, target, record, before, sameSlot]

theorem receive_match (old : Cross.History family oldOriginal inputs) (new : Cross.History family newOriginal nextInputs)
    (oldPosition : Position family inputs) (newPosition : Position family nextInputs)
    (matched : Match code family old new)
    (sources : ChallengeLifecycle.readSources code family new newPosition = ChallengeLifecycle.readSources code family old oldPosition) :
    Match code family (old.receive family oldPosition) (new.receive family newPosition) := by
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
      dsimp only [ChallengeLifecycle.readSources] at reaffirm attempt
      unfold ChallengeTransport.reconfirmationSource at reaffirm
      unfold ChallengeTransport.attemptSource at attempt
      cases oldRead : Cross.readReconfirmation family oldTarget oldPosition <;>
        cases newRead : Cross.readReconfirmation family newTarget newPosition <;>
        (try rw [oldRead] at reaffirm) <;> (try rw [newRead] at reaffirm) <;>
        dsimp only [Option.map] at reaffirm
      · cases oldAttempt : readAttempt family inputs oldTarget.claim oldPosition <;>
          cases newAttempt : readAttempt family nextInputs newTarget.claim newPosition <;>
          (try rw [oldAttempt] at attempt) <;> (try rw [newAttempt] at attempt) <;>
          dsimp only [Option.map] at attempt
        · simpa only [Cross.History.receive, oldRead, newRead, oldAttempt, newAttempt] using matched
        · cases attempt
        · cases attempt
        · rename_i oldReceipt newReceipt
          have same := Option.some.inj attempt
          have item := attempt_items code family oldTarget newTarget oldReceipt newReceipt same
          let oldAddress : Fin oldState.current.slots.length := ⟨0, by rw [oldSlots]; exact Nat.zero_lt_succ 0⟩
          let newAddress : Fin newState.current.slots.length := ⟨0, by rw [newSlots]; exact Nat.zero_lt_succ 0⟩
          have oldPresent : oldState.current.slots.get oldAddress = .live (Cross.tracked family oldTarget) := by simp [oldSlots, oldAddress]
          have newPresent : newState.current.slots.get newAddress = .live (Cross.tracked family newTarget) := by simp [newSlots, newAddress]
          have boundary := attempt_boundary_images code family oldTarget newTarget oldReceipt newReceipt
            oldState.current newState.current oldAddress newAddress rfl oldPresent newPresent same
          have after := cross_state_image code family oldState newState oldAddress newAddress _ _ oldPresent newPresent
            (.attempt oldTarget oldReceipt rfl) (.attempt newTarget newReceipt rfl) matched.state rfl boundary.1 boundary.2
          by_cases accepted : (Mandate.law base scope).Valid (oldReceipt.position.item family inputs).before (oldReceipt.position.item family inputs).request
          · have nextAccepted : (Mandate.law base scope).Valid (newReceipt.position.item family nextInputs).before (newReceipt.position.item family nextInputs).request := by rw [item]; exact accepted
            simp only [Cross.History.receive, oldRead, newRead, oldAttempt, newAttempt, dif_pos accepted, dif_pos nextAccepted]
            exact ⟨matched.original, after, rfl⟩
          · have nextRefused : ¬(Mandate.law base scope).Valid (newReceipt.position.item family nextInputs).before (newReceipt.position.item family nextInputs).request := by rw [item]; exact accepted
            simp only [Cross.History.receive, oldRead, newRead, oldAttempt, newAttempt, dif_neg accepted, dif_neg nextRefused]
            exact ⟨matched.original, after, matched.pending⟩
      · cases reaffirm
      · cases reaffirm
      · rename_i oldReceipt newReceipt
        have same := Option.some.inj reaffirm
        let oldAddress : Fin oldState.current.slots.length := ⟨0, by rw [oldSlots]; exact Nat.zero_lt_succ 0⟩
        let newAddress : Fin newState.current.slots.length := ⟨0, by rw [newSlots]; exact Nat.zero_lt_succ 0⟩
        have oldPresent : oldState.current.slots.get oldAddress = .live (Cross.tracked family oldTarget) := by simp [oldSlots, oldAddress]
        have newPresent : newState.current.slots.get newAddress = .live (Cross.tracked family newTarget) := by simp [newSlots, newAddress]
        have boundary := reaffirm_boundary_images code family oldTarget newTarget oldReceipt newReceipt
          oldState.current newState.current oldAddress newAddress rfl oldPresent newPresent same
        have after := cross_state_image code family oldState newState oldAddress newAddress _ _ oldPresent newPresent
          (.reaffirm oldTarget oldReceipt rfl) (.reaffirm newTarget newReceipt rfl) matched.state rfl boundary.1 boundary.2
        simp only [Cross.History.receive, oldRead, newRead]
        exact ⟨matched.original, after, congrArg some (ChallengeEventImage.reaffirm.inj same).2.2.2⟩

variable (limit : Nat)
  (initial : (I family nextInputs).initial = (I family inputs).initial)
  (events : ∀ ordinal < limit,
    ProgrammeSource.rawEvent (I family nextInputs) (ProgrammeHistory.visitAt (I family inputs) ordinal).current =
      ProgrammeSource.rawEvent (I family inputs) (ProgrammeHistory.visitAt (I family inputs) ordinal).current)

include initial events in
theorem read_sources_congr (old : Cross.History family oldOriginal inputs) (new : Cross.History family newOriginal nextInputs)
    (matched : Match code family old new) (within : Cross.Programme.Within family limit old)
    (oldPosition : Position family inputs) (newPosition : Position family nextInputs)
    (ordinal : newPosition.ordinal = oldPosition.ordinal) (index : newPosition.index.val = oldPosition.index.val)
    (inside : oldPosition.ordinal < limit) :
    ChallengeLifecycle.readSources code family new newPosition = ChallengeLifecycle.readSources code family old oldPosition := by
  cases old with
  | closed oldState oldArchive oldSlots =>
    cases new with
    | closed newState newArchive newSlots => rfl
    | pending newTarget newState newSlots => cases matched.pending
  | pending oldTarget oldState oldSlots =>
    cases new with
    | closed newState newArchive newSlots => cases matched.pending
    | pending newTarget newState newSlots =>
      have target := Option.some.inj matched.pending
      exact Prod.ext
        (reconfirmation_sources code family oldTarget newTarget oldPosition newPosition matched.original target
          (ChallengeTransport.read_images code family limit initial events oldPosition newPosition ordinal index inside))
        (attempt_sources code family oldTarget newTarget oldPosition newPosition matched.original target
          (ChallengeTransport.position_image_congr code family limit initial events oldPosition newPosition ordinal index inside))

include initial events in
theorem receive_from_prefix (old : Cross.History family oldOriginal inputs) (new : Cross.History family newOriginal nextInputs)
    (matched : Match code family old new) (within : Cross.Programme.Within family limit old)
    (oldPosition : Position family inputs) (newPosition : Position family nextInputs)
    (ordinal : newPosition.ordinal = oldPosition.ordinal) (index : newPosition.index.val = oldPosition.index.val)
    (inside : oldPosition.ordinal < limit) :
    Match code family (old.receive family oldPosition) (new.receive family newPosition) :=
  receive_match code family old new oldPosition newPosition matched
    (read_sources_congr code family limit initial events old new matched within oldPosition newPosition ordinal index inside)

include initial events in
theorem positions_match (oldPositions : List (Position family inputs)) (newPositions : List (Position family nextInputs))
    (pairs : List.Forall₂ (fun old new => new.ordinal = old.ordinal ∧ new.index.val = old.index.val ∧ old.ordinal < limit) oldPositions newPositions)
    (old : Cross.History family oldOriginal inputs) (new : Cross.History family newOriginal nextInputs)
    (matched : Match code family old new) (within : Cross.Programme.Within family limit old) :
    Match code family (oldPositions.foldl (Cross.History.receive family) old) (newPositions.foldl (Cross.History.receive family) new) := by
  induction pairs generalizing old new with
  | nil => exact matched
  | cons positionPair pairs ih =>
    exact ih (old.receive family _) (new.receive family _)
      (receive_from_prefix code family limit initial events old new matched within _ _ positionPair.1 positionPair.2.1 positionPair.2.2)
      (Cross.Programme.receive_within family limit old _ within positionPair.2.2)

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
theorem visits_match (visits : List Nat) (bounded : ∀ ordinal ∈ visits, ordinal < limit)
    (old : Cross.History family oldOriginal inputs) (new : Cross.History family newOriginal nextInputs)
    (matched : Match code family old new) (within : Cross.Programme.Within family limit old) :
    Match code family
      (visits.foldl (fun history ordinal => (positionsAt family inputs ordinal).foldl (Cross.History.receive family) history) old)
      (visits.foldl (fun history ordinal => (positionsAt family nextInputs ordinal).foldl (Cross.History.receive family) history) new) := by
  induction visits generalizing old new with
  | nil => exact matched
  | cons ordinal rest ih =>
    have inside := bounded ordinal (by simp)
    have after := positions_match code family limit initial events _ _ (visit_positions family limit initial events ordinal inside) old new matched within
    apply ih (fun later member => bounded later (List.mem_cons_of_mem _ member)) _ _ after
    apply Cross.Programme.fold_within family limit old _ within
    intro position member
    obtain ⟨index, _, same⟩ := List.mem_map.mp member
    cases same
    exact inside

include initial events in
theorem continue_match (start count : Nat) (bounded : start + count ≤ limit)
    (old : Cross.History family oldOriginal inputs) (new : Cross.History family newOriginal nextInputs)
    (matched : Match code family old new) (within : Cross.Programme.Within family limit old) :
    Match code family (Cross.Programme.continueFrom family old start count) (Cross.Programme.continueFrom family new start count) := by
  apply visits_match code family limit initial events _ _ old new matched within
  intro ordinal member
  obtain ⟨offset, before, same⟩ := List.mem_map.mp member
  cases same
  have inside := List.mem_range.mp before
  omega


theorem inherit_match
    (old : Mandate.Challenge.History family oldOrigin oldOriginal)
    (new : Mandate.Challenge.History family newOrigin newOriginal)
    (matched : LocalLifecycle.Match code family old new) :
    Match code family (Cross.History.inherit family old) (Cross.History.inherit family new) := by
  have oldState : (Cross.History.inherit family old).state.current = old.state.current := by
    cases old with
    | closed state archive slots => rfl
    | pending target state slots => cases target <;> rfl
  have newState : (Cross.History.inherit family new).state.current = new.state.current := by
    cases new with
    | closed state archive slots => rfl
    | pending target state slots => cases target <;> rfl
  have oldPending : ChallengeLifecycle.pendingImage code family (Cross.History.inherit family old) =
      LocalLifecycle.pendingImage code family old := by
    cases old with
    | closed state archive slots => rfl
    | pending target state slots => cases target <;> rfl
  have newPending : ChallengeLifecycle.pendingImage code family (Cross.History.inherit family new) =
      LocalLifecycle.pendingImage code family new := by
    cases new with
    | closed state archive slots => rfl
    | pending target state slots => cases target <;> rfl
  exact ⟨matched.original, by rw [oldState,newState];exact matched.state,
    newPending.trans (matched.pending.trans oldPending.symm)⟩

private theorem transport_pending {origin atInput toInput : Index} {original : Claim family origin}
    (history : Cross.History family original atInput) (count : Nat)
    (within : Cross.Programme.Within family count history)
    (initial : (I family toInput).initial = (I family atInput).initial)
    (events : ∀ ordinal < count,
      ProgrammeSource.rawEvent (I family toInput) (ProgrammeHistory.visitAt (I family atInput) ordinal).current =
        ProgrammeSource.rawEvent (I family atInput) (ProgrammeHistory.visitAt (I family atInput) ordinal).current) :
    ChallengeLifecycle.pendingImage code family
      (Cross.Programme.transportHistory family count (ChallengeTransport.items family count initial events) history within) =
    ChallengeLifecycle.pendingImage code family history := by
  cases history with
  | closed state archive slots => rfl
  | pending target state slots =>
    exact congrArg some (ChallengeTransport.claim_image code family count initial events target.claim within)

theorem transport_independent_prefixes {oldSeed newSeed : Index}
    (old : Cross.History family oldOriginal oldSeed) (new : Cross.History family newOriginal newSeed)
    (matched : Match code family old new) (oldCount newCount : Nat)
    (oldWithin : Cross.Programme.Within family oldCount old)
    (newWithin : Cross.Programme.Within family newCount new)
    (oldInitial : (I family inputs).initial = (I family oldSeed).initial)
    (newInitial : (I family nextInputs).initial = (I family newSeed).initial)
    (oldEvents : ∀ ordinal < oldCount,
      ProgrammeSource.rawEvent (I family inputs) (ProgrammeHistory.visitAt (I family oldSeed) ordinal).current =
        ProgrammeSource.rawEvent (I family oldSeed) (ProgrammeHistory.visitAt (I family oldSeed) ordinal).current)
    (newEvents : ∀ ordinal < newCount,
      ProgrammeSource.rawEvent (I family nextInputs) (ProgrammeHistory.visitAt (I family newSeed) ordinal).current =
        ProgrammeSource.rawEvent (I family newSeed) (ProgrammeHistory.visitAt (I family newSeed) ordinal).current) :
    Match code family
      (Cross.Programme.transportHistory family oldCount (ChallengeTransport.items family oldCount oldInitial oldEvents) old oldWithin)
      (Cross.Programme.transportHistory family newCount (ChallengeTransport.items family newCount newInitial newEvents) new newWithin) := by
  refine ⟨matched.original,?_,?_⟩
  · rw [Cross.Programme.transport_preserves_the_entire_generated_state,
      Cross.Programme.transport_preserves_the_entire_generated_state]
    exact matched.state
  · exact (transport_pending code family new newCount newWithin newInitial newEvents).trans
      (matched.pending.trans (transport_pending code family old oldCount oldWithin oldInitial oldEvents).symm)

theorem transport_match {oldSeed newSeed : Index}
    (old : Cross.History family oldOriginal oldSeed) (new : Cross.History family newOriginal newSeed)
    (matched : Match code family old new) (count : Nat)
    (oldWithin : Cross.Programme.Within family count old)
    (newWithin : Cross.Programme.Within family count new)
    (oldInitial : (I family inputs).initial = (I family oldSeed).initial)
    (newInitial : (I family nextInputs).initial = (I family newSeed).initial)
    (oldEvents : ∀ ordinal < count,
      ProgrammeSource.rawEvent (I family inputs) (ProgrammeHistory.visitAt (I family oldSeed) ordinal).current =
        ProgrammeSource.rawEvent (I family oldSeed) (ProgrammeHistory.visitAt (I family oldSeed) ordinal).current)
    (newEvents : ∀ ordinal < count,
      ProgrammeSource.rawEvent (I family nextInputs) (ProgrammeHistory.visitAt (I family newSeed) ordinal).current =
        ProgrammeSource.rawEvent (I family newSeed) (ProgrammeHistory.visitAt (I family newSeed) ordinal).current) :
    Match code family
      (Cross.Programme.transportHistory family count (ChallengeTransport.items family count oldInitial oldEvents) old oldWithin)
      (Cross.Programme.transportHistory family count (ChallengeTransport.items family count newInitial newEvents) new newWithin) :=
  transport_independent_prefixes code family old new matched count count oldWithin newWithin oldInitial newInitial oldEvents newEvents

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.CrossMigration
