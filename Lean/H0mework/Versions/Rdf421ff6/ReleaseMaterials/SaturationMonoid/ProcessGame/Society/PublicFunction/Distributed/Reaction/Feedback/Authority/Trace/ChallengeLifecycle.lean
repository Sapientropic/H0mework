import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.ChallengeJoint

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.ChallengeLifecycle

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Mandate.Challenge

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port (Mandate.State Party Technology) Instrument)
  {base : RawLaw Party Good Port Technology Instrument} {scope : Mandate.Scope}
  {Index : Type} (family : ProgrammeFamily base scope Index)
  {originInputs inputs nextInputs : Index} {original : Claim family originInputs}

def pendingImage {atInput : Index} : Cross.History family original atInput → Option (ChallengeImage Party Good Port Technology Instrument)
  | .pending target _ _ => some (challengeImage code family atInput target.claim)
  | .closed .. => none

structure Match (old : Cross.History family original inputs) (new : Cross.History family original nextInputs) : Prop where
  state : challengeStateImage code family originInputs new.state.current = challengeStateImage code family originInputs old.state.current
  pending : pendingImage code family new = pendingImage code family old

def readSources {atInput : Index} (history : Cross.History family original atInput) (position : Position family atInput) :=
  match history with
  | .pending target _ _ => (ChallengeTransport.reconfirmationSource code family target position,
      ChallengeTransport.attemptSource code family target position)
  | .closed .. => (none, none)

private theorem snapshot_of_claim_image (old : Claim family inputs) (new : Claim family nextInputs)
    (same : challengeImage code family nextInputs new = challengeImage code family inputs old) :
    new.snapshot family nextInputs = old.snapshot family inputs :=
  congrArg (fun item => item.before.technology)
    (itemImage_injective code (congrArg (fun image => image.position.item) same))

private theorem tracked_of_claim_image (old : Cross.Target family original inputs) (new : Cross.Target family original nextInputs)
    (same : challengeImage code family nextInputs new.claim = challengeImage code family inputs old.claim) :
    Cross.tracked family new = Cross.tracked family old :=
  congrArg (fun residual : Mandate.State Party Technology => {obligation family originInputs original with residual := residual})
    (snapshot_of_claim_image code family old.claim new.claim same)

private theorem cross_image (state : (Cross.process family original).GeneratedState)
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

private theorem reaffirm_boundary_images
    (old : Cross.Target family original inputs) (new : Cross.Target family original nextInputs)
    (oldReceipt : Cross.Reconfirmation family old) (newReceipt : Cross.Reconfirmation family new)
    (oldState newState : ResponsibilityState (V family originInputs))
    (oldSlot : Fin oldState.slots.length) (newSlot : Fin newState.slots.length)
    (sameSlot : newSlot.val = oldSlot.val)
    (oldPresent : oldState.slots.get oldSlot = .live (Cross.tracked family old))
    (newPresent : newState.slots.get newSlot = .live (Cross.tracked family new))
    (same : challengeEventImage code family originInputs (.remoteReaffirm original nextInputs new newReceipt) =
      challengeEventImage code family originInputs (.remoteReaffirm original inputs old oldReceipt)) :
    challengeSlotImage code family originInputs (Cross.disposition family original (.reaffirm new newReceipt rfl)).targetSlot =
        challengeSlotImage code family originInputs (Cross.disposition family original (.reaffirm old oldReceipt rfl)).targetSlot ∧
      challengeRecordImage code family originInputs ((NativeResponsibilityProcess.Edge.cross (P := Cross.process family original) newSlot (Cross.tracked family new) newPresent (.reaffirm new newReceipt rfl)).lifecycleEvent) =
      challengeRecordImage code family originInputs ((NativeResponsibilityProcess.Edge.cross (P := Cross.process family original) oldSlot (Cross.tracked family old) oldPresent (.reaffirm old oldReceipt rfl)).lifecycleEvent) := by
  have parts := ChallengeEventImage.reaffirm.inj same
  have previous := tracked_of_claim_image code family old new parts.2.2.1
  have next := tracked_of_claim_image code family (oldReceipt.target family) (newReceipt.target family) parts.2.2.2
  change ChallengeSlotImage.live (challengeObligationImage code family originInputs (Cross.tracked family (newReceipt.target family))) =
        ChallengeSlotImage.live (challengeObligationImage code family originInputs (Cross.tracked family (oldReceipt.target family))) ∧
      ChallengeRecordImage.mk newSlot.val .progressed
        (some (.live (challengeObligationImage code family originInputs (Cross.tracked family new))))
        (.live (challengeObligationImage code family originInputs (Cross.tracked family (newReceipt.target family))))
        (challengeEventImage code family originInputs (.remoteReaffirm original nextInputs new newReceipt)) =
      ChallengeRecordImage.mk oldSlot.val .progressed
        (some (.live (challengeObligationImage code family originInputs (Cross.tracked family old))))
        (.live (challengeObligationImage code family originInputs (Cross.tracked family (oldReceipt.target family))))
        (challengeEventImage code family originInputs (.remoteReaffirm original inputs old oldReceipt))
  rw [sameSlot, previous, next, same]
  exact ⟨rfl, rfl⟩

private theorem attempt_items (old : Cross.Target family original inputs) (new : Cross.Target family original nextInputs)
    (oldReceipt : Attempt family inputs old.claim) (newReceipt : Attempt family nextInputs new.claim)
    (same : challengeEventImage code family originInputs (.remoteAttempt original nextInputs new newReceipt) =
      challengeEventImage code family originInputs (.remoteAttempt original inputs old oldReceipt)) :
    newReceipt.position.item family nextInputs = oldReceipt.position.item family inputs := by
  have parts := ChallengeEventImage.attempt.inj same
  exact (equal_position_images_recover_the_actual_item code family inputs nextInputs _ _ parts.2.2.2.1).2

private theorem attempt_boundary_images
    (old : Cross.Target family original inputs) (new : Cross.Target family original nextInputs)
    (oldReceipt : Attempt family inputs old.claim) (newReceipt : Attempt family nextInputs new.claim)
    (oldState newState : ResponsibilityState (V family originInputs))
    (oldSlot : Fin oldState.slots.length) (newSlot : Fin newState.slots.length)
    (sameSlot : newSlot.val = oldSlot.val)
    (oldPresent : oldState.slots.get oldSlot = .live (Cross.tracked family old))
    (newPresent : newState.slots.get newSlot = .live (Cross.tracked family new))
    (same : challengeEventImage code family originInputs (.remoteAttempt original nextInputs new newReceipt) =
      challengeEventImage code family originInputs (.remoteAttempt original inputs old oldReceipt)) :
    challengeSlotImage code family originInputs (Cross.disposition family original (.attempt new newReceipt rfl)).targetSlot =
        challengeSlotImage code family originInputs (Cross.disposition family original (.attempt old oldReceipt rfl)).targetSlot ∧
      challengeRecordImage code family originInputs ((NativeResponsibilityProcess.Edge.cross (P := Cross.process family original) newSlot (Cross.tracked family new) newPresent (.attempt new newReceipt rfl)).lifecycleEvent) =
      challengeRecordImage code family originInputs ((NativeResponsibilityProcess.Edge.cross (P := Cross.process family original) oldSlot (Cross.tracked family old) oldPresent (.attempt old oldReceipt rfl)).lifecycleEvent) := by
  have parts := ChallengeEventImage.attempt.inj same
  have previous := tracked_of_claim_image code family old new parts.2.2.1
  have item := attempt_items code family old new oldReceipt newReceipt same
  unfold Cross.disposition
  by_cases accepted : (Mandate.law base scope).Valid (oldReceipt.position.item family inputs).before (oldReceipt.position.item family inputs).request
  · have nextAccepted : (Mandate.law base scope).Valid (newReceipt.position.item family nextInputs).before (newReceipt.position.item family nextInputs).request := by rw [item]; exact accepted
    simp only [NativeResponsibilityProcess.Edge.lifecycleEvent, Cross.process, Cross.disposition, dif_pos accepted, dif_pos nextAccepted]
    change ChallengeSlotImage.terminal (challengeObligationImage code family originInputs (Cross.tracked family new))
          (challengeEventImage code family originInputs (.remoteAttempt original nextInputs new newReceipt)) =
        ChallengeSlotImage.terminal (challengeObligationImage code family originInputs (Cross.tracked family old))
          (challengeEventImage code family originInputs (.remoteAttempt original inputs old oldReceipt)) ∧
      ChallengeRecordImage.mk newSlot.val .obligationTerminal
        (some (.live (challengeObligationImage code family originInputs (Cross.tracked family new))))
        (.terminal (challengeObligationImage code family originInputs (Cross.tracked family new))
          (challengeEventImage code family originInputs (.remoteAttempt original nextInputs new newReceipt)))
        (challengeEventImage code family originInputs (.remoteAttempt original nextInputs new newReceipt)) =
      ChallengeRecordImage.mk oldSlot.val .obligationTerminal
        (some (.live (challengeObligationImage code family originInputs (Cross.tracked family old))))
        (.terminal (challengeObligationImage code family originInputs (Cross.tracked family old))
          (challengeEventImage code family originInputs (.remoteAttempt original inputs old oldReceipt)))
        (challengeEventImage code family originInputs (.remoteAttempt original inputs old oldReceipt))
    rw [sameSlot, previous, same]
    exact ⟨rfl, rfl⟩
  · have nextRefused : ¬(Mandate.law base scope).Valid (newReceipt.position.item family nextInputs).before (newReceipt.position.item family nextInputs).request := by rw [item]; exact accepted
    simp only [NativeResponsibilityProcess.Edge.lifecycleEvent, Cross.process, Cross.disposition, dif_neg accepted, dif_neg nextRefused]
    change ChallengeSlotImage.live (challengeObligationImage code family originInputs (Cross.tracked family new)) =
        ChallengeSlotImage.live (challengeObligationImage code family originInputs (Cross.tracked family old)) ∧
      ChallengeRecordImage.mk newSlot.val .deferred
        (some (.live (challengeObligationImage code family originInputs (Cross.tracked family new))))
        (.live (challengeObligationImage code family originInputs (Cross.tracked family new)))
        (challengeEventImage code family originInputs (.remoteAttempt original nextInputs new newReceipt)) =
      ChallengeRecordImage.mk oldSlot.val .deferred
        (some (.live (challengeObligationImage code family originInputs (Cross.tracked family old))))
        (.live (challengeObligationImage code family originInputs (Cross.tracked family old)))
        (challengeEventImage code family originInputs (.remoteAttempt original inputs old oldReceipt))
    rw [sameSlot, previous, same]
    exact ⟨rfl, rfl⟩

private theorem cross_state_image
    (old new : (Cross.process family original).GeneratedState)
    (oldSlot : Fin old.current.slots.length) (newSlot : Fin new.current.slots.length)
    (oldObligation newObligation : AdmittedObligation (V family originInputs))
    (oldPresent : old.current.slots.get oldSlot = .live oldObligation)
    (newPresent : new.current.slots.get newSlot = .live newObligation)
    (oldEvent : Cross.Boundary family original oldObligation) (newEvent : Cross.Boundary family original newObligation)
    (before : challengeStateImage code family originInputs new.current = challengeStateImage code family originInputs old.current)
    (sameSlot : newSlot.val = oldSlot.val)
    (target : challengeSlotImage code family originInputs (Cross.disposition family original newEvent).targetSlot =
      challengeSlotImage code family originInputs (Cross.disposition family original oldEvent).targetSlot)
    (record : challengeRecordImage code family originInputs
        ((NativeResponsibilityProcess.Edge.cross (P := Cross.process family original) newSlot newObligation newPresent newEvent).lifecycleEvent) =
      challengeRecordImage code family originInputs
        ((NativeResponsibilityProcess.Edge.cross (P := Cross.process family original) oldSlot oldObligation oldPresent oldEvent).lifecycleEvent)) :
    challengeStateImage code family originInputs (new.step (Cross.process family original) (.cross newSlot newObligation newPresent newEvent)).current =
      challengeStateImage code family originInputs (old.step (Cross.process family original) (.cross oldSlot oldObligation oldPresent oldEvent)).current := by
  rw [cross_image, cross_image, target, record, before, sameSlot]

theorem receive_match (old : Cross.History family original inputs) (new : Cross.History family original nextInputs)
    (oldPosition : Position family inputs) (newPosition : Position family nextInputs)
    (matched : Match code family old new)
    (sources : readSources code family new newPosition = readSources code family old oldPosition) :
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
      dsimp only [readSources] at reaffirm attempt
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
            exact ⟨after, rfl⟩
          · have nextRefused : ¬(Mandate.law base scope).Valid (newReceipt.position.item family nextInputs).before (newReceipt.position.item family nextInputs).request := by rw [item]; exact accepted
            simp only [Cross.History.receive, oldRead, newRead, oldAttempt, newAttempt, dif_neg accepted, dif_neg nextRefused]
            exact ⟨after, matched.pending⟩
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
        exact ⟨after, congrArg some (ChallengeEventImage.reaffirm.inj same).2.2.2⟩

private theorem claim_coordinates (old : Claim family inputs) (new : Claim family nextInputs)
    (same : challengeImage code family nextInputs new = challengeImage code family inputs old) :
    new.position.ordinal = old.position.ordinal ∧ new.position.index.val = old.position.index.val := by
  have indices := congrArg (fun image => image.position.origin.traceIndex) same
  change some new.position.index.val = some old.position.index.val at indices
  exact ⟨congrArg (fun image => image.position.ordinal) same, Option.some.inj indices⟩

variable (limit : Nat)
  (initial : (I family nextInputs).initial = (I family inputs).initial)
  (events : ∀ ordinal < limit,
    ProgrammeSource.rawEvent (I family nextInputs) (ProgrammeHistory.visitAt (I family inputs) ordinal).current =
      ProgrammeSource.rawEvent (I family inputs) (ProgrammeHistory.visitAt (I family inputs) ordinal).current)

include initial events in
theorem read_sources_congr (old : Cross.History family original inputs) (new : Cross.History family original nextInputs)
    (matched : Match code family old new) (within : Cross.Programme.Within family limit old)
    (oldPosition : Position family inputs) (newPosition : Position family nextInputs)
    (ordinal : newPosition.ordinal = oldPosition.ordinal) (index : newPosition.index.val = oldPosition.index.val)
    (inside : oldPosition.ordinal < limit) :
    readSources code family new newPosition = readSources code family old oldPosition := by
  cases old with
  | closed oldState oldArchive oldSlots =>
    cases new with
    | closed newState newArchive newSlots => rfl
    | pending newTarget newState newSlots => cases matched.pending
  | pending oldTarget oldState oldSlots =>
    cases new with
    | closed newState newArchive newSlots => cases matched.pending
    | pending newTarget newState newSlots =>
      have targets := claim_coordinates code family oldTarget.claim newTarget.claim (Option.some.inj matched.pending)
      exact Prod.ext
        (ChallengeTransport.reconfirmation_source_congr code family limit initial events oldTarget newTarget
          targets.1 targets.2 within oldPosition newPosition ordinal index inside)
        (ChallengeTransport.attempt_source_congr code family limit initial events oldTarget newTarget
          targets.1 targets.2 within oldPosition newPosition ordinal index inside)

include initial events in
theorem receive_from_prefix (old : Cross.History family original inputs) (new : Cross.History family original nextInputs)
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
    (old : Cross.History family original inputs) (new : Cross.History family original nextInputs)
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
    (old : Cross.History family original inputs) (new : Cross.History family original nextInputs)
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
    (old : Cross.History family original inputs) (new : Cross.History family original nextInputs)
    (matched : Match code family old new) (within : Cross.Programme.Within family limit old) :
    Match code family (Cross.Programme.continueFrom family old start count) (Cross.Programme.continueFrom family new start count) := by
  apply visits_match code family limit initial events _ _ old new matched within
  intro ordinal member
  obtain ⟨offset, before, same⟩ := List.mem_map.mp member
  cases same
  have inside := List.mem_range.mp before
  omega

theorem transport_seeds_match {seedInputs : Index}
    (seed : Cross.History family original seedInputs) (count : Nat) (within : Cross.Programme.Within family count seed)
    (oldInitial : (I family inputs).initial = (I family seedInputs).initial)
    (newInitial : (I family nextInputs).initial = (I family seedInputs).initial)
    (oldEvents : ∀ ordinal < count,
      ProgrammeSource.rawEvent (I family inputs) (ProgrammeHistory.visitAt (I family seedInputs) ordinal).current =
        ProgrammeSource.rawEvent (I family seedInputs) (ProgrammeHistory.visitAt (I family seedInputs) ordinal).current)
    (newEvents : ∀ ordinal < count,
      ProgrammeSource.rawEvent (I family nextInputs) (ProgrammeHistory.visitAt (I family seedInputs) ordinal).current =
        ProgrammeSource.rawEvent (I family seedInputs) (ProgrammeHistory.visitAt (I family seedInputs) ordinal).current) :
    let oldCommon := ChallengeTransport.items family (inputs := seedInputs) (nextInputs := inputs) count oldInitial oldEvents
    let newCommon := ChallengeTransport.items family (inputs := seedInputs) (nextInputs := nextInputs) count newInitial newEvents
    Match code family
      (Cross.Programme.transportHistory family (inputs := seedInputs) (nextInputs := inputs) count oldCommon seed within)
      (Cross.Programme.transportHistory family (inputs := seedInputs) (nextInputs := nextInputs) count newCommon seed within) := by
  dsimp only
  constructor
  · have oldState := Cross.Programme.transport_preserves_the_entire_generated_state family
      (inputs := seedInputs) (nextInputs := inputs) count (ChallengeTransport.items family count oldInitial oldEvents) seed within
    have newState := Cross.Programme.transport_preserves_the_entire_generated_state family
      (inputs := seedInputs) (nextInputs := nextInputs) count (ChallengeTransport.items family count newInitial newEvents) seed within
    exact congrArg (fun state => challengeStateImage code family originInputs state.current) (newState.trans oldState.symm)
  · cases seed with
    | closed state archive slots => rfl
    | pending target state slots =>
      exact congrArg some ((ChallengeTransport.claim_image code family (inputs := seedInputs) (nextInputs := nextInputs)
        count newInitial newEvents target.claim within).trans
          (ChallengeTransport.claim_image code family (inputs := seedInputs) (nextInputs := inputs)
            count oldInitial oldEvents target.claim within).symm)

theorem within_mono (first last : Nat) (le : first ≤ last) (history : Cross.History family original inputs)
    (within : Cross.Programme.Within family first history) : Cross.Programme.Within family last history := by
  cases history with
  | closed state archive slots => exact True.intro
  | pending target state slots => exact Nat.lt_of_lt_of_le within le

theorem transport_within (count : Nat)
    (common : ∀ ordinal < count,
      Institutions.Capitalism.Universal.Source.ProgrammeFace.Registered.traceItems (I family nextInputs)
          (ProgrammeHistory.visitAt (I family nextInputs) ordinal).current =
        Institutions.Capitalism.Universal.Source.ProgrammeFace.Registered.traceItems (I family inputs)
          (ProgrammeHistory.visitAt (I family inputs) ordinal).current)
    (history : Cross.History family original inputs) (within : Cross.Programme.Within family count history) :
    Cross.Programme.Within family count
      (Cross.Programme.transportHistory family (inputs := inputs) (nextInputs := nextInputs) count common history within) := by
  cases history with
  | closed state archive slots => exact True.intro
  | pending target state slots =>
    change (Cross.Programme.replacement family count common target.claim within).position.ordinal < count
    rw [(Cross.Programme.replacement_same_item_and_snapshot family count common target.claim within).2.2.2.1]
    exact within

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.ChallengeLifecycle
