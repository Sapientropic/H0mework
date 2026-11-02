import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Challenge
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.HistoryCoupling

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.ChallengeTransport

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Institutions.Capitalism.Universal.Source.ProgrammeFace Mandate.Challenge

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port (Mandate.State Party Technology) Instrument)
  {base : RawLaw Party Good Port Technology Instrument} {scope : Mandate.Scope}
  {Index : Type} (family : ProgrammeFamily base scope Index)
  {inputs nextInputs : Index} (limit : Nat)
  (initial : (I family nextInputs).initial = (I family inputs).initial)
  (events : ∀ ordinal < limit,
    ProgrammeSource.rawEvent (I family nextInputs) (ProgrammeHistory.visitAt (I family inputs) ordinal).current =
      ProgrammeSource.rawEvent (I family inputs) (ProgrammeHistory.visitAt (I family inputs) ordinal).current)

include initial events in
theorem items (ordinal : Nat) (inside : ordinal < limit) :
    Registered.traceItems (I family nextInputs) (ProgrammeHistory.visitAt (I family nextInputs) ordinal).current =
      Registered.traceItems (I family inputs) (ProgrammeHistory.visitAt (I family inputs) ordinal).current :=
  Native.Coupling.History.trace_items (I family inputs) (I family nextInputs)
    ((family.law_exact nextInputs).trans (family.law_exact inputs).symm) initial limit events ordinal inside

theorem position_image (position : Position family inputs) (inside : position.ordinal < limit) :
    positionImage code family nextInputs (Cross.Programme.position family limit (items family limit initial events) position inside) =
      positionImage code family inputs position := by
  apply (PositionImage.mk.injEq ..).mpr
  refine ⟨?_, rfl, congrArg (itemImage code) (Cross.Programme.position_same_item family limit (items family limit initial events) position inside)⟩
  exact Native.Coupling.History.origin_image code (I family inputs) (I family nextInputs)
    ((family.law_exact nextInputs).trans (family.law_exact inputs).symm) initial limit events position.ordinal inside position.index

theorem claim_image (claim : Claim family inputs) (inside : claim.position.ordinal < limit) :
    challengeImage code family nextInputs (Cross.Programme.replacement family limit (items family limit initial events) claim inside) =
      challengeImage code family inputs claim := by
  let replacement := Cross.Programme.replacement family limit (items family limit initial events) claim inside
  have preserved := Cross.Programme.replacement_same_item_and_snapshot family limit (items family limit initial events) claim inside
  have first := Native.Coupling.History.first_birth code (I family inputs) (I family nextInputs)
    ((family.law_exact nextInputs).trans (family.law_exact inputs).symm) initial limit events claim.position.ordinal inside
      (claim.signer family inputs)
  have oldFound : Native.Coupling.Causality.birthHistoryImage code (I family inputs) claim.position.ordinal (claim.signer family inputs) =
      some (Identity.birthImage code (I family inputs) (claim.birth family inputs).original) := by
    exact congrArg (Option.map (Identity.birthImage code (I family inputs))) (claim.birth family inputs).generated
  have newFound : Native.Coupling.Causality.birthHistoryImage code (I family nextInputs) claim.position.ordinal (claim.signer family inputs) =
      some (Identity.birthImage code (I family nextInputs) (replacement.birth family nextInputs).original) := by
    have found := congrArg (Option.map (Identity.birthImage code (I family nextInputs))) (replacement.birth family nextInputs).generated
    change Native.Coupling.Causality.birthHistoryImage code (I family nextInputs) replacement.position.ordinal (replacement.signer family nextInputs) = _ at found
    simpa only [replacement, preserved.2.2.2.1, preserved.2.2.1, Option.map_some] using found
  apply (ChallengeImage.mk.injEq ..).mpr
  refine ⟨?_, ?_⟩
  · rw [Cross.Programme.replacement_position]
    exact position_image code family limit initial events claim.position inside
  · exact Native.Coupling.State.birth_actor_natural code (I family inputs) (I family nextInputs)
      ((family.law_exact nextInputs).trans (family.law_exact inputs).symm) initial _ _
      (Option.some.inj (newFound.symm.trans (first.trans oldFound)))

private theorem position_ext {atInput : Index} (first second : Position family atInput)
    (ordinal : second.ordinal = first.ordinal) (index : second.index.val = first.index.val) : second = first := by
  cases first with
  | mk firstOrdinal firstIndex =>
    cases second with
    | mk secondOrdinal secondIndex =>
      dsimp only at ordinal index
      subst secondOrdinal
      have same := Fin.ext index
      cases same
      rfl

private theorem claim_ext {atInput : Index} (first second : Claim family atInput) (same : second.position = first.position) : second = first := by
  cases first; cases second; cases same; rfl

private theorem read_present {atInput other : Index} (first : Position family atInput) (second : Position family other)
    (same : second.item family other = first.item family atInput) :
    (read family other second).isSome = (read family atInput first).isSome := by
  unfold Mandate.Challenge.read
  simp only [same]
  split_ifs <;> rfl

theorem replacement_of_read (position : Position family inputs) (inside : position.ordinal < limit)
    (old : Claim family inputs) (new : Claim family nextInputs)
    (oldRead : read family inputs position = some old)
    (newRead : read family nextInputs (Cross.Programme.position family limit (items family limit initial events) position inside) = some new) :
    new = Cross.Programme.replacement family limit (items family limit initial events) old
      (by rw [read_position family inputs position old oldRead]; exact inside) := by
  apply claim_ext family
  apply position_ext family
  · simp only [Cross.Programme.replacement_position, Cross.Programme.position]
    exact (congrArg Position.ordinal (read_position family nextInputs _ _ newRead)).trans
      (congrArg Position.ordinal (read_position family inputs position old oldRead)).symm
  · exact (congrArg (fun p => p.index.val) (read_position family nextInputs _ _ newRead)).trans
      ((congrArg (fun p => p.index.val) (read_position family inputs position old oldRead)).symm.trans
        (Cross.Programme.replacement_same_item_and_snapshot family limit (items family limit initial events) old _).2.2.2.2.symm)

include initial events in
theorem position_image_congr (old : Position family inputs) (new : Position family nextInputs)
    (ordinal : new.ordinal = old.ordinal) (index : new.index.val = old.index.val)
    (inside : old.ordinal < limit) : positionImage code family nextInputs new = positionImage code family inputs old := by
  have same : new = Cross.Programme.position family limit (items family limit initial events) old inside :=
    position_ext family _ _ ordinal index
  rw [same]
  exact position_image code family limit initial events old inside

include initial events in
theorem claim_image_congr (old : Claim family inputs) (new : Claim family nextInputs)
    (ordinal : new.position.ordinal = old.position.ordinal) (index : new.position.index.val = old.position.index.val)
    (inside : old.position.ordinal < limit) : challengeImage code family nextInputs new = challengeImage code family inputs old := by
  have same : new = Cross.Programme.replacement family limit (items family limit initial events) old inside := by
    apply claim_ext family
    apply position_ext family
    · simpa only [Cross.Programme.replacement_position, Cross.Programme.position] using ordinal
    · exact index.trans (Cross.Programme.replacement_same_item_and_snapshot family limit (items family limit initial events) old inside).2.2.2.2.symm
  rw [same]
  exact claim_image code family limit initial events old inside

include code initial events in
theorem position_items_congr (old : Position family inputs) (new : Position family nextInputs)
    (ordinal : new.ordinal = old.ordinal) (index : new.index.val = old.index.val)
    (inside : old.ordinal < limit) : new.item family nextInputs = old.item family inputs :=
  (equal_position_images_recover_the_actual_item code family inputs nextInputs old new
    (position_image_congr code family limit initial events old new ordinal index inside)).2

variable {originInputs : Index} {original : Claim family originInputs}

include code initial events in
private theorem reconfirmation_present (oldTarget : Cross.Target family original inputs)
    (newTarget : Cross.Target family original nextInputs)
    (targetOrdinal : newTarget.claim.position.ordinal = oldTarget.claim.position.ordinal)
    (targetIndex : newTarget.claim.position.index.val = oldTarget.claim.position.index.val)
    (targetInside : oldTarget.claim.position.ordinal < limit)
    (old : Position family inputs) (new : Position family nextInputs)
    (ordinal : new.ordinal = old.ordinal) (index : new.index.val = old.index.val) (inside : old.ordinal < limit) :
    (Cross.readReconfirmation family newTarget new).isSome = (Cross.readReconfirmation family oldTarget old).isSome := by
  have sameItem := position_items_congr code family limit initial events old new ordinal index inside
  have sameTarget := position_items_congr code family limit initial events oldTarget.claim.position newTarget.claim.position targetOrdinal targetIndex targetInside
  have sameRead := read_present family old new sameItem
  unfold Cross.readReconfirmation
  cases oldRead : Mandate.Challenge.read family inputs old <;>
    cases newRead : Mandate.Challenge.read family nextInputs new <;>
    simp only [oldRead, newRead] at sameRead ⊢
  · rfl
  · cases sameRead
  · cases sameRead
  · rename_i oldClaim newClaim
    have oldAt := read_position family inputs old oldClaim oldRead
    have newAt := read_position family nextInputs new newClaim newRead
    have oldIndex := congrArg (fun p => p.index.val) oldAt
    have newIndex := congrArg (fun p => p.index.val) newAt
    simp only [Later, Claim.signer, oldAt, newAt, oldIndex, newIndex,
      ordinal, index, targetOrdinal, targetIndex, sameItem, sameTarget]
    split_ifs <;> rfl

include code initial events in
private theorem attempt_present (oldClaim : Claim family inputs) (newClaim : Claim family nextInputs)
    (targetOrdinal : newClaim.position.ordinal = oldClaim.position.ordinal)
    (targetIndex : newClaim.position.index.val = oldClaim.position.index.val)
    (targetInside : oldClaim.position.ordinal < limit)
    (old : Position family inputs) (new : Position family nextInputs)
    (ordinal : new.ordinal = old.ordinal) (index : new.index.val = old.index.val) (inside : old.ordinal < limit) :
    (readAttempt family nextInputs newClaim new).isSome = (readAttempt family inputs oldClaim old).isSome := by
  have sameItem := position_items_congr code family limit initial events old new ordinal index inside
  have sameTarget := position_items_congr code family limit initial events oldClaim.position newClaim.position targetOrdinal targetIndex targetInside
  have equivalent :
      (Later family nextInputs newClaim.position new ∧
        Withdrawal (scope := scope) (new.item family nextInputs).before (new.item family nextInputs).request ∧
          (new.item family nextInputs).before.technology = newClaim.snapshot family nextInputs) ↔
      (Later family inputs oldClaim.position old ∧
        Withdrawal (scope := scope) (old.item family inputs).before (old.item family inputs).request ∧
          (old.item family inputs).before.technology = oldClaim.snapshot family inputs) := by
    simp only [Later, Claim.snapshot, ordinal, index, targetOrdinal, targetIndex, sameItem, sameTarget]
  unfold readAttempt
  by_cases checked : Later family inputs oldClaim.position old ∧
      Withdrawal (scope := scope) (old.item family inputs).before (old.item family inputs).request ∧
        (old.item family inputs).before.technology = oldClaim.snapshot family inputs
  · rw [dif_pos checked, dif_pos (equivalent.mpr checked)]; rfl
  · rw [dif_neg checked, dif_neg (fun accepted => checked (equivalent.mp accepted))]; rfl

private theorem reconfirmation_position {atInput : Index} (target : Cross.Target family original atInput)
    (position : Position family atInput) (receipt : Cross.Reconfirmation family target)
    (selected : Cross.readReconfirmation family target position = some receipt) : receipt.claim.position = position := by
  unfold Cross.readReconfirmation at selected
  split at selected
  · cases selected
  · rename_i claim readClaim
    split at selected
    · cases Option.some.inj selected
      exact read_position family atInput _ _ readClaim
    · cases selected

private theorem attempt_position {atInput : Index} (claim : Claim family atInput)
    (position : Position family atInput) (receipt : Attempt family atInput claim)
    (selected : readAttempt family atInput claim position = some receipt) : receipt.position = position := by
  unfold readAttempt at selected
  split at selected
  · cases Option.some.inj selected; rfl
  · cases selected

def reconfirmationSource {atInput : Index} (target : Cross.Target family original atInput) (position : Position family atInput) :=
  (Cross.readReconfirmation family target position).map fun receipt =>
    challengeEventImage code family originInputs (.remoteReaffirm original atInput target receipt)

def attemptSource {atInput : Index} (target : Cross.Target family original atInput) (position : Position family atInput) :=
  (readAttempt family atInput target.claim position).map fun receipt =>
    challengeEventImage code family originInputs (.remoteAttempt original atInput target receipt)

include initial events in
theorem reconfirmation_source_congr (oldTarget : Cross.Target family original inputs)
    (newTarget : Cross.Target family original nextInputs)
    (targetOrdinal : newTarget.claim.position.ordinal = oldTarget.claim.position.ordinal)
    (targetIndex : newTarget.claim.position.index.val = oldTarget.claim.position.index.val)
    (targetInside : oldTarget.claim.position.ordinal < limit)
    (old : Position family inputs) (new : Position family nextInputs)
    (ordinal : new.ordinal = old.ordinal) (index : new.index.val = old.index.val) (inside : old.ordinal < limit) :
    reconfirmationSource code family newTarget new = reconfirmationSource code family oldTarget old := by
  have present := reconfirmation_present code family limit initial events oldTarget newTarget targetOrdinal targetIndex targetInside old new ordinal index inside
  unfold reconfirmationSource
  cases oldRead : Cross.readReconfirmation family oldTarget old <;>
    cases newRead : Cross.readReconfirmation family newTarget new <;>
    simp only [oldRead, newRead, Option.map_none, Option.map_some] at present ⊢
  · cases present
  · cases present
  · rename_i oldReceipt newReceipt
    have oldAt := reconfirmation_position family oldTarget old oldReceipt oldRead
    have newAt := reconfirmation_position family newTarget new newReceipt newRead
    apply congrArg some
    dsimp only [challengeEventImage]
    congr 1
    · exact claim_image_congr code family limit initial events oldTarget.claim newTarget.claim targetOrdinal targetIndex targetInside
    · apply claim_image_congr code family limit initial events oldReceipt.claim newReceipt.claim
      · exact (congrArg Position.ordinal newAt).trans (ordinal.trans (congrArg Position.ordinal oldAt).symm)
      · exact (congrArg (fun p => p.index.val) newAt).trans (index.trans (congrArg (fun p => p.index.val) oldAt).symm)
      · rw [oldAt]; exact inside

include initial events in
theorem attempt_source_congr (oldTarget : Cross.Target family original inputs)
    (newTarget : Cross.Target family original nextInputs)
    (targetOrdinal : newTarget.claim.position.ordinal = oldTarget.claim.position.ordinal)
    (targetIndex : newTarget.claim.position.index.val = oldTarget.claim.position.index.val)
    (targetInside : oldTarget.claim.position.ordinal < limit)
    (old : Position family inputs) (new : Position family nextInputs)
    (ordinal : new.ordinal = old.ordinal) (index : new.index.val = old.index.val) (inside : old.ordinal < limit) :
    attemptSource code family newTarget new = attemptSource code family oldTarget old := by
  have present := attempt_present code family limit initial events oldTarget.claim newTarget.claim targetOrdinal targetIndex targetInside old new ordinal index inside
  unfold attemptSource
  cases oldRead : readAttempt family inputs oldTarget.claim old <;>
    cases newRead : readAttempt family nextInputs newTarget.claim new <;>
    simp only [oldRead, newRead, Option.map_none, Option.map_some] at present ⊢
  · cases present
  · cases present
  · rename_i oldReceipt newReceipt
    have oldAt := attempt_position family oldTarget.claim old oldReceipt oldRead
    have newAt := attempt_position family newTarget.claim new newReceipt newRead
    have sameItem := position_items_congr code family limit initial events old new ordinal index inside
    apply congrArg some
    dsimp only [challengeEventImage]
    rw [oldAt, newAt, sameItem]
    congr 1
    · exact claim_image_congr code family limit initial events oldTarget.claim newTarget.claim targetOrdinal targetIndex targetInside
    · exact position_image_congr code family limit initial events old new ordinal index inside

include initial events in
theorem read_images (old : Position family inputs) (new : Position family nextInputs)
    (ordinal : new.ordinal = old.ordinal) (index : new.index.val = old.index.val) (inside : old.ordinal < limit) :
    (Mandate.Challenge.read family nextInputs new).map (challengeImage code family nextInputs) =
      (Mandate.Challenge.read family inputs old).map (challengeImage code family inputs) := by
  have sameItem := position_items_congr code family limit initial events old new ordinal index inside
  have present := read_present family old new sameItem
  cases oldRead : Mandate.Challenge.read family inputs old <;>
    cases newRead : Mandate.Challenge.read family nextInputs new <;>
    simp only [oldRead, newRead, Option.map_none, Option.map_some] at present ⊢
  · cases present
  · cases present
  · rename_i oldClaim newClaim
    apply congrArg some
    apply claim_image_congr code family limit initial events oldClaim newClaim
    · exact (congrArg Position.ordinal (read_position family nextInputs new newClaim newRead)).trans
        (ordinal.trans (congrArg Position.ordinal (read_position family inputs old oldClaim oldRead)).symm)
    · exact (congrArg (fun p => p.index.val) (read_position family nextInputs new newClaim newRead)).trans
        (index.trans (congrArg (fun p => p.index.val) (read_position family inputs old oldClaim oldRead)).symm)
    · rw [read_position family inputs old oldClaim oldRead]; exact inside

private theorem positions_ordinal {atInput : Index} (ordinal : Nat) (position : Position family atInput)
    (member : position ∈ positionsAt family atInput ordinal) : position.ordinal = ordinal := by
  obtain ⟨index, _, same⟩ := List.mem_map.mp member
  cases same
  rfl

include initial events in
private theorem positions_mapped (ordinal : Nat) (inside : ordinal < limit) :
    positionsAt family nextInputs ordinal = (positionsAt family inputs ordinal).attach.map
      (fun record => let position := record.val; Cross.Programme.position family limit (items family limit initial events) position
        (by rw [positions_ordinal family ordinal position record.property]; exact inside)) := by
  simp only [positionsAt]
  apply List.ext_getElem
  · simpa only [List.length_map, List.length_attach, List.length_finRange] using congrArg List.length (items family limit initial events ordinal inside)
  · intro index oldBound newBound
    simp only [List.getElem_map, List.getElem_attach, List.getElem_finRange]
    apply position_ext family <;> rfl

include initial events in
theorem claims_images (ordinal : Nat) (inside : ordinal < limit) :
    (claimsAt family nextInputs ordinal).map (challengeImage code family nextInputs) =
      (claimsAt family inputs ordinal).map (challengeImage code family inputs) := by
  unfold claimsAt
  rw [positions_mapped family limit initial events ordinal inside]
  simp only [List.filterMap_map, List.map_filterMap, Function.comp_def]
  trans (positionsAt family inputs ordinal).attach.filterMap (fun record =>
    (Mandate.Challenge.read family inputs record.val).map (challengeImage code family inputs))
  · apply List.filterMap_congr
    intro record _
    exact read_images code family limit initial events record.val _ rfl rfl
      (by rw [positions_ordinal family ordinal record.val record.property]; exact inside)
  · simpa only [List.filterMap_map, Function.comp_def] using
      congrArg (List.filterMap (fun position => (Mandate.Challenge.read family inputs position).map (challengeImage code family inputs)))
        (List.attach_map_subtype_val (positionsAt family inputs ordinal))

include initial events in
theorem census_images (count : Nat) (bounded : count ≤ limit) :
    (Mandate.Challenge.recordsAt family nextInputs count).map (fun record => challengeImage code family nextInputs record.1) =
      (Mandate.Challenge.recordsAt family inputs count).map (fun record => challengeImage code family inputs record.1) := by
  simp only [Mandate.Challenge.recordsAt, List.map_flatMap, List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro ordinal member
  exact claims_images code family limit initial events ordinal (Nat.lt_of_lt_of_le (List.mem_range.mp member) bounded)

include initial events in
theorem actual_source_transport (target : Cross.Target family original inputs)
    (within : target.claim.position.ordinal < limit) (position : Position family inputs) (inside : position.ordinal < limit) :
    let nextTarget := Cross.Programme.transportTarget family limit (items family limit initial events) target within
    let nextPosition := Cross.Programme.position family limit (items family limit initial events) position inside
    challengeImage code family nextInputs nextTarget.claim = challengeImage code family inputs target.claim ∧
      nextTarget.snapshot family = target.snapshot family ∧
      reconfirmationSource code family nextTarget nextPosition = reconfirmationSource code family target position ∧
      attemptSource code family nextTarget nextPosition = attemptSource code family target position := by
  have preserved := Cross.Programme.replacement_same_item_and_snapshot family limit (items family limit initial events) target.claim within
  exact ⟨claim_image code family limit initial events target.claim within,
    Cross.Programme.transported_target_keeps_snapshot family limit (items family limit initial events) target within,
    reconfirmation_source_congr code family limit initial events target _ preserved.2.2.2.1 preserved.2.2.2.2 within position _ rfl rfl inside,
    attempt_source_congr code family limit initial events target _ preserved.2.2.2.1 preserved.2.2.2.2 within position _ rfl rfl inside⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.ChallengeTransport
