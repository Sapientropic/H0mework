import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeRecoverySource

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeRecovery
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (past : NativeReviewRun.Stages model)

structure Qualified (material : NativeRecoveryMaterial.Ready model start past)
    (original : NativeRecoverySource.Original model start past material) where
  private mk ::
  old : original.position.ordinal < NativeRecoverySource.ordinal model start past
  pending : (NativeRecoverySource.before model start past material original).isPending _ _ = true
  stale : NativeRecoverySource.stale model start past material original = true
  renewal : Mandate.Challenge.Reconfirmation (NativeRecoverySource.family model start past material)
    (NativeRecoverySource.sourceIndex model start past material) original
  renewed : Mandate.Challenge.readReconfirmation _ _ original (NativeRecoverySource.position model start past material 0) = some renewal
  forward : ReconfirmationClosure.advances _ _ original (NativeRecoverySource.position model start past material 0) renewal = true
  noRenewal : Mandate.Challenge.readReconfirmation _ _ original (NativeRecoverySource.position model start past material 1) = none
  attempt : Mandate.Challenge.Attempt (NativeRecoverySource.family model start past material)
    (NativeRecoverySource.sourceIndex model start past material) renewal.target
  withdrawn : Mandate.Challenge.readAttempt _ _ renewal.target (NativeRecoverySource.position model start past material 1) = some attempt
  paid : model.source.code.law.Valid (attempt.position.item _ _).before (attempt.position.item _ _).request

def qualify (material : NativeRecoveryMaterial.Ready model start past)
    (original : NativeRecoverySource.Original model start past material) : Option (Qualified model start past material original) :=
  if old : original.position.ordinal < NativeRecoverySource.ordinal model start past then
  if pending : (NativeRecoverySource.before model start past material original).isPending _ _ = true then
  if stale : NativeRecoverySource.stale model start past material original = true then
  match renewed : Mandate.Challenge.readReconfirmation _ _ original (NativeRecoverySource.position model start past material 0) with
  | none => none
  | some renewal =>
    if forward : ReconfirmationClosure.advances _ _ original (NativeRecoverySource.position model start past material 0) renewal = true then
    match noRenewal : Mandate.Challenge.readReconfirmation _ _ original (NativeRecoverySource.position model start past material 1) with
    | some _ => none
    | none =>
      match withdrawn : Mandate.Challenge.readAttempt _ _ renewal.target (NativeRecoverySource.position model start past material 1) with
      | none => none
      | some attempt =>
        if paid : model.source.code.law.Valid (attempt.position.item _ _).before (attempt.position.item _ _).request then
          some ⟨old, pending, stale, renewal, renewed, forward, noRenewal, attempt, withdrawn, paid⟩
        else none
    else none
  else none
  else none
  else none

variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

structure Ready where
  private mk ::
  communication : UnifiedResponse.Clear model start vocabulary encoding law past
  queue : JointResponse.queueClear model start past = true
  material : NativeRecoveryMaterial.Ready model start past
  audit : (StageTrace.audit (NativeRecoveryMaterial.row model start past material)).all Prod.snd = true
  original : NativeRecoverySource.Original model start past material
  member : original ∈ NativeRecoverySource.originals model start past material
  qualified : Qualified model start past material original

inductive Obstruction where
  | communication | queue | material (reason : NativeRecoveryMaterial.Obstruction) | noStaleOriginal
  deriving DecidableEq
inductive Plan where
  | blocked (reason : Obstruction)
  | ready (answer : Ready model start past vocabulary encoding law)

def produce : Plan model start past vocabulary encoding law :=
  if communication : UnifiedResponse.Clear model start vocabulary encoding law past then
  if queue : JointResponse.queueClear model start past = true then
    match NativeRecoveryMaterial.produce model start past with
    | .blocked reason => .blocked (.material reason)
    | .ready material =>
      if audit : (StageTrace.audit (NativeRecoveryMaterial.row model start past material)).all Prod.snd = true then
        match (NativeRecoverySource.originals model start past material).attach.findSome? (fun original =>
            (qualify model start past material original.val).map fun qualified =>
              (⟨communication, queue, material, audit, original.val, original.property, qualified⟩ : Ready model start past vocabulary encoding law)) with
        | none => .blocked .noStaleOriginal
        | some answer => .ready answer
      else .blocked (.material .unpaid)
  else .blocked .queue
  else .blocked .communication

abbrev full (answer : Ready model start past vocabulary encoding law) := NativeRecoveryMaterial.full model start past answer.material

theorem the_recovery_word_has_actual_validity_for_every_original_item
    (answer : Ready model start past vocabulary encoding law) :
    ∀ item ∈ StageTrace.items (NativeRecoveryMaterial.row model start past answer.material),
      model.source.code.law.Valid item.before item.request := by
  intro item inside
  have paid := List.all_eq_true.mp answer.audit (item, decide (model.source.code.law.Valid item.before item.request))
    (List.mem_map.mpr ⟨item, inside, rfl⟩)
  exact of_decide_eq_true paid

theorem the_actual_reconfirmation_and_withdrawal_close_the_same_stale_original
    (answer : Ready model start past vocabulary encoding law) :
    (NativeRecoverySource.history model start past answer.material answer.original).isPending _ _ = false := by
  have terminal := ReconfirmationClosure.the_two_actual_positions_close_the_same_original
    (NativeRecoverySource.family model start past answer.material) (NativeRecoverySource.sourceIndex model start past answer.material)
    answer.original (NativeRecoverySource.position model start past answer.material 0) (NativeRecoverySource.position model start past answer.material 1)
    (NativeRecoverySource.the_two_positions_are_the_complete_actual_visit model start past answer.material)
    answer.qualified.renewal answer.qualified.renewed answer.qualified.forward answer.qualified.noRenewal
    answer.qualified.attempt answer.qualified.withdrawn (by rw [← model.law_exact]; exact answer.qualified.paid)
  have beyond := IncidentChallenge.actual_item_is_before_the_native_inventory model start (full model start past vocabulary encoding law answer)
    (NativeRecoveryMaterial.row model start past answer.material)
    (NativeRecoverySource.the_actual_row_is_in_the_complete_source model start past answer.material)
  apply WithdrawalHistory.terminal_through_persists _ _ answer.original _ _ terminal
  change NativeRecoverySource.ordinal model start past + 1 ≤ NativeRecoverySource.depth model start past answer.material + 2
  change NativeRecoverySource.ordinal model start past < NativeRecoverySource.depth model start past answer.material + 2 at beyond
  omega

theorem the_original_terminal_row_is_in_the_actual_full_inventory
    (answer : Ready model start past vocabulary encoding law) :
    ∃ row ∈ NativeReview.inventory model start (full model start past vocabulary encoding law answer),
      row.1 = answer.original ∧ row.2.isPending _ _ = false := by
  obtain ⟨row, member, same⟩ := List.mem_map.mp answer.member
  have closed := the_actual_reconfirmation_and_withdrawal_close_the_same_stale_original model start past vocabulary encoding law answer
  rw [← same] at closed
  refine ⟨row, member, same, ?_⟩
  obtain ⟨birth, birthInside, mapped⟩ := List.mem_flatMap.mp member
  obtain ⟨claim, claimInside, identity⟩ := List.mem_map.mp mapped
  cases identity
  exact closed

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeRecovery
