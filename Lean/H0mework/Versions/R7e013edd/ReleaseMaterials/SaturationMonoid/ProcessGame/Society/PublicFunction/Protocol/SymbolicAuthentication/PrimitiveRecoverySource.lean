import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PrimitiveRecoveryPair

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PrimitiveRecoverySource

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)

variable (past : JointResponse.Stages model)
abbrev current := PrimitiveRecoveryPair.current model start past
abbrev full (worker : Fin model.source.code.sites) := PrimitiveRecoveryPair.full model start past worker
abbrev native (worker : Fin model.source.code.sites) := IncidentChallenge.native model start (full model start past worker)
abbrev family (worker : Fin model.source.code.sites) := IncidentChallenge.family model start (full model start past worker)
abbrev inputs (worker : Fin model.source.code.sites) := IncidentChallenge.sourceIndex model start (full model start past worker)
abbrev Original (worker : Fin model.source.code.sites) := Native.Authority.Challenge (native model start past worker)
abbrev originals (worker : Fin model.source.code.sites) := (NativeReview.inventory model start (full model start past worker)).map Sigma.fst
abbrev cut := EventStep.boundary (EventHistory.execute start past)
abbrev before (worker : Fin model.source.code.sites) (original : Original model start past worker) :=
  Mandate.Challenge.through (family model start past worker) (inputs model start past worker) original (cut model start past)
def stale (worker : Fin model.source.code.sites) (original : Original model start past worker) : Bool :=
  match before model start past worker original with
  | .closed .. => false
  | .pending target .. => decide ((target.claim _ _).snapshot _ _ ≠ (current model start past).current.technology)

structure Conditions (worker : Fin model.source.code.sites) (original : Original model start past worker) : Prop where
  resources : PrimitiveRecoveryPair.Resources model start past worker
  signature : model.source.code.law.Valid (current model start past).current (WithdrawalInquiry.reaffirm model worker)
  withdrawal : model.source.code.law.Valid (current model start past).current (PrimitiveRecoveryPair.request model start past worker)
  active : (current model start past).current.technology.holder.isSome = true ∨
    (current model start past).current.technology.offered.isSome = true
  old : original.position.ordinal < cut model start past
  pending : (before model start past worker original).isPending (family model start past worker) (inputs model start past worker) = true
  signer : model.source.code.siteParty worker = original.signer (family model start past worker) (inputs model start past worker)
  stale : stale model start past worker original = true

instance (worker : Fin model.source.code.sites) (original : Original model start past worker) :
    Decidable (Conditions model start past worker original) :=
  decidable_of_iff
    (PrimitiveRecoveryPair.Resources model start past worker ∧
      model.source.code.law.Valid (current model start past).current (WithdrawalInquiry.reaffirm model worker) ∧
      model.source.code.law.Valid (current model start past).current (PrimitiveRecoveryPair.request model start past worker) ∧
      ((current model start past).current.technology.holder.isSome = true ∨
        (current model start past).current.technology.offered.isSome = true) ∧
      original.position.ordinal < cut model start past ∧
      (before model start past worker original).isPending (family model start past worker) (inputs model start past worker) = true ∧
      model.source.code.siteParty worker = original.signer (family model start past worker) (inputs model start past worker) ∧
      stale model start past worker original = true)
    ⟨fun h => by rcases h with ⟨a,b,c,d,e,f,g,h⟩; exact ⟨a,b,c,d,e,f,g,h⟩,
      fun h => ⟨h.resources,h.signature,h.withdrawal,h.active,h.old,h.pending,h.signer,h.stale⟩⟩

variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

structure Source where
  private mk ::
  unfinished : ¬ JointResponse.Clear model start vocabulary encoding law past
  communication : UnifiedResponse.Clear model start vocabulary encoding law past
  queue : JointResponse.queueClear model start past = true
  worker : Fin model.source.code.sites
  original : Original model start past worker
  member : original ∈ originals model start past worker
  conditions : Conditions model start past worker original

-- Scan the actual source and finite local-information fibre; no Ready/receipt is supplied.
def produce : Option (Source model start past vocabulary encoding law) :=
  if unfinished : ¬ JointResponse.Clear model start vocabulary encoding law past then
  if communication : UnifiedResponse.Clear model start vocabulary encoding law past then
  if queue : JointResponse.queueClear model start past = true then
  match Distributed.Recall.Information.Agency.ownerAt model.source.code (EventHistory.execute start past).ownerStart
      (current model start past).history.length with
  | none => none
  | some worker => (originals model start past worker).attach.findSome? fun original =>
      if conditions : Conditions model start past worker original.val then
        some ⟨unfinished, communication, queue, worker, original.val, original.property, conditions⟩ else none
  else none else none else none

theorem primitive_fields_generate_the_original_raw_conditions
    (material : NativeRecoveryMaterial.Ready model start past)
    (original : Original model start past material.worker)
    (conditions : Conditions model start past material.worker original) :
    RawNativeService.conditions model start past material original ∧
    (StageTrace.audit (NativeRecoveryMaterial.row model start past material)).all Prod.snd = true := by
  have items := PrimitiveRecoveryPair.primitive_local_resources_generate_both_exact_raw_items
    model start past material.worker conditions.resources
  have first := IncidentChallenge.position_item_is_the_actual_item model start (NativeRecoverySource.full model start past material)
    (NativeRecoverySource.row model start past material)
    (NativeRecoverySource.the_actual_row_is_in_the_complete_source model start past material)
    ⟨0, by rw [NativeRecoveryMaterial.the_actual_row_has_exactly_two_items]; decide⟩
  have second := IncidentChallenge.position_item_is_the_actual_item model start (NativeRecoverySource.full model start past material)
    (NativeRecoverySource.row model start past material)
    (NativeRecoverySource.the_actual_row_is_in_the_complete_source model start past material)
    ⟨1, by rw [NativeRecoveryMaterial.the_actual_row_has_exactly_two_items]; decide⟩
  have firstExact : (NativeRecoverySource.position model start past material 0).item
      (NativeRecoverySource.family model start past material) (NativeRecoverySource.sourceIndex model start past material) =
      ⟨0, (current model start past).current, WithdrawalInquiry.reaffirm model material.worker⟩ := by
    dsimp only [NativeRecoverySource.position, NativeRecoverySource.family, NativeRecoverySource.sourceIndex]
    simpa only [Fin.val_zero, List.get_eq_getElem, items, List.getElem_cons_zero] using first
  have secondExact : (NativeRecoverySource.position model start past material 1).item
      (NativeRecoverySource.family model start past material) (NativeRecoverySource.sourceIndex model start past material) =
      ⟨1, (current model start past).current, PrimitiveRecoveryPair.request model start past material.worker⟩ := by
    dsimp only [NativeRecoverySource.position, NativeRecoverySource.family, NativeRecoverySource.sourceIndex]
    simpa only [Fin.val_one, List.get_eq_getElem, items, List.getElem_cons_succ, List.getElem_cons_zero] using second
  have signature : (Mandate.law model.base model.scope).Valid (current model start past).current
      (WithdrawalInquiry.reaffirm model material.worker) := by rw [← model.law_exact]; exact conditions.signature
  have withdrawal : (Mandate.law model.base model.scope).Valid (current model start past).current
      (PrimitiveRecoveryPair.request model start past material.worker) := by rw [← model.law_exact]; exact conditions.withdrawal
  refine ⟨{
    old := conditions.old
    pending := conditions.pending
    sameVisit := rfl
    ordered := by change (0 : Nat) < 1; omega
    signed := ?_
    accepted := ?_
    active := ?_
    signer := ?_
    withdrawal := ?_
    snapshot := ?_
    paid := ?_ }, ?_⟩
  · rw [firstExact]; exact ⟨conditions.resources.member, rfl, rfl, rfl, trivial⟩
  · rw [firstExact]; exact signature
  · rw [firstExact]; exact conditions.active
  · rw [firstExact]; exact conditions.signer
  · rw [secondExact]
    exact ⟨rfl, rfl, rfl, rfl, Or.inl ⟨conditions.resources.member, rfl⟩⟩
  · rw [firstExact, secondExact]
  · rw [secondExact]; exact withdrawal
  · change ((StageTrace.items (PrimitiveRecoveryPair.row model start past material.worker)).map
      (fun item => (item, decide (model.source.code.law.Valid item.before item.request)))).all Prod.snd = true
    rw [items]
    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      decide_eq_true conditions.signature, decide_eq_true conditions.withdrawal, Bool.true_and]

theorem actual_source_primitives_generate_raw_admission
    (source : Source model start past vocabulary encoding law) :
    (RawNativeService.produce model start past vocabulary encoding law).isSome = true := by
  rcases source with ⟨unfinished, communication, queue, worker, original, member, conditions⟩
  obtain ⟨material, selected, same⟩ := PrimitiveRecoveryPair.actual_primitives_generate_the_original_material
    model start past worker conditions.resources
  subst worker
  obtain ⟨raw, audit⟩ := primitive_fields_generate_the_original_raw_conditions model start past material original conditions
  have isStale : NativeRecoverySource.stale model start past material original = true := by
    unfold NativeRecoverySource.stale
    change (match before model start past material.worker original with
      | .closed .. => false
      | .pending target .. => decide ((target.claim _ _).snapshot _ _ ≠ (current model start past).current.technology)) = true
    have previous := conditions.stale
    unfold stale at previous
    cases history : before model start past material.worker original with
    | closed state archive slots => simp only [history, Bool.false_eq_true] at previous
    | pending target state slots =>
      rw [history] at previous
      dsimp only at previous ⊢
      exact decide_eq_true (of_decide_eq_true previous)
  cases outcome : RawNativeService.produce model start past vocabulary encoding law with
  | some value => rfl
  | none =>
    exfalso
    unfold RawNativeService.produce at outcome
    simp only [dif_pos unfinished, dif_pos communication, dif_pos queue] at outcome
    split at outcome
    · rename_i reason found
      have impossible := found.symm.trans selected
      cases impossible
    · rename_i chosen found
      have same := NativeRecoveryMaterial.Plan.ready.inj (found.symm.trans selected)
      subst chosen
      simp only [dif_pos audit] at outcome
      have impossible := List.findSome?_eq_none_iff.mp outcome ⟨original, member⟩ (List.mem_attach _ _)
      simp only [dif_pos raw, dif_pos isStale, Option.some_ne_none] at impossible

theorem every_actual_primitive_claim_is_found
    (unfinished : ¬ JointResponse.Clear model start vocabulary encoding law past)
    (communication : UnifiedResponse.Clear model start vocabulary encoding law past)
    (queue : JointResponse.queueClear model start past = true)
    (worker : Fin model.source.code.sites) (original : Original model start past worker)
    (member : original ∈ originals model start past worker)
    (conditions : Conditions model start past worker original) :
    (produce model start past vocabulary encoding law).isSome = true := by
  unfold produce
  simp only [dif_pos unfinished, dif_pos communication, dif_pos queue, conditions.resources.owned]
  cases selected : (originals model start past worker).attach.findSome? (fun original =>
      if conditions : Conditions model start past worker original.val then
        some (Source.mk unfinished communication queue worker original.val original.property conditions) else none) with
  | some source => rfl
  | none =>
    have absent := List.findSome?_eq_none_iff.mp selected ⟨original, member⟩ (List.mem_attach _ _)
    simp only [dif_pos conditions, Option.some_ne_none] at absent

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PrimitiveRecoverySource
