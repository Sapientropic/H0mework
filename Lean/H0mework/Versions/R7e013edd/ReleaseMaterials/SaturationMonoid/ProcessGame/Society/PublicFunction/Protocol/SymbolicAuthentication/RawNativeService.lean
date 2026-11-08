import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RawNativeReconfirmation

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RawNativeService
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open Mandate.Challenge

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (past : JointResponse.Stages model)

abbrev conditions (material : NativeRecoveryMaterial.Ready model start past)
    (original : NativeRecoverySource.Original model start past material) :=
  RawNativeReconfirmation.Conditions (NativeRecoverySource.family model start past material)
    (NativeRecoverySource.sourceIndex model start past material) original
    (NativeRecoverySource.position model start past material 0) (NativeRecoverySource.position model start past material 1)

theorem raw_source_conditions_generate_the_original_qualification
    (material : NativeRecoveryMaterial.Ready model start past)
    (original : NativeRecoverySource.Original model start past material)
    (raw : conditions model start past material original)
    (stale : NativeRecoverySource.stale model start past material original = true) :
    ∃ qualified, NativeRecovery.qualify model start past material original = some qualified := by
  obtain ⟨receipt, renewed, _, forward, noRenewal, attempt, withdrawn, paid⟩ :=
    RawNativeReconfirmation.raw_items_generate_the_same_original_reconfirmation_and_paid_attempt
      (NativeRecoverySource.family model start past material) (NativeRecoverySource.sourceIndex model start past material)
      original _ _ raw
  have actualPaid : model.source.code.law.Valid (attempt.position.item _ _).before (attempt.position.item _ _).request := by
    rw [model.law_exact]; exact paid
  have old : original.position.ordinal < NativeRecoverySource.ordinal model start past := raw.old
  have pending : (NativeRecoverySource.before model start past material original).isPending _ _ = true := raw.pending
  simp only [NativeRecovery.qualify, dif_pos old, dif_pos pending, dif_pos stale]
  split
  · rename_i missing
    have impossible := missing.symm.trans renewed
    cases impossible
  · rename_i renewal found
    have same := Option.some.inj (found.symm.trans renewed)
    subst renewal
    split
    · split
      · rename_i unexpected found
        have impossible := found.symm.trans noRenewal
        cases impossible
      · split
        · rename_i missing
          have impossible := missing.symm.trans withdrawn
          cases impossible
        · rename_i selected found
          have same := Option.some.inj (found.symm.trans withdrawn)
          subst selected
          split
          · exact ⟨_, rfl⟩
          · rename_i absent; exact False.elim (absent actualPaid)
    · rename_i absent; exact False.elim (absent forward)

variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

structure Source where
  private mk ::
  unfinished : ¬ JointResponse.Clear model start vocabulary encoding law past
  communication : UnifiedResponse.Clear model start vocabulary encoding law past
  queue : JointResponse.queueClear model start past = true
  material : NativeRecoveryMaterial.Ready model start past
  selected : NativeRecoveryMaterial.produce model start past = .ready material
  audit : (StageTrace.audit (NativeRecoveryMaterial.row model start past material)).all Prod.snd = true
  original : NativeRecoverySource.Original model start past material
  member : original ∈ NativeRecoverySource.originals model start past material
  raw : conditions model start past material original
  stale : NativeRecoverySource.stale model start past material original = true

-- This reads actual original items, not a supplied lifecycle receipt or a terminal certificate.
def produce : Option (Source model start past vocabulary encoding law) :=
  if unfinished : ¬ JointResponse.Clear model start vocabulary encoding law past then
  if communication : UnifiedResponse.Clear model start vocabulary encoding law past then
  if queue : JointResponse.queueClear model start past = true then
  match selected : NativeRecoveryMaterial.produce model start past with
  | .blocked _ => none
  | .ready material =>
    if audit : (StageTrace.audit (NativeRecoveryMaterial.row model start past material)).all Prod.snd = true then
      (NativeRecoverySource.originals model start past material).attach.findSome? fun original =>
        if raw : conditions model start past material original.val then
        if stale : NativeRecoverySource.stale model start past material original.val = true then
          some ⟨unfinished, communication, queue, material, selected, audit, original.val, original.property, raw, stale⟩
        else none else none
    else none
  else none else none else none

theorem the_actual_raw_source_forces_the_original_recovery
    (source : Source model start past vocabulary encoding law) :
    ∃ answer, NativeRecovery.produce model start past vocabulary encoding law = .ready answer := by
  obtain ⟨qualified, checked⟩ := raw_source_conditions_generate_the_original_qualification model start past
    source.material source.original source.raw source.stale
  unfold NativeRecovery.produce
  simp only [dif_pos source.communication, dif_pos source.queue, source.selected, dif_pos source.audit]
  split
  · rename_i missing
    have absent := List.findSome?_eq_none_iff.mp missing
      ⟨source.original, source.member⟩ (List.mem_attach _ _)
    simp only [checked, Option.map_some] at absent
    cases absent
  · exact ⟨_, rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RawNativeService
