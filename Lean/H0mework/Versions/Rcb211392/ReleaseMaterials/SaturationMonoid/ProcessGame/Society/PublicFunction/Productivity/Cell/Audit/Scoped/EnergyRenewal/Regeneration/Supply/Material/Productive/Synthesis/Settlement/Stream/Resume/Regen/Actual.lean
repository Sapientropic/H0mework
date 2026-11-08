import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Resume.Regen.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Runtime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {seed : Seed} {oldRequests : Requests.Source} {oldMode : Material.Mode} {cut : Nat}
  (previous : Inherited seed oldRequests oldMode cut)
  (requests : Requests.Source) (authority : Authority)

theorem the_first_tick_starts_on_the_original_generated_next :
    HEq (activated previous requests authority 0).current.visit.current
      (Resume.Runtime.activated seed oldRequests oldMode cut).tick.nextCurrent.visit.current := by
  rw [(Resume.Runtime.same_occurrence_whole_ledger_and_own_next seed oldRequests oldMode cut).2.2]
  change HEq (ProgrammeHistory.visitAt (input previous requests authority) (cut + 1)).current
    (ProgrammeHistory.visitAt (Resume.input seed oldRequests oldMode)
      ((show Nat from (Resume.Runtime.activated seed oldRequests oldMode cut).state) + 1)).current
  rw [Resume.Runtime.activated_state]
  exact heq_of_eq (original_current_prefix previous requests authority _ (le_refl _))

def actualRun (ordinal : Nat) :
    (Financial.Family.process Finance.sources).Run previous.result.account.current
      (consume previous requests authority ordinal).account.current := by
  rw [(consume previous requests authority ordinal).accountExact]
  exact familyRun previous requests authority ordinal

theorem original_admissions_keep_their_positions (ordinal : Nat) :
    previous.result.account.current.slots.map (Financial.Family.slotClaim Finance.sources) <+:
      (consume previous requests authority ordinal).account.current.slots.map
        (Financial.Family.slotClaim Finance.sources) := by
  rw [(consume previous requests authority ordinal).accountExact]
  exact Financial.Family.continueVisits_preserves_original_claims Finance.sources
    (input previous requests authority) (cut + 1) (ordinal + 1) previous.result.account

theorem original_native_history_is_preserved (ordinal : Nat) :
    previous.result.account.current.history <+: (consume previous requests authority ordinal).account.current.history := by
  rw [(actualRun previous requests authority ordinal).history_eq]
  exact List.prefix_append _ _

theorem all_original_paid_receipts_stay_at_their_positions (ordinal index : Nat)
    (archive : TerminalArchive (Financial.Family.vocabulary Finance.sources))
    (present : previous.result.account.current.slots[index]? = some (.terminal archive)) :
    (consume previous requests authority ordinal).account.current.slots[index]? = some (.terminal archive) := by
  let carried := Financial.Family.Migration.follow Finance.sources
    (actualRun previous requests authority ordinal) index (.terminal archive) present
  exact carried.present.trans (congrArg some (carried.path.terminal_is_unchanged Finance.sources))

theorem actual_before_is_the_same_old_stream_position (ordinal : Nat) :
    (execution previous requests authority ordinal).before = (run previous requests authority ordinal).raw := by
  change ProgrammeSource.rawCurrent (input previous requests authority)
    (ProgrammeHistory.visitAt (input previous requests authority)
      (cut + 1 + (show Nat from (activated previous requests authority ordinal).state))).current = _
  rw [activated_state]
  exact own_current previous requests authority ordinal

theorem actual_word_comes_from_the_original_policy (ordinal : Nat) :
    (execution previous requests authority ordinal).submitted =
      word seed requests authority (ordinal + 1) (run previous requests authority ordinal) := by
  change ProgrammeSource.rawEvent (input previous requests authority)
    (ProgrammeHistory.visitAt (input previous requests authority)
      (cut + 1 + (show Nat from (activated previous requests authority ordinal).state))).current = _
  rw [activated_state, selected_word_at_cut]

theorem actual_refeed_keeps_the_original_request_protocol (ordinal : Nat)
    (repair : needsOriginalRefeed seed requests (ordinal + 1) (run previous requests authority ordinal) = true) :
    (consume previous requests authority ordinal).frame.protocol = (run previous requests authority ordinal).protocol := by
  rw [(consume previous requests authority ordinal).frameExact]
  exact original_repair_holds_the_request_and_its_deadline seed requests authority (ordinal + 1)
    (run previous requests authority ordinal) repair

def actualRefusal (ordinal : Nat) :=
  firstRefusal seed.basis.origin.scope (execution previous requests authority ordinal).interpreted.items

def actualRegeneration (ordinal : Nat) :
    Option {row : Item //
      row ∈ (execution previous requests authority ordinal).interpreted.items ∧
      row.request = liftProvider row.before Refeed.recycle ∧
      (law seed.basis.origin.scope).Valid row.before row.request} :=
  (execution previous requests authority ordinal).interpreted.items.attach.findSome? fun row =>
    if paid : row.val.request = liftProvider row.val.before Refeed.recycle ∧
        (law seed.basis.origin.scope).Valid row.val.before row.val.request then
      some ⟨row.val, row.property, paid⟩
    else none

theorem the_recycle_command_is_signed_at_the_original_donor (current : Current) :
    (liftProvider current Refeed.recycle).signer = Refeed.donor ∧
      (liftProvider current Refeed.recycle).operation = .produce Refeed.donor := ⟨rfl, rfl⟩

theorem the_transport_command_uses_the_original_feed_address (current : Current) :
    (liftProvider current Refeed.transport).operation = .transfer Refeed.donor supplier [(.feed, 1)] := rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Runtime
