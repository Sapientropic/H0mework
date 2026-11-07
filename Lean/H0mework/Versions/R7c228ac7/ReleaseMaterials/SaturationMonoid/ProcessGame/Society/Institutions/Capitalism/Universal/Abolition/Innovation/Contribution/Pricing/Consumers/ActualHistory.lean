import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.ActualReadback

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Abolition.Accounting.Quantifiers
open Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material
noncomputable section

private theorem native_snapshot_is_retained
    (current : Evolving.Epoch.Current (Party := Bool) (Good := Bool) (Port := Bool)
      (Technology := Unit) (Instrument := Unit))
    (work : Public.Inquiry.HasWork current.native.frame current.native.actual.actual) :
    current.advance.native.actual.snapshot = current.native.actual.snapshot := by
  have start : current.advance.native.start = current.native.start := by
    unfold Evolving.Epoch.Current.advance
    rw [dif_pos work]
    cases Public.Accounting.registration? current.native.input current.native.depth current.native.count
      current.native.prefixLimit current.native.renewalLimit current.native.oldPast current.native.start
      current.native.actual.actual <;> rfl
  unfold Public.Inquiry.ActualAt.snapshot
  rw [current.advance.native.bodyPaid,current.native.bodyPaid]
  rw [start]

theorem the_real_repair_keeps_each_original_consumed_input
    (raw : Compile.RawInput Bool Bool Bool Unit Unit) (old : raw ∈ base.native.actual.snapshot.past) :
    raw ∈ source.native.actual.snapshot.past := by
  have work := Root.Runtime.the_actual_body_must_consume_its_original_native_head base
    Evolving.Epoch.Consumers.repair base_ready base_review rfl the_original_food_repair_is_actually_payable
  have stable := congrArg Physical.Cursor.past (native_snapshot_is_retained _ work)
  have first := Evolving.Epoch.Transition.next_snapshot_keeps_the_one_actual_effective_input
    (Root.Runtime.queued base Evolving.Epoch.Consumers.repair) base_ready
  rw [← Evolving.Epoch.Current.advance_eq_epoch
    (Root.Runtime.queued base Evolving.Epoch.Consumers.repair) base_ready] at first
  have kept : raw ∈ (Root.Runtime.queued base Evolving.Epoch.Consumers.repair).advance.native.actual.snapshot.past :=
    (congrArg (fun history => raw ∈ history) first).mpr (List.mem_append_left _ old)
  exact (congrArg (fun history => raw ∈ history) stable).mpr kept

theorem the_original_paid_programme_is_still_in_the_actual_quote_history :
    .execute Original.defaultWord ∈ source.native.actual.snapshot.past := by
  apply the_real_repair_keeps_each_original_consumed_input
  have code := Evolving.Epoch.Transition.next_snapshot_keeps_the_one_actual_effective_input
    Evolving.Epoch.Consumers.current Evolving.Epoch.Consumers.original_complete
  have original : .execute Original.defaultWord ∈ Evolving.Epoch.Consumers.current.native.actual.snapshot.past := by
    have paid := (Runtime.Drain.the_finite_source_loop_finishes_at_the_original_native_consumption
      Original.seed Original.grossClaim).2.2
    change .execute Original.defaultWord ∈ (if (Runtime.Drain.completed Original.seed Original.grossClaim).bodyPaid
      then Physical.next (Runtime.cursor Original.seed Original.grossClaim)
      else Runtime.cursor Original.seed Original.grossClaim).past
    rw [paid,if_pos rfl]
    change .execute Original.defaultWord ∈ (Runtime.cursor Original.seed Original.grossClaim).past ++
      [.execute (word Original.seed Original.grossClaim)]
    apply List.mem_append_right
    have actual : word Original.seed Original.grossClaim = Original.defaultWord :=
      the_actual_original_selected_word_is_not_recomputed
    rw [actual]
    exact List.mem_singleton_self _
  exact (congrArg (fun history => .execute Original.defaultWord ∈ history) code).mpr
    (List.mem_append_left _ original)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual

-- Suggestion-index traversal unfolds these concrete currents too deeply.
run_cmd Lean.modifyEnv fun env =>
  let names := ["the_real_repair_keeps_each_original_consumed_input",
    "the_original_paid_programme_is_still_in_the_actual_quote_history"]
  names.foldl (fun env name => Lean.LibrarySuggestions.nameDenyListExt.addEntry env name) env
