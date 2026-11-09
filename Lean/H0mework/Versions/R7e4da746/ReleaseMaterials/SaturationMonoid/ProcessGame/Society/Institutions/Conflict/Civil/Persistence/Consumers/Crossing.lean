import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.AttackOrigin
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Evolving

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Consumers.Crossing

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Conflict.Consumers.Evolving

noncomputable section

abbrev opening : C := Conflict.Consumers.Evolving.source
abbrev cut : C := Root.terminal opening front
abbrev attempted : Option (Compile.RawInput Bool Bool Bool Unit Unit) := some (.primitive levy)
abbrev Move := Script Bool Bool Bool Unit Unit

private theorem tailTrace : Trace cut [levy, settle] (Root.terminal opening conflict) :=
  Root.trace_after_prefix opening (Root.terminal opening conflict) front [levy, settle] conflictPaid.trace

private theorem cut_exact :
    cut.native.input = compact ∧ cut.raw = ((Physical.Public.interpreter compact).execute oldRaw 0 front).final := by
  refine ⟨(Quantities.Execution.endAt_input opening _).trans sourceInput, ?_⟩
  rw [(Root.trace_before_prefix opening (Root.terminal opening conflict) front [levy, settle]
    conflictPaid.trace).raw_is_the_complete_original_execution 0, sourceInput, sourceRead]

private theorem original_levy_body :
    Boundary.Actual.items cut attempted = [⟨0, cut.raw, levy⟩] := by
  have guards : Ready cut ∧ ReviewAvailable cut ∧ levy.consents = [] ∧
      (Physical.Public.interpreter cut.native.input).Valid cut.raw levy := by
    cases tailTrace with
    | cons _ _ _ _ ready review consents valid _ => exact ⟨ready, review, consents, valid⟩
  have original := the_original_root_executes_the_generated_request cut levy guards.1 guards.2.1
    guards.2.2.1 guards.2.2.2
  change Optimality.Programme.Epoch.materialItems (queued cut levy) ++ [] = _
  rw [List.append_nil, Optimality.Programme.Epoch.materialItems,
    if_neg ((queued_is_ready_iff cut levy).mpr guards.1)]
  exact original.2.1

private def debitOrdinal : Fin (Boundary.Actual.items cut attempted).length :=
  ⟨0, by rw [original_levy_body]; decide⟩

private theorem exact_original_item :
    (Boundary.Actual.items cut attempted)[debitOrdinal] = ⟨0, cut.raw, levy⟩ := by
  have listed := List.getElem_mem (l := Boundary.Actual.items cut attempted) debitOrdinal.isLt
  exact List.mem_singleton.mp (original_levy_body ▸ listed)

def originalCrossing : Boundary.Actual.DamageAt cut attempted id :=
  ⟨(debitOrdinal, false, true, false), by
    change 0 < Reparation.loss (Physical.Public.interpreter cut.native.input) id
      (Boundary.Actual.items cut attempted)[debitOrdinal] (false, true, false)
    rw [exact_original_item, cut_exact.1, cut_exact.2]
    decide +kernel⟩

theorem the_original_levy_is_a_six_unit_loss_and_has_its_old_legal_guard :
    originalCrossing.quantity = 6 ∧ cut.native.input.law.Valid
      originalCrossing.item.before originalCrossing.item.request := by
  change Reparation.loss (Physical.Public.interpreter cut.native.input) id
      (Boundary.Actual.items cut attempted)[debitOrdinal] (false, true, false) = 6 ∧
    cut.native.input.law.Valid ((Boundary.Actual.items cut attempted)[debitOrdinal]).before
      ((Boundary.Actual.items cut attempted)[debitOrdinal]).request
  rw [exact_original_item, cut_exact.1, cut_exact.2]
  decide +kernel

def firstCrossing (tail : Move) :
    FirstFailure opening [] id false (Window.at cut) (attempted :: tail) :=
  ⟨[], attempted, tail, rfl, trivial, .attack originalCrossing⟩

/-- The original full restitution really pays. Checking its raw prefix
still identifies the first cross-community loss, at the original item. -/
theorem even_full_actual_restitution_cannot_hide_the_earlier_crossing :
    Quantities.Settled opening (Quantities.Execution.primitiveScript (restored 6)) ∧
      ¬ Checked opening [] id false (Window.at cut)
        (Quantities.Execution.primitiveScript [levy, settle, returnAt 6]) ∧
      Quantities.Recorded cut [attempted] :=
  ⟨fullReturnPaid.whole, (firstCrossing _).refutes, Quantities.record _ _⟩

theorem the_first_failure_is_the_original_six_unit_reparation_opening :
    let past := Quantities.Execution.primitiveScript front
    ∃ attack : OriginalAttack opening id (past ++ [attempted]),
      (firstCrossing []).originalAttack past rfl = some attack ∧
      attack.val.quantity = 6 ∧
      attack.val ∈ Reparation.Actual.openings opening id past attempted := by
  let past := Quantities.Execution.primitiveScript front
  let attack : OriginalAttack opening id (past ++ [attempted]) :=
    ⟨⟨past, attempted, originalCrossing⟩, rfl⟩
  exact ⟨attack, rfl, the_original_levy_is_a_six_unit_loss_and_has_its_old_legal_guard.1,
    attack.is_in_the_original_openings⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Consumers.Crossing
