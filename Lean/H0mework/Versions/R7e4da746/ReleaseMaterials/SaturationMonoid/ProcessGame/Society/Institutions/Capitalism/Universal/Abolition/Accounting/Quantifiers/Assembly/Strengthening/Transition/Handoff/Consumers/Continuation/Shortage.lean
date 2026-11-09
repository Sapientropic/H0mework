import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation.Need
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Period

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Quantities Evolving.Epoch Actual
open Innovation.Contribution.Pricing.Root.Runtime (ReviewAvailable)

noncomputable section

local notation "Word" => [some (Compile.RawInput.execute withoutProvision)]

variable (cut : C)

local notation "Owner" => cut.native.input
local notation "Here" => cut.native.actual.snapshot

open private permitted_review_selects_the_period from H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Period

theorem a_missing_provision_is_actually_refused (owned : Owner = input) (raw : cut.raw = secondRaw)
    (ready : ¬ Pending cut) (review : ReviewAvailable cut) :
    (Execution.endAt cut Word).raw = cut.raw ∧
      Execution.inventory cut Word = [] ∧
      (∃ failed : MissingScope cut, shortage cut failed = some (false, .necessity, true, 1) ∧
        Public.Scope.failure? Owner cut.native.depth cut.native.count cut.native.prefixLimit
          cut.native.renewalLimit cut.native.oldPast Here (.execute withoutProvision) = some failed ∧
        Public.Scope.deferred Owner cut.native.depth cut.native.count cut.native.prefixLimit
          cut.native.renewalLimit cut.native.oldPast Here (.execute withoutProvision) = some (.execute withoutProvision)) ∧
      Recorded cut Word := by
  let query := Execution.query cut (some (.execute withoutProvision))
  obtain ⟨failed, generated, named⟩ := the_actual_scope_refuses_for_the_original_need cut owned raw
  have route : query.executionRaw = .execute withoutProvision :=
    permitted_review_selects_the_period cut withoutProvision review
  have readyQuery : ¬ Public.Inquiry.HasWork query.native.frame query.native.actual.actual := ready
  have effect := Public.Scope.an_actual_scope_rejection_cannot_advance_the_physical_current Owner
    cut.native.depth cut.native.count cut.native.prefixLimit cut.native.renewalLimit
    cut.native.oldPast Here (.execute withoutProvision) failed generated
  have report := Public.Scope.every_actual_rejection_stops_and_keeps_its_original_residual Owner
    cut.native.depth cut.native.count cut.native.prefixLimit cut.native.renewalLimit
    cut.native.oldPast Here (.execute withoutProvision) failed generated
  have sameMaterial : query.physicalResult.next.raw = cut.raw ∧
      query.physicalResult.execution.items = [] := by
    unfold Current.physicalResult
    rw [route]
    exact ⟨congrArg (fun physical => physical.raw) effect.1, effect.2⟩
  refine ⟨?_, ?_, ⟨failed, named, report.2⟩, record cut _⟩
  · change query.advance.raw = cut.raw
    rw [Current.advance_eq_epoch _ readyQuery, Transition.next_state_reads_the_same_actual_material_target query readyQuery]
    exact sameMaterial.1
  · change Optimality.Programme.Epoch.materialItems query ++ [] = []
    unfold Optimality.Programme.Epoch.materialItems
    rw [if_neg readyQuery, sameMaterial.2]
    rfl

theorem the_same_cut_refuses_the_unfunded_word_and_preserves_the_original_row :
    (Execution.endAt start Word).raw.clock = 6 ∧ Execution.inventory start Word = [] ∧
      (∃ failed : MissingScope start, shortage start failed = some (false, .necessity, true, 1) ∧
        Public.Scope.failure? start.native.input start.native.depth start.native.count start.native.prefixLimit
          start.native.renewalLimit start.native.oldPast start.native.actual.snapshot (.execute withoutProvision) = some failed ∧
        Public.Scope.deferred start.native.input start.native.depth start.native.count start.native.prefixLimit
          start.native.renewalLimit start.native.oldPast start.native.actual.snapshot (.execute withoutProvision) =
          some (.execute withoutProvision)) ∧ Recorded start Word := by
  have available : ReviewAvailable start := by
    unfold ReviewAvailable
    rw [start_control.2]
    trivial
  have rejected := a_missing_provision_is_actually_refused start start_input start_raw start_ready available
  exact ⟨(congrArg (fun raw => raw.clock) rejected.1).trans start_clock, rejected.2⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation
