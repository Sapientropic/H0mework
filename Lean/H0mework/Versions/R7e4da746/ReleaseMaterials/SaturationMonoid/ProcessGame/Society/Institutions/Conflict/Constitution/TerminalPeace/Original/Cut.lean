import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Consumers.Refusal

set_option autoImplicit false
set_option maxRecDepth 8192

open private physically_executed levy_inventory exact_levy_loss from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Consumers.ActualDamage

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Original

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Conflict.Consumers.Evolving (C compact destroy levy sourceInput sourceRead)
open Reparation.Consumers (actualOrigin withoutLivingPayment levyPast levyInput address)
open Quantities.Execution (endAt endAt_append endAt_input primitiveScript)

noncomputable section

abbrev Raw := RawCurrent Bool Bool Unit Unit
abbrev Item := ExecutionItem Bool Bool Bool Unit Unit
abbrev Word := Reparation.Actual.Script Bool Bool Bool Unit Unit

abbrev seed : C := actualOrigin
abbrev community : Bool → Bool := id
abbrev prior : Word := levyPast
abbrev attack := levyInput
abbrev before : C := endAt seed prior

/-- This prefix ends at the actual material write, before its already
generated native accounting input. -/
def born : Word := prior ++ [attack]

/-- This is the rejected assault's real physical history, including the
original accounting step. Its unmet living floor remains visible. -/
def history : Word := primitiveScript withoutLivingPayment

theorem exact_history : history = born ++ [none] := rfl

abbrev cut : C := endAt seed history

theorem actual_trace : Trace seed withoutLivingPayment cut := physically_executed

theorem same_source : cut.native.input = compact := (endAt_input seed history).trans sourceInput

theorem prior_source : before.native.input = compact := (endAt_input seed prior).trans sourceInput

theorem original_levy_items : Boundary.Actual.items before attack = [⟨0, before.raw, levy⟩] :=
  levy_inventory

def position : Fin (Boundary.Actual.items before attack).length :=
  ⟨0, by rw [original_levy_items]; decide⟩

theorem item_is_literal (site : Fin (Boundary.Actual.items before attack).length) :
    (Boundary.Actual.items before attack)[site] = ⟨0, before.raw, levy⟩ := by
  have original : (Boundary.Actual.items before attack)[site] ∈ Boundary.Actual.items before attack :=
    List.getElem_mem _
  exact List.mem_singleton.mp
    ((congrArg (fun rows => (Boundary.Actual.items before attack)[site] ∈ rows) original_levy_items).mp original)

def damage : Boundary.Actual.DamageAt before attack community :=
  ⟨(position, address), by
    change 0 < Reparation.loss (Boundary.Actual.materialLaw before) id
      (Boundary.Actual.items before attack)[position] address
    rw [item_is_literal, exact_levy_loss]
    norm_num⟩

def occurrence : Reparation.Actual.Occurrence seed community := ⟨prior, attack, damage⟩

theorem loss_six : occurrence.quantity = 6 := by
  change Reparation.loss (Boundary.Actual.materialLaw before) id
    (Boundary.Actual.items before attack)[position] address = 6
  rw [item_is_literal, exact_levy_loss]

theorem exact_address : occurrence.address = (2, 0, (false, true, false)) := rfl

theorem original_victim : occurrence.key.1 = false := rfl

theorem exact_damage_item : occurrence.damage.item = ⟨0, before.raw, levy⟩ := item_is_literal position

private theorem levy_trace : Trace before [levy] cut :=
  Conflict.Root.trace_after_prefix seed _ [destroy] [levy] actual_trace

theorem levy_native_has_no_second_item : Boundary.Actual.items (endAt seed born) none = [] := by
  have source := levy_trace.a_nonempty_execution_starts_at_the_actual_ready_boundary (by simp)
  have original := levy_trace.every_original_instruction_has_its_actual_guards 0
    ⟨0, before.raw, levy⟩ List.mem_cons_self
  have work := the_actual_body_must_consume_its_original_native_head before levy
    source.1 source.2 original.2 original.1
  rw [born, endAt_append]
  exact Reparation.Transport.native_step_has_no_material_items none work

theorem ready : Ready cut := by
  have source := levy_trace.a_nonempty_execution_starts_at_the_actual_ready_boundary (by simp)
  have original := levy_trace.every_original_instruction_has_its_actual_guards 0
    ⟨0, before.raw, levy⟩ List.mem_cons_self
  exact (two_actual_root_steps_pay_and_consume_the_generated_primitive before levy
    source.1 source.2 original.2 original.1).1

theorem review : ReviewAvailable cut := by
  have source := levy_trace.a_nonempty_execution_starts_at_the_actual_ready_boundary (by simp)
  have original := levy_trace.every_original_instruction_has_its_actual_guards 0
    ⟨0, before.raw, levy⟩ List.mem_cons_self
  exact afterNative_keeps_the_available_review before levy source.1 source.2 original.2 original.1

/-- Stock entries are from the literal original operation fold. The
financial principal at the old slot stays separate from the filed loss. -/
def snapshot (exposed controller : ℚ) : Raw :=
  ⟨fun person good => if good then 1 else if person then controller else exposed,
    fun _ debtor creditor => if debtor = true ∧ creditor = false then 6 else 0, (), 4, 4⟩

theorem before_raw : before.raw = snapshot 117 107 := by
  have trace := Conflict.Root.trace_before_prefix seed _ [destroy] [levy] actual_trace
  have raw := trace.raw_is_the_complete_original_execution 0
  change before.raw = _ at raw
  rw [raw, sourceInput, sourceRead]
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;> decide +kernel
  · funext instrument debtor creditor
    cases instrument
    cases debtor <;> cases creditor <;> decide +kernel
  · exact Subsingleton.elim _ _
  · decide +kernel
  · decide +kernel

theorem cut_raw : cut.raw = snapshot 111 113 := by
  have raw := actual_trace.raw_is_the_complete_original_execution 0
  change cut.raw = _ at raw
  rw [raw, sourceInput, sourceRead]
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;> decide +kernel
  · funext instrument debtor creditor
    cases instrument
    cases debtor <;> cases creditor <;> decide +kernel
  · exact Subsingleton.elim _ _
  · decide +kernel
  · decide +kernel

theorem the_original_cut_still_owes_the_living_payment : ¬ Quantities.Feasible seed history :=
  Reparation.Consumers.the_actual_assault_leaves_its_living_payment_unfulfilled

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Original
