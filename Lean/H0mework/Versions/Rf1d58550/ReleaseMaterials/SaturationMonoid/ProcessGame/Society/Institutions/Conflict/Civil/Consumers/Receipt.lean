import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Consumers.Words
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.PrimitiveClock

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Consumers

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Conflict.Consumers.Evolving
open Quantities

noncomputable section

abbrev exitCut := Root.terminal opening (intervention ++ calm)
abbrev exitScript := Execution.primitiveScript exit

theorem original_exit_trace : Trace exitCut exit (Root.terminal opening ((intervention ++ calm) ++ exit)) :=
  Root.trace_after_prefix opening _ (intervention ++ calm) exit the_peace_exit_is_paid_after_the_citizen_invests.trace

private theorem the_exit_cut_is_literal : exitCut.raw =
    ((Physical.Public.interpreter compact).execute oldRaw 0 (intervention ++ calm)).final := by
  have first := Root.trace_before_prefix opening _ (intervention ++ calm) exit
    the_peace_exit_is_paid_after_the_citizen_invests.trace
  rw [first.raw_is_the_complete_original_execution 0, sourceInput, sourceRead]

private theorem exit_cut_input : exitCut.native.input = compact :=
  (Execution.endAt_input opening _).trans sourceInput

private theorem the_exit_has_one_original_paid_inventory_position :
    Execution.inventory exitCut exitScript = [⟨0, exitCut.raw, life false⟩] := by
  rw [Execution.primitive_inventory original_exit_trace 0]
  rfl

private theorem the_original_exit_service_is_matched : Clock.FullyServed exitCut task exitScript := by
  let geometry := Clock.geometry exitCut task exitScript
  have inRange : 0 < (Execution.inventory exitCut exitScript).length := by
    rw [the_exit_has_one_original_paid_inventory_position]
    decide
  let position : Fin (Execution.inventory exitCut exitScript).length := ⟨0, inRange⟩
  have item : (Execution.inventory exitCut exitScript).get position = ⟨0, exitCut.raw, life false⟩ := by
    rw [List.get_eq_getElem]
    apply Option.some.inj
    calc
      _ = (Execution.inventory exitCut exitScript)[0]? := (List.getElem?_eq_getElem inRange).symm
      _ = _ := by rw [the_exit_has_one_original_paid_inventory_position]; rfl
  apply (Clock.fully_served_iff_the_original_capacity_covers_every_slot _ _ _).mpr
  apply Clock.distinct_paid_positions_cover_the_original_services geometry (fun _ => position)
  · intro left _ right _ _
    apply Fin.ext
    have l : left.val < 1 := left.isLt
    have r : right.val < 1 := right.isLt
    omega
  · intro slot _
    have unique : slot = ⟨0, by decide⟩ := by
      apply Fin.ext
      change slot.val = 0
      have bound : slot.val < 1 := slot.isLt
      omega
    subst slot
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold geometry Clock.geometry Clock.geometryOf
    dsimp only
    rw [item, exit_cut_input, the_exit_cut_is_literal]
    decide +kernel

private theorem the_original_exit_floor_is_paid :
    Boundary.floorPaid opening exitCut (protectedMembers opening command) exit := by
  intro cell listed
  obtain ⟨original, resident⟩ := List.mem_filter.mp listed
  have independent := of_decide_eq_true (List.mem_filter.mp (of_decide_eq_true resident)).2
  obtain ⟨bearer, _, need⟩ := List.mem_flatMap.mp original
  rw [sourceInput] at need
  change cell ∈ [(bearer, .necessity, true, amount Bool [(true, 1)] true)] at need
  have exactCell := List.mem_singleton.mp need
  rw [exactCell] at independent
  have same : bearer = false := by cases bearer <;> simp_all [command]
  subst bearer
  rw [exactCell]
  unfold Boundary.deliveredAt
  rw [Demand.delivered_is_from_original_inventory, the_exit_has_one_original_paid_inventory_position]
  change _ ≤ ([(⟨0, exitCut.raw, life false⟩ : ExecutionItem Bool Bool Bool Unit Unit)].map
    (fun item => flowAt (Optimality.Cost.actualPart (Physical.Public.interpreter exitCut.native.input)
      item.before item.request (.use .necessity)) false true)).sum
  rw [exit_cut_input, the_exit_cut_is_literal]
  decide +kernel

theorem the_citizen_keeps_and_spends_her_original_independent_exit :
    ExitAt opening command task (intervention ++ calm) exit := by
  refine ⟨the_peace_exit_is_paid_after_the_citizen_invests, ?_, ?_, ?_, ?_, the_original_exit_floor_is_paid⟩
  · have citizen : false ∈ protectedMembers opening command :=
      List.mem_filter.mpr ⟨original_citizen_keeps_standing [] false, by decide⟩
    exact List.ne_nil_of_mem citizen
  · intro person listed
    have notCommand : person ∉ command := of_decide_eq_true (List.mem_filter.mp listed).2
    have same : person = false := by cases person <;> simp_all [command]
    subst person
    exact ⟨original_citizen_keeps_standing _ false, _, List.mem_cons_self, rfl, _, List.mem_cons_self, by decide⟩
  · rw [the_exit_has_one_original_paid_inventory_position]
    intro item listed
    rw [List.mem_singleton.mp listed]
    refine ⟨original_citizen_keeps_standing _ false, by simp [life, command], rfl, ?_⟩
    intro lot inside _
    unfold RawLaw.actualDebit at inside
    split at inside
    · have same : lot = ((false, true), (1 : ℚ)) := by
        simpa only [RawLaw.debit, life, locate, List.map_cons, List.map_nil, List.mem_singleton] using inside
      rw [same]
      rfl
    · exact (List.not_mem_nil inside).elim
  · apply Clock.Window.a_fully_paid_script_ending_in_time_serves_every_original_window
      _ _ _ the_original_exit_service_is_matched
    change (Root.terminal opening ((intervention ++ calm) ++ exit)).raw.clock ≤ task.deadline
    rw [Execution.a_paid_primitive_trace_keeps_the_actual_clock
      the_peace_exit_is_paid_after_the_citizen_invests.trace, sourceRead]
    decide +kernel

theorem the_actual_refusal_stops_the_old_attack_and_writes_the_exit :
    ∃ result, tryStop opening command task intervention calm exit [conflict] = .stopped result := by
  unfold tryStop
  rw [dif_pos the_investment_is_the_citizens_own_action]
  cases inspectAgenda opening intervention [conflict] with
  | bypass word listed paid =>
      rw [List.mem_singleton.mp listed] at paid
      exact (the_original_attack_cannot_requisition_the_spent_stock paid).elim
  | blocked refusals =>
      obtain ⟨recorded, exactChoice⟩ := inspectExit_selects_every_paid_independent_exit
        the_citizen_keeps_and_spends_her_original_independent_exit
      rw [exactChoice]
      exact ⟨_, rfl⟩

theorem an_actual_alternative_bypasses_when_funded_before_levy :
    (inspectAgenda opening intervention [conflict, routedAttack]).stops = false := by
  cases inspected : (inspectAgenda opening intervention [conflict, routedAttack]).stops with
  | false => rfl
  | true =>
    have blocked := (the_intervention_stops_exactly_when_no_paid_attack_bypasses
      opening intervention [conflict, routedAttack]).mp inspected
    exact (blocked routedAttack (List.mem_cons_of_mem _ List.mem_cons_self)
      a_differently_financed_attack_is_an_actual_bypass).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Consumers
