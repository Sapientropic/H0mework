import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Original
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Refusal

set_option autoImplicit false
set_option maxRecDepth 8192

open private keysAt original_key from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Actual.Incidence

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Original.Replay

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Root.Registered.Macro
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Conflict.Consumers.Evolving (C compact levy)
open ExposureGuard (stop)
open Reparation.Consumers (address)
open Reparation.Actual Reparation.Actual.Allocation
open Quantities.Execution (endAt endAt_append next query submitted_is_original)

noncomputable section

private theorem valid_at (source : C) (law : source.native.input = compact)
    (raw : source.raw = snapshot 111 113) :
    (Physical.Public.interpreter source.native.input).Valid source.raw levy := by
  rw [law, raw]
  decide +kernel

theorem old_authority : cut.native.input.law.Valid cut.raw levy := by
  rw [same_source, cut_raw]
  decide +kernel

private theorem items_at (source : C) (law : source.native.input = compact)
    (raw : source.raw = snapshot 111 113) (quiet : Ready source) (available : ReviewAvailable source) :
    Boundary.Actual.items source attack = [⟨0, source.raw, levy⟩] :=
  (Quantities.Execution.the_selected_primitive_is_paid_by_the_original_root (queued source levy) levy quiet
    (the_available_review_forwards_the_actual_requested_primitive source levy available)
    rfl (valid_at source law raw)).2.2

private theorem loss_at (source : C) (law : source.native.input = compact)
    (raw : source.raw = snapshot 111 113) :
    Reparation.loss (Boundary.Actual.materialLaw source) community ⟨0, source.raw, levy⟩ address = 6 := by
  unfold Boundary.Actual.materialLaw
  rw [law, raw]
  decide +kernel

private def indexAt (source : C) (items : Boundary.Actual.items source attack = [⟨0, source.raw, levy⟩]) :
    Fin (Boundary.Actual.items source attack).length :=
  ⟨0, by rw [items]; exact Nat.zero_lt_one⟩

private theorem item_at (source : C) (items : Boundary.Actual.items source attack = [⟨0, source.raw, levy⟩])
    (position : Fin (Boundary.Actual.items source attack).length) :
    (Boundary.Actual.items source attack)[position] = ⟨0, source.raw, levy⟩ := by
  exact List.mem_singleton.mp ((congrArg (fun rows => (Boundary.Actual.items source attack)[position] ∈ rows)
    items).mp (List.getElem_mem _))

private def damageAt (source : C) (items : Boundary.Actual.items source attack = [⟨0, source.raw, levy⟩])
    (six : Reparation.loss (Boundary.Actual.materialLaw source) community ⟨0, source.raw, levy⟩ address = 6) :
    Boundary.Actual.DamageAt source attack community :=
  ⟨(indexAt source items, address), by
    change 0 < Reparation.loss (Boundary.Actual.materialLaw source) community
      (Boundary.Actual.items source attack)[indexAt source items] address
    rw [item_at source items, six]
    norm_num⟩

private theorem damage_at_six (source : C) (items : Boundary.Actual.items source attack = [⟨0, source.raw, levy⟩])
    (six : Reparation.loss (Boundary.Actual.materialLaw source) community ⟨0, source.raw, levy⟩ address = 6) :
    (damageAt source items six).quantity = 6 := by
  change Reparation.loss (Boundary.Actual.materialLaw source) community
    (Boundary.Actual.items source attack)[indexAt source items] address = 6
  rw [item_at source items, six]

theorem replayed_items : Boundary.Actual.items cut attack = [⟨0, cut.raw, levy⟩] :=
  items_at cut same_source cut_raw ready review

def candidate : Boundary.Actual.DamageAt cut attack community :=
  damageAt cut replayed_items (loss_at cut same_source cut_raw)

theorem candidate_six : candidate.quantity = 6 :=
  damage_at_six cut replayed_items (loss_at cut same_source cut_raw)

def replayed_occurrence : Occurrence seed community := ⟨history, attack, candidate⟩

def replayed_balance : Balance := opening replayed_occurrence

theorem replayed_balance_six : replayed_balance.remaining = 6 := candidate_six

theorem replayed_address : replayed_occurrence.address = (4, 0, (false, true, false)) := rfl

theorem replayed_occurrence_is_distinct : replayed_occurrence ≠ occurrence := by
  intro same
  have atAddress := congrArg Occurrence.address same
  rw [replayed_address, exact_address] at atAddress
  cases atAddress

private theorem replayed_damages :
    Boundary.Actual.damages cut attack community = [candidate] := by
  have width : (Boundary.Actual.items cut attack).length = 1 := congrArg List.length replayed_items
  have unique (loss : Boundary.Actual.DamageAt cut attack community) : loss = candidate := by
    have item : loss.item = ⟨0, cut.raw, levy⟩ := item_at cut replayed_items loss.position
    have valid := loss.actual_foreign_debit.2.1
    have key := original_key loss
    rw [item] at key valid
    unfold keysAt at key
    rw [RawLaw.actualDebit, if_pos valid] at key
    change loss.key ∈ [address] at key
    have first : loss.position.val < 1 := loss.position.isLt.trans_eq width
    have second : candidate.position.val < 1 := candidate.position.isLt.trans_eq width
    have same : loss.position = candidate.position := Fin.ext (by omega)
    exact Subtype.ext (Prod.ext same (List.mem_singleton.mp key))
  have listed := Boundary.Actual.every_actual_debit_is_assessed candidate
  have distinct := Boundary.Actual.each_damage_address_occurs_once cut attack community
  cases exactLosses : Boundary.Actual.damages cut attack community with
  | nil => exact (List.not_mem_nil (exactLosses ▸ listed)).elim
  | cons first rest =>
    have empty : rest = [] := List.eq_nil_iff_forall_not_mem.mpr (fun loss found =>
      (List.nodup_cons.mp (exactLosses ▸ distinct)).1 ((unique loss).trans (unique first).symm ▸ found))
    rw [unique first, empty]

def replayHistory : Word := history ++ [attack, none]

def replayState : State seed community replayHistory := run seed community replayHistory

theorem replayed_raw : (endAt seed replayHistory).raw = snapshot 105 119 := by
  unfold replayHistory
  rw [endAt_append]
  change (afterNative cut levy).raw = _
  rw [(two_actual_root_steps_pay_and_consume_the_generated_primitive cut levy ready review
    rfl (valid_at cut same_source cut_raw)).2, same_source, cut_raw]
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;> decide +kernel
  · funext instrument debtor creditor
    cases instrument
    cases debtor <;> cases creditor <;> decide +kernel
  · exact Subsingleton.elim _ _
  · decide +kernel
  · decide +kernel

theorem replay_accounting_has_no_second_item : Boundary.Actual.items (next cut attack) none = [] :=
  Reparation.Transport.native_step_has_no_material_items none
    (the_actual_body_must_consume_its_original_native_head cut levy ready review rfl (valid_at cut same_source cut_raw))

theorem replayed_authority : SourceAuthority cut [attack, none] := by
  intro item listed
  change item ∈ Quantities.Execution.inventory cut ([attack] ++ [none]) at listed
  rw [Quantities.Execution.inventory_append] at listed
  change item ∈ Boundary.Actual.items cut attack ++ Boundary.Actual.items (next cut attack) none at listed
  rw [replayed_items, replay_accounting_has_no_second_item, List.append_nil] at listed
  rcases List.mem_singleton.mp listed with rfl
  exact old_authority

theorem replayed_balances :
    replayState.stack.balances = [(occurrence, balance), (replayed_occurrence, replayed_balance)] := by
  let past := history ++ [attack]
  let rows := [(occurrence, balance), (replayed_occurrence, replayed_balance)]
  have opened : openings seed community history attack = [replayed_occurrence] := by
    unfold openings
    rw [replayed_damages]
    rfl
  have signed : (atInput history attack rows).result = rows := by
    have width : (Boundary.Actual.items cut attack).length = 1 := congrArg List.length replayed_items
    obtain ⟨site, single⟩ := List.length_eq_one_iff.mp (List.length_finRange.trans width)
    have positions : itemPositions (seed := seed) history attack = [site] := single
    unfold atInput
    rw [positions]
    let plan := atItem seed history attack site rows
    change plan.changes.result = rows
    have same := Changes.kept_without_the_original_victim_signatures history attack site
      plan.changes plan.original (by
        intro row original
        change (Boundary.Actual.items cut attack)[site].request.signer ≠ row.1.key.1
        rw [item_at cut replayed_items]
        rcases List.mem_cons.mp original with rfl | last
        · decide
        · rcases List.mem_singleton.mp last with rfl
          decide)
    rw [same, Changes.unchanged_result]
  have born : (run seed community past).stack.balances = rows := by
    unfold past
    rw [run_snoc, written_balances, show (run seed community history).stack.balances = _ from balances_exact, opened]
    exact signed
  have noItems : Boundary.Actual.items (endAt seed past) none = [] := by
    unfold past
    rw [endAt_append]
    exact replay_accounting_has_no_second_item
  have noOpening : openings seed community past none = [] := by
    unfold openings
    rw [Boundary.Actual.no_material_write_has_no_damage _ _ _ noItems]
    rfl
  have full : replayHistory = past ++ [none] := by simp [replayHistory, past, List.append_assoc]
  unfold replayState
  rw [full, run_snoc, written_balances, noOpening, List.map_nil, List.append_nil]
  exact (no_original_items_keeps_rows past none _ noItems).1.trans born

abbrev stopCut : C := endAt cut [stop]

private abbrev stopQuery := query cut stop

private theorem stop_query_ready :
    ¬ Public.Inquiry.HasWork stopQuery.native.frame stopQuery.native.actual.actual := ready

private theorem stop_routed : stopQuery.executionRaw = .stopReview := by
  unfold Evolving.Epoch.Current.executionRaw Evolving.Epoch.Current.choice
  rw [show stopQuery.control = cut.control from (cut.requery_keeps_control_and_complete_account _).1,
    show stopQuery.proposal = .stopReview from submitted_is_original cut .stopReview]
  unfold Evolving.Epoch.select
  split
  · rfl
  · rename_i cursor active
    have available : cursor.recourse = true := by simpa only [ReviewAvailable, active] using review
    rw [if_pos available]
    rfl

private theorem stop_cut_transition :
    stopCut = Evolving.Epoch.Transition.next stopQuery stop_query_ready :=
  stopQuery.advance_eq_epoch stop_query_ready

theorem stop_raw : stopCut.raw = cut.raw := by
  rw [stop_cut_transition, Evolving.Epoch.Transition.next_state_reads_the_same_actual_material_target]
  unfold Evolving.Epoch.Current.physicalResult
  rw [stop_routed]
  rfl

theorem stop_clock : stopCut.raw.clock = cut.raw.clock := congrArg RawCurrent.clock stop_raw

theorem stop_review : ReviewAvailable stopCut := by
  have sameControl : stopCut.control = cut.control := by
    rw [stop_cut_transition, Evolving.Epoch.Transition.next_reads_the_written_control]
    unfold Evolving.Epoch.Current.afterControl Evolving.Epoch.Current.choice
    rw [show stopQuery.control = cut.control from (cut.requery_keeps_control_and_complete_account _).1,
      show stopQuery.proposal = .stopReview from submitted_is_original cut .stopReview]
    unfold Evolving.Epoch.select
    split
    · rfl
    · rename_i cursor active
      have available : cursor.recourse = true := by simpa only [ReviewAvailable, active] using review
      rw [if_pos available]
      rfl
  unfold ReviewAvailable
  rw [sameControl]
  exact review

theorem stop_ready : Ready stopCut := by
  rw [stop_cut_transition]
  let n := (Evolving.Epoch.Transition.next stopQuery stop_query_ready).native
  have emptyMaterial : stopQuery.physicalResult.execution.items = [] := by
    unfold Evolving.Epoch.Current.physicalResult
    rw [stop_routed]
    rfl
  have items := Public.Accounting.actual_items_are_the_same_public_execution n.input n.depth n.count
    n.prefixLimit n.renewalLimit n.oldPast n.start
  have empty : Public.Accounting.items n.input n.depth n.count n.prefixLimit n.renewalLimit n.oldPast n.start = [] :=
    List.map_eq_nil_iff.mp (items.trans emptyMaterial)
  change ¬ (n.actual.actual.bodyPaid = false ∨
    (Public.Accounting.item? n.input n.depth n.count n.prefixLimit n.renewalLimit n.oldPast n.start n.actual.actual).isSome = true)
  simp only [Public.Accounting.item?, n.bodyPaid, if_true, empty, List.getElem?_nil, Option.isSome_none,
    Bool.true_eq_false, Bool.false_eq_true, or_self, not_false_eq_true]

theorem stop_source : stopCut.native.input = compact :=
  (Quantities.Execution.next_input cut stop).trans same_source

def candidate_after_stop : Boundary.Actual.DamageAt stopCut attack community :=
  damageAt stopCut (items_at stopCut stop_source (stop_raw.trans cut_raw) stop_ready stop_review)
    (loss_at stopCut stop_source (stop_raw.trans cut_raw))

theorem candidate_after_stop_six : candidate_after_stop.quantity = 6 :=
  damage_at_six stopCut _ _

theorem stop_cut_is_the_original_extended_history : endAt seed (history ++ [stop]) = stopCut :=
  endAt_append seed history [stop]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Original.Replay
