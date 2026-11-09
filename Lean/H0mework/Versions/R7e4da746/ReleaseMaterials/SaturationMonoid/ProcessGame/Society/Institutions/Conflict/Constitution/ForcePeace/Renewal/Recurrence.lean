import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal.Authority

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Quantities.Execution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "M" => State Party Technology
local notation "Item" => ExecutionItem Party Good Port M Instrument
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Script" => Reparation.Actual.Script Party Good Port M Instrument

variable {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}

private theorem MaterialTrace.cut_after_item {start final : M} (before : List Item) (item : Item)
    (later : List Item) (trace : MaterialTrace base scope start (before ++ item :: later) final) :
    let after := ((law base scope).step item.before item.request).technology
    MaterialTrace base scope start (before ++ [item]) after ∧ MaterialTrace base scope after later final := by
  obtain ⟨middle, initial, remainder⟩ := MaterialTrace.cut base scope before (item :: later) trace
  cases remainder with
  | cons exactState licensed rest =>
    exact ⟨initial.append base scope (.cons exactState licensed (.nil _)), rest⟩

private theorem MaterialTrace.retains_holder {start final : M} {items : List Item} {candidate : Party}
    (trace : MaterialTrace base scope start items final) (initial : start.holder = some candidate)
    (each : ∀ item ∈ items, Keeps base scope State.holder candidate item) :
    final.holder = some candidate := by
  induction trace with
  | nil => exact initial
  | cons _ _ _ later =>
    exact later (each _ List.mem_cons_self).2 (fun item listed => each item (List.mem_cons_of_mem _ listed))

theorem MaterialTrace.holder_of_liveGrant {start final : M} {items : List Item} {candidate : Party}
    (trace : MaterialTrace base scope start items final) (grant : LiveGrant base scope items candidate) :
    final.holder = some candidate := by
  obtain ⟨lead, proposal, between, acceptance, tail, position, _, accepted, signer, _, each⟩ := grant
  have split : items = (lead ++ proposal :: between) ++ acceptance :: tail := by
    simp only [position, List.append_assoc, List.cons_append]
  rw [split] at trace
  have afterAcceptance := (MaterialTrace.cut_after_item _ acceptance tail trace).2
  have holder : ((law base scope).step acceptance.before acceptance.request).technology.holder = some candidate := by
    rw [accepted.after]
    exact accepted.canRun.1.trans (congrArg some signer)
  exact afterAcceptance.retains_holder holder each

theorem the_actual_holder_is_equivalent_to_a_live_paid_grant_after_release
    (source : C) (history : Script) (installed : Emergency.Installed source base scope)
    (released : Civil.Mandate.Released source.raw) (authorized : Reparation.Actual.SourceAuthority source history)
    (candidate : Party) :
    (endAt source history).raw.technology.holder = some candidate ↔
      LiveGrant base scope (inventory source history) candidate := by
  have trace := the_actual_inventory_carries_the_mandate_state base scope source history installed authorized
  exact ⟨trace.grant_after_release base scope released candidate, trace.holder_of_liveGrant⟩

theorem the_actual_protected_operation_has_an_earlier_live_grant
    (source : C) (history : Script) (installed : Emergency.Installed source base scope)
    (released : Civil.Mandate.Released source.raw) (authorized : Reparation.Actual.SourceAuthority source history)
    (front : List Item) (item : Item) (back : List Item)
    (position : inventory source history = front ++ item :: back)
    (ordinary : Emergency.Ordinary item.request)
    (usesMandate : Emergency.UsesMandate base scope item.before item.request) :
    LiveGrant base scope front item.request.signer ∧
      scope.task.earliest ≤ item.before.clock ∧ item.before.clock ≤ scope.task.deadline := by
  have trace := the_actual_inventory_carries_the_mandate_state base scope source history installed authorized
  rw [position] at trace
  obtain ⟨before, licensed⟩ := MaterialTrace.at_item base scope front item back trace
  obtain ⟨holder, deadline⟩ := Emergency.every_protected_operation_reads_the_original_clock base scope
    item.before item.request ordinary licensed usesMandate
  exact ⟨before.grant_after_release base scope released _ holder, deadline⟩

/-- A release at any original item, including within a multi-item submission,
cuts off every earlier proposal and acceptance. The new signatures must both
occur in the suffix of that item. -/
theorem every_original_release_requires_fresh_signatures_in_its_own_suffix
    (source : C) (history : Script) (installed : Emergency.Installed source base scope)
    (authorized : Reparation.Actual.SourceAuthority source history)
    (before : List Item) (release : Item) (remaining : List Item)
    (position : inventory source history = before ++ release :: remaining)
    (released : Civil.Mandate.Released ((law base scope).step release.before release.request)) :
    (∀ candidate, (endAt source history).raw.technology.holder = some candidate →
      LiveGrant base scope remaining candidate) ∧
    ∀ (front : List Item) (item : Item) (back : List Item), remaining = front ++ item :: back →
      ∀ debit : (Party × Good) × ℚ,
        debit ∈ (PublicFunction.physicalLaw source.native.input.law).actualDebit item.before item.request →
        base.stockPort source.raw.technology.technology debit.1.1 debit.1.2 = scope.service →
        LiveGrant base scope front item.request.signer ∧
          (Emergency.Ordinary item.request →
            scope.task.earliest ≤ item.before.clock ∧ item.before.clock ≤ scope.task.deadline) := by
  have trace := the_actual_inventory_carries_the_mandate_state base scope source history installed authorized
  rw [position] at trace
  obtain ⟨initial, remainder⟩ := MaterialTrace.cut_after_item before release remaining trace
  refine ⟨fun candidate holds => remainder.grant_after_release base scope released candidate holds, ?_⟩
  intro front item back itemPosition debit charged protectedAddress
  rw [itemPosition] at remainder
  obtain ⟨beforeItem, licensed⟩ := MaterialTrace.at_item base scope front item back remainder
  have tech := (beforeItem.same_technology base scope).trans (initial.same_technology base scope)
  have fixedAddress : base.stockPort item.before.technology.technology debit.1.1 debit.1.2 = scope.service := by
    rwa [tech]
  have lawExact : source.native.input.law = law base scope := installed
  rw [lawExact] at charged
  obtain ⟨holder, deadline⟩ := paid_debit_reads_holder item licensed debit charged fixedAddress
  exact ⟨beforeItem.grant_after_release base scope released _ holder, deadline⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal
