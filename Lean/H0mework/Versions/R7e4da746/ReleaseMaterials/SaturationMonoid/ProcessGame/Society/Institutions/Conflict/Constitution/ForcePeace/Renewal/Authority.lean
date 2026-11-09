import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal.Lineage
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Mandate.Authority

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

theorem LiveGrant.ordered {items : List Item} {candidate : Party}
    (grant : LiveGrant base scope items candidate) :
    ∃ (proposal acceptance : Item) (first second : Nat), first < second ∧
      items[first]? = some proposal ∧ items[second]? = some acceptance ∧
      PaidCommand base scope proposal (.propose candidate) ∧ PaidCommand base scope acceptance .accept ∧
      acceptance.request.signer = candidate := by
  obtain ⟨lead, proposal, between, acceptance, tail, original, proposed, accepted, signer, _, _⟩ := grant
  refine ⟨proposal, acceptance, lead.length, lead.length + 1 + between.length, by omega,
    ?_, ?_, proposed, accepted, signer⟩
  · rw [original, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  · rw [original, List.getElem?_append_right (by omega : lead.length ≤ _),
      show lead.length + 1 + between.length - lead.length = between.length + 1 by omega]
    rw [List.getElem?_cons_succ, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl

theorem the_actual_successor_holder_has_original_grant (source : C) (history : Script)
    (installed : Emergency.Installed source base scope)
    (released : Civil.Mandate.Released source.raw)
    (authorized : Reparation.Actual.SourceAuthority source history)
    (candidate : Party) (holder : (endAt source history).raw.technology.holder = some candidate) :
    LiveGrant base scope (inventory source history) candidate :=
  (the_actual_inventory_carries_the_mandate_state base scope source history installed authorized)
    |>.grant_after_release base scope released candidate holder

omit [DecidableEq Instrument] in
theorem paid_debit_reads_holder (item : Item)
    (licensed : (law base scope).Valid item.before item.request)
    (debit : (Party × Good) × ℚ)
    (charged : debit ∈ (PublicFunction.physicalLaw (law base scope)).actualDebit item.before item.request)
    (protectedAddress : base.stockPort item.before.technology.technology debit.1.1 debit.1.2 = scope.service) :
    item.before.technology.holder = some item.request.signer ∧
      (Emergency.Ordinary item.request →
        scope.task.earliest ≤ item.before.clock ∧ item.before.clock ≤ scope.task.deadline) := by
  have affected : debit ∈ (law base scope).debit item.before item.request := by
    rw [RawLaw.actualDebit, if_pos (PublicFunction.valid_physical _ _ _ licensed)] at charged
    cases operation : item.request.operation <;>
      simpa only [RawLaw.debit, operation, PublicFunction.physicalLaw] using charged
  cases operation : item.request.operation with
  | revise operator target =>
    refine ⟨?_, fun ordinary => ?_⟩
    · have noConsent : item.request.consents = [] := by
        have policy := licensed.1.2
        cases mark : target.last with
        | none => simp [law, RawLaw.operationAllowed, RawPolicy.eval, operation, mark] at policy
        | some cmd =>
          simp only [law, RawLaw.operationAllowed, RawPolicy.eval, operation, mark, decide_eq_true_eq] at policy
          exact policy.2.1
      have required : scope.service ∈ (law base scope).requiredPorts item.before item.request :=
        List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨debit, affected, protectedAddress⟩))
      rcases licensed.2.1 scope.service required with allowed | consent
      · simpa [law, scope.separate] using allowed
      · simp [noConsent] at consent
    · simp [Emergency.Ordinary, operation] at ordinary
  | _ =>
    have ordinary : Emergency.Ordinary item.request := by simp only [Emergency.Ordinary, operation]
    have chargedBase : debit ∈ base.debit (eraseCurrent item.before) (eraseRequest item.request) := by
      simpa only [RawLaw.debit, operation, eraseRequest, eraseOperation, eraseCurrent, law] using affected
    have exactUse := Emergency.every_protected_operation_reads_the_original_clock base scope
      item.before item.request ordinary licensed
      (Emergency.protected_debit_reads_the_mandate base scope item.before item.request debit chargedBase protectedAddress)
    exact ⟨exactUse.1, fun _ => exactUse.2⟩

/-- Every actual debit of an original protected address has the two prior
signatures, even when the debit is hidden inside another operation or submitted
at the same clock. Operational use must also fit the original time window. -/
theorem the_actual_protected_debit_has_original_grant (source : C) (history : Script)
    (installed : Emergency.Installed source base scope)
    (released : Civil.Mandate.Released source.raw)
    (authorized : Reparation.Actual.SourceAuthority source history)
    (front : List Item) (item : Item) (back : List Item)
    (position : inventory source history = front ++ item :: back)
    (debit : (Party × Good) × ℚ)
    (charged : debit ∈ (PublicFunction.physicalLaw source.native.input.law).actualDebit item.before item.request)
    (protectedAddress : base.stockPort source.raw.technology.technology debit.1.1 debit.1.2 = scope.service) :
    LiveGrant base scope front item.request.signer ∧
      (Emergency.Ordinary item.request →
        scope.task.earliest ≤ item.before.clock ∧ item.before.clock ≤ scope.task.deadline) := by
  have trace := the_actual_inventory_carries_the_mandate_state base scope source history installed authorized
  rw [position] at trace
  obtain ⟨before, licensed⟩ := MaterialTrace.at_item base scope front item back trace
  have fixedAddress : base.stockPort item.before.technology.technology debit.1.1 debit.1.2 = scope.service := by
    rwa [before.same_technology base scope]
  have lawExact : source.native.input.law = law base scope := installed
  rw [lawExact] at charged
  obtain ⟨holder, deadline⟩ := paid_debit_reads_holder item licensed debit charged fixedAddress
  exact ⟨before.grant_after_release base scope released _ holder, deadline⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal
