import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Mandate.Authority
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Restitution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Mandate

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Conflict.Root (Cut)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "C" => Cut Party Good Port (State Party Technology) Instrument
local notation "Req" => Request Party Good Port (State Party Technology) Instrument
local notation "Word" => RawEvent Party Good Port (State Party Technology) Instrument
local notation "Base" => RawLaw Party Good Port Technology Instrument
local notation "J" => Scope (Party := Party) (Good := Good) (Port := Port)
local notation "script" => Quantities.Execution.primitiveScript

/-- The first intervention is the original member's revocation request.
The rest of the paid word may include life, maintenance and independent exit. -/
theorem the_paid_civilian_revoke_removes_holder_and_offer
    (source : C) (base : Base) (scope : J) (actor : Party) (tail : Word)
    (installed : source.native.input.law = law base scope)
    (paid : Conflict.Root.Paid source (request scope source.raw actor .revoke :: tail)) :
    let command := request scope source.raw actor .revoke
    Released (Conflict.Root.terminal source [command]).raw ∧
      actor ∈ PublicFunction.Delegation.members scope.task ∧
      Quantities.Recorded source (script [command]) ∧
      Evolving.Epoch.Current.ClosedAt (Conflict.Root.terminal source [command]) := by
  let command := request scope source.raw actor .revoke
  have original := paid.authorized ⟨0, source.raw, command⟩ List.mem_cons_self
  rw [installed] at original
  have member := ((command_policy base scope source.raw actor .revoke).mp original.1.2).1
  have trace := Conflict.Root.trace_before_prefix source _ [command] tail paid.trace
  have raw := trace.raw_is_the_original_instruction_fold
  change (Conflict.Root.terminal source [command]).raw =
    (PublicFunction.physicalLaw source.native.input.law).step source.raw command at raw
  rw [installed] at raw
  have step : (PublicFunction.physicalLaw (law base scope)).step source.raw command =
      (law base scope).step source.raw command := by
    rw [RawLaw.step, RawLaw.step, if_pos (PublicFunction.valid_physical _ _ _ original), if_pos original]
    rfl
  have release := (paid_command_effect base scope source.raw actor .revoke original).1
  have written := Quantities.record source (script [command])
  refine ⟨?_, member, written, written.next⟩
  change Released (Conflict.Root.terminal source [command]).raw
  rw [raw, step]
  exact ⟨congrArg State.holder release, congrArg State.offered release⟩

private theorem original_checks (source : C) (base : Base) (scope : J) (word : Word)
    (installed : source.native.input.law = law base scope)
    (paid : Conflict.Root.Paid source word) :
    ∀ item ∈ (law base scope).rawItems source.raw word, (law base scope).Valid item.before item.request := by
  have valid := paid.authorized
  unfold Conflict.Root.Authorized at valid
  change ∀ item ∈ (PublicFunction.physicalLaw source.native.input.law).rawItems source.raw word,
    source.native.input.law.Valid item.before item.request at valid
  rw [installed] at valid
  intro item present
  have same := PublicFunction.execute_physical_of_authorized (law base scope) source.raw 0 word
    (fun item inside => PublicFunction.valid_physical _ _ _ (valid item inside)) valid
  unfold RawLaw.rawItems at present
  rw [same] at present
  exact valid item present

theorem no_paid_protected_operation_before_a_fresh_nomination
    (source : C) (base : Base) (scope : J) (front tail : Word) (action : Req)
    (installed : source.native.input.law = law base scope)
    (released : Released source.raw)
    (noOffer : ∀ request ∈ front, DoesNotPropose request)
    (controlled : NeedsAuthority base scope ((law base scope).execute source.raw 0 front).final action) :
    ¬ Conflict.Root.Paid source (front ++ action :: tail) := by
  intro paid
  let cut := ((law base scope).execute source.raw 0 front).final
  let original : ExecutionItem Party Good Port (State Party Technology) Instrument :=
    ⟨0 + front.length, cut, action⟩
  have inside : original ∈ (law base scope).rawItems source.raw (front ++ action :: tail) := by
    unfold RawLaw.rawItems
    rw [(law base scope).execute_append]
    exact List.mem_append_right _ List.mem_cons_self
  have closed := a_finite_word_without_new_nomination_keeps_release base scope source.raw 0 front released noOffer
  exact a_released_mandate_refuses_every_protected_operation base scope cut action closed controlled
    (original_checks source base scope _ installed paid original inside)

/-- After release, an executable controlled operation requires an earlier
original paid proposal by a task member. Its actor and item are recovered. -/
theorem a_protected_operation_after_release_needs_an_original_paid_civilian_proposal
    (source : C) (base : Base) (scope : J) (front tail : Word) (action : Req)
    (installed : source.native.input.law = law base scope) (released : Released source.raw)
    (controlled : NeedsAuthority base scope ((law base scope).execute source.raw 0 front).final action)
    (paid : Conflict.Root.Paid source (front ++ action :: tail)) :
    ∃ item ∈ (law base scope).rawItems source.raw front, ∃ candidate target,
      item.request.operation = .revise item.request.signer target ∧ target.last = some (.propose candidate) ∧
      item.request.signer ∈ PublicFunction.Delegation.members scope.task ∧
      (law base scope).Valid item.before item.request := by
  classical
  have excluded : ¬ ∀ request ∈ front, DoesNotPropose request := fun noOffer =>
    no_paid_protected_operation_before_a_fresh_nomination source base scope front tail action
      installed released noOffer controlled paid
  push Not at excluded
  obtain ⟨request, member, marked⟩ := excluded
  have origin : request ∈ ((law base scope).rawItems source.raw front).map ExecutionItem.request := by
    unfold RawLaw.rawItems
    rw [(law base scope).inventory_requests_exact source.raw 0 front]
    exact member
  obtain ⟨item, inside, same⟩ := List.mem_map.mp origin
  subst request
  have combined : item ∈ (law base scope).rawItems source.raw (front ++ action :: tail) := by
    unfold RawLaw.rawItems
    rw [(law base scope).execute_append]
    exact List.mem_append_left _ inside
  have actual := original_checks source base scope _ installed paid item combined
  have policy := actual.1.2
  cases operation : item.request.operation <;> simp [DoesNotPropose, operation] at marked
  case revise operator target =>
    obtain ⟨candidate, label⟩ := marked
    simp only [law, RawLaw.operationAllowed, RawPolicy.eval, operation, label, decide_eq_true_eq] at policy
    have signer := congrArg (fun actor => (Operation.revise actor target :
      Operation Party Good (State Party Technology) Instrument)) policy.1
    exact ⟨item, inside, candidate, target, operation.trans signer, label, policy.2.2.2.2.2.1, actual⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Mandate
