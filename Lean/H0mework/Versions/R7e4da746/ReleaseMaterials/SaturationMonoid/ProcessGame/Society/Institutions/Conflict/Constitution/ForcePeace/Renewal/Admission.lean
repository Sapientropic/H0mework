import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal.Participation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Quantities.Execution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument]

local notation "M" => State Party Technology
local notation "Req" => Request Party Good Port M Instrument
local notation "Item" => ExecutionItem Party Good Port M Instrument
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port M Instrument
local notation "Script" => Reparation.Actual.Script Party Good Port M Instrument

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
/-- Only the original candidate nomination acquires the additional check. -/
def IndependentNomination (request : Req) : Prop :=
  match request.operation with
  | .revise _ target => match target.last with
    | some (.propose candidate) => request.signer ≠ candidate
    | _ => True
  | _ => True

instance (request : Req) : Decidable (IndependentNomination request) := by
  unfold IndependentNomination
  split <;> try infer_instance
  split <;> infer_instance

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem not_independent_is_an_original_self_nomination (request : Req)
    (denied : ¬ IndependentNomination request) :
    ∃ (operator : Party) (target : M), request.operation = .revise operator target ∧
      target.last = some (.propose request.signer) := by
  cases operation : request.operation with
  | revise operator target =>
    cases marked : target.last with
    | none => simp [IndependentNomination, operation, marked] at denied
    | some command =>
      cases command with
      | propose candidate =>
        have same : request.signer = candidate := by
          simpa only [IndependentNomination, operation, marked, not_not] using denied
        exact ⟨operator, target, rfl, same.symm ▸ marked⟩
      | _ => simp [IndependentNomination, operation, marked] at denied
  | _ => simp [IndependentNomination, operation] at denied

def AdmittedHistory (cut : C) (history : Script) : Prop :=
  ∀ item ∈ inventory cut history,
    cut.native.input.law.Valid item.before item.request ∧ IndependentNomination item.request

theorem AdmittedHistory.original_authority {cut : C} {history : Script}
    (checked : AdmittedHistory cut history) : Reparation.Actual.SourceAuthority cut history :=
  fun item listed => (checked item listed).1

theorem AdmittedHistory.append {cut : C} {past suffix : Script}
    (pastChecked : AdmittedHistory cut past) (suffixChecked : AdmittedHistory (endAt cut past) suffix) :
    AdmittedHistory cut (past ++ suffix) := by
  intro item listed
  rw [inventory_append] at listed
  rcases List.mem_append.mp listed with first | later
  · exact pastChecked item first
  · have checked := suffixChecked item later
    rwa [endAt_input] at checked

theorem AdmittedHistory.restrict {cut : C} {past suffix : Script}
    (checked : AdmittedHistory cut (past ++ suffix)) :
    AdmittedHistory cut past ∧ AdmittedHistory (endAt cut past) suffix := by
  constructor <;> intro item listed
  · apply checked
    rw [inventory_append]
    exact List.mem_append_left _ listed
  · have accepted := checked item (by rw [inventory_append]; exact List.mem_append_right _ listed)
    change (endAt cut past).native.input.law.Valid item.before item.request ∧ _
    rwa [endAt_input]

inductive Violation (cut : C) (input : Input)
  | authority (item : Item) (listed : item ∈ inventory cut [input])
      (invalid : ¬ cut.native.input.law.Valid item.before item.request)
  | selfNomination (item : Item) (listed : item ∈ inventory cut [input])
      (licensed : cut.native.input.law.Valid item.before item.request) (denied : ¬ IndependentNomination item.request)

theorem Violation.refutes {cut : C} {input : Input} (issue : Violation cut input) :
    ¬ AdmittedHistory cut [input] := by
  intro checked
  cases issue with
  | authority item listed denied => exact denied (checked item listed).1
  | selfNomination item listed _ denied => exact denied (checked item listed).2

inductive Admission (cut : C) (input : Input)
  | approved (checked : AdmittedHistory cut [input])
  | refused (issue : Violation cut input)

def inspectAdmission (cut : C) (input : Input) : Admission cut input :=
  match Capitalism.Universal.Abolition.Material.inspectList
    (fun item : Item => cut.native.input.law.Valid item.before item.request ∧ IndependentNomination item.request)
    (inventory cut [input]) with
  | .clear all => .approved all
  | .failure item listed failed =>
    if licensed : cut.native.input.law.Valid item.before item.request then
      .refused (.selfNomination item listed licensed (fun independent => failed ⟨licensed, independent⟩))
    else .refused (.authority item listed licensed)

variable [DecidableEq Technology] {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}

omit [DecidableEq Instrument] in
theorem PaidCommand.distinct_proposer {item : Item} {candidate : Party}
    (paid : PaidCommand base scope item (.propose candidate)) (independent : IndependentNomination item.request) :
    item.request.signer ≠ candidate := by
  rw [paid.request_eq] at independent
  simpa [IndependentNomination, request, advance_last] using independent

theorem LiveGrant.two_distinct_original_signers {items : List Item} {candidate : Party}
    (grant : LiveGrant base scope items candidate)
    (checked : ∀ item ∈ items, IndependentNomination item.request) :
    ∃ (proposal acceptance : Item) (first second : Nat),
      first < second ∧ items[first]? = some proposal ∧ items[second]? = some acceptance ∧
      PaidCommand base scope proposal (.propose candidate) ∧ PaidCommand base scope acceptance .accept ∧
      proposal.request.signer ∈ PublicFunction.Delegation.members scope.task ∧
      acceptance.request.signer = candidate ∧ proposal.request.signer ≠ acceptance.request.signer := by
  obtain ⟨proposal, acceptance, first, second, order, originalProposal, originalAcceptance,
    proposed, accepted, signer⟩ := grant.ordered
  have distinct := proposed.distinct_proposer (checked proposal (List.mem_of_getElem? originalProposal))
  exact ⟨proposal, acceptance, first, second, order, originalProposal, originalAcceptance,
    proposed, accepted, proposed.canRun.1, signer, fun same => distinct (same.trans signer)⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal
