import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal.Authority
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Defence

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal

open Capitalism.Universal.Source.Program
open PublicFunction.Mandate

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument] [DecidableEq Community]

local notation "Item" => ExecutionItem Party Good Port (State Party Technology) Instrument

variable {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {items : List (ExecutionItem Party Good Port (State Party Technology) Instrument)} {candidate : Party}

omit [DecidableEq Community] in
theorem LiveGrant.two_original_payments (grant : LiveGrant base scope items candidate) :
    ∃ (proposal acceptance : Item) (first second : Nat),
      first < second ∧ second < items.length ∧
      items[first]? = some proposal ∧ items[second]? = some acceptance ∧
      proposal.request.signer ∈ PublicFunction.Delegation.members scope.task ∧
      acceptance.request.signer = candidate ∧
      (PublicFunction.physicalLaw (law base scope)).actualDebit proposal.before proposal.request =
        locate proposal.request.signer scope.revisionCost ∧
      (PublicFunction.physicalLaw (law base scope)).actualDebit acceptance.before acceptance.request =
        locate candidate scope.revisionCost := by
  obtain ⟨proposal, acceptance, first, second, ordered, originalProposal, originalAcceptance,
    proposed, accepted, signer⟩ := grant.ordered
  have secondInside : second < items.length := (List.getElem?_eq_some_iff.mp originalAcceptance).choose
  exact ⟨proposal, acceptance, first, second, ordered, secondInside, originalProposal,
    originalAcceptance, proposed.canRun.1, signer, proposed.fee, signer ▸ accepted.fee⟩

omit [DecidableEq Community] in
theorem LiveGrant.external_candidate_cannot_self_authorize (grant : LiveGrant base scope items candidate)
    (external : candidate ∉ PublicFunction.Delegation.members scope.task) :
    ∃ (proposal : Item) (index : Nat), items[index]? = some proposal ∧
      PaidCommand base scope proposal (.propose candidate) ∧
      proposal.request.signer ∈ PublicFunction.Delegation.members scope.task ∧
      proposal.request.signer ≠ candidate := by
  obtain ⟨proposal, _, first, _, _, original, _, proposed, _, _⟩ := grant.ordered
  have standing := proposed.canRun.1
  exact ⟨proposal, first, original, proposed, standing, fun same => external (same ▸ standing)⟩

omit [DecidableEq Community] in
theorem LiveGrant.no_grant_from_one_external_signer (grant : LiveGrant base scope items candidate)
    (external : candidate ∉ PublicFunction.Delegation.members scope.task) :
    ¬ ∀ item ∈ items, item.request.signer = candidate := by
  obtain ⟨proposal, index, original, _, _, different⟩ := grant.external_candidate_cannot_self_authorize external
  exact fun all => different (all proposal (List.mem_of_getElem? original))

variable {source : Root.Cut Party Good Port (State Party Technology) Instrument}
  {attackWord : RawEvent Party Good Port (State Party Technology) Instrument}
  {community : Party → Community}

/-- With the task drawn from the exposed community, the actor at the
original foreign crossing cannot sign a restoration on its own. -/
theorem LiveGrant.crossing_needs_an_exposed_community_signer
    (attack : Boundary.AggressionAt source attackWord community)
    (taskStanding : ∀ person ∈ PublicFunction.Delegation.members scope.task, person ∈ attack.residents)
    (grant : LiveGrant base scope items attack.attacker) :
    ∃ (proposal : Item) (index : Nat), items[index]? = some proposal ∧
      PaidCommand base scope proposal (.propose attack.attacker) ∧
      proposal.request.signer ∈ attack.residents ∧ proposal.request.signer ≠ attack.attacker := by
  have external : attack.attacker ∉ PublicFunction.Delegation.members scope.task := by
    intro bears
    exact attack.foreign (decide_eq_true_eq.mp (List.mem_filter.mp (taskStanding _ bears)).2)
  obtain ⟨proposal, index, original, proposed, localMember, different⟩ :=
    grant.external_candidate_cannot_self_authorize external
  exact ⟨proposal, index, original, proposed, taskStanding _ localMember, different⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal
