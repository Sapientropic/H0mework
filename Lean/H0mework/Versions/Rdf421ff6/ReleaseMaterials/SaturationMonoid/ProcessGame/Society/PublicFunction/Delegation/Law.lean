import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Planning
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority.LawExtension

/-! A task-scoped revocable delegation. The original task beneficiaries
generate the challenge constituency. Its port is separate from the delegated
service port, so the delegate cannot veto a challenge by withholding consent.
The raw interpreter still checks and debits the real revision cost.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Delegation

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

abbrev State := LawExtension.Title Party Technology

def members (task : PublicTaskSpec Party Good) : List Party := task.slots.map ServiceSlot.bearer

structure Jurisdiction (Party Good Port : Type) where
  task : PublicTaskSpec Party Good
  service : Port
  challenge : Port
  separate : service ≠ challenge
  revisionCost : Bundle Good

variable (base : RawLaw Party Good Port Technology Instrument)
  (scope : Jurisdiction Party Good Port)

def law : RawLaw Party Good Port (State (Party := Party) (Technology := Technology)) Instrument where
  technique := fun technology => base.technique technology.1
  controller := fun technology port =>
    if port = scope.service then technology.2.getD (base.controller technology.1 port)
    else base.controller technology.1 port
  allowed := fun technology port actor =>
    if port = scope.challenge then decide (actor ∈ members scope.task)
    else if port = scope.service then match technology.2 with
      | some delegate => decide (actor = delegate)
      | none => decide (actor ∈ members scope.task)
    else base.allowed technology.1 port actor
  stockPort := fun technology => base.stockPort technology.1
  revisionPort := fun _ => scope.challenge
  revisionCost := fun _ _ => scope.revisionCost
  settlementUnit := base.settlementUnit
  settlementRate := base.settlementRate
  issuerPort := base.issuerPort
  necessities := fun current => base.necessities (LawExtension.eraseCurrent current)
  mandatoryMaintenance := fun current => base.mandatoryMaintenance (LawExtension.eraseCurrent current)
  policy := .opaque (fun current request => match request.operation with
    | .revise operator target => decide
        (operator = request.signer ∧ request.signer ∈ members scope.task ∧
          request.consents = [] ∧ current.technology.2.isSome = true ∧
          target = (current.technology.1, none))
    | _ => base.operationAllowed (LawExtension.eraseCurrent current)
        (LawExtension.eraseRequest request))
  duration := fun current => base.duration (LawExtension.eraseCurrent current)

def revokeRequest (current : RawCurrent Party Good (State (Party := Party) (Technology := Technology)) Instrument)
    (signer : Party) : Request Party Good Port (State (Party := Party) (Technology := Technology)) Instrument :=
  ⟨signer, [], scope.challenge, [scope.challenge], .revise signer (current.technology.1, none)⟩

structure ChallengeResources
    (current : RawCurrent Party Good (State (Party := Party) (Technology := Technology)) Instrument)
    (signer : Party) : Prop where
  nonnegative : NonnegativeBundle (Party × Good) (locate signer scope.revisionCost)
  independent : ∀ item ∈ locate signer scope.revisionCost,
    base.stockPort current.technology.1 item.1.1 item.1.2 ≠ scope.service ∧
    base.stockPort current.technology.1 item.1.1 item.1.2 ≠ scope.challenge ∧
    base.allowed current.technology.1
      (base.stockPort current.technology.1 item.1.1 item.1.2) signer = true
  affordable : ∀ item ∈ locate signer scope.revisionCost,
    flowAt (locate signer scope.revisionCost) item.1.1 item.1.2 ≤ current.stock item.1.1 item.1.2

omit [DecidableEq Good] [DecidableEq Instrument] in
theorem revoke_policy_iff
    (current : RawCurrent Party Good (State (Party := Party) (Technology := Technology)) Instrument)
    (signer : Party) :
    (law base scope).operationAllowed current (revokeRequest scope current signer) = true ↔
      signer ∈ members scope.task ∧ current.technology.2.isSome = true := by
  simp [law, RawLaw.operationAllowed, RawPolicy.eval, revokeRequest]

omit [DecidableEq Good] [DecidableEq Instrument] in
theorem challenge_port_is_independent
    (technology : State (Party := Party) (Technology := Technology)) (signer : Party) :
    (law base scope).allowed technology scope.challenge signer = true ↔
      signer ∈ members scope.task := by
  simp [law]

omit [DecidableEq Instrument] in
theorem generate_paid_challenge
    (current : RawCurrent Party Good (State (Party := Party) (Technology := Technology)) Instrument)
    (signer : Party) (member : signer ∈ members scope.task)
    (delegated : current.technology.2.isSome = true)
    (resources : ChallengeResources base scope current signer) :
    (law base scope).Valid current (revokeRequest scope current signer) := by
  refine ⟨⟨True.intro, (revoke_policy_iff base scope current signer).mpr ⟨member, delegated⟩⟩,
    ?_, True.intro, resources.nonnegative, ?_, resources.affordable⟩
  · intro port inside
    change port ∈ [scope.challenge] ++
      (locate signer scope.revisionCost).map
        (fun item => base.stockPort current.technology.1 item.1.1 item.1.2) ++
      [scope.challenge] at inside
    simp only [List.mem_append, List.mem_singleton] at inside
    rcases inside with (rfl | cost) | rfl
    · exact Or.inl ((challenge_port_is_independent base scope current.technology signer).mpr member)
    · obtain ⟨item, present, rfl⟩ := List.mem_map.mp cost
      have independent := resources.independent item present
      refine Or.inl ?_
      simp only [law, if_neg independent.2.1, if_neg independent.1, revokeRequest]
      exact independent.2.2
    · exact Or.inl ((challenge_port_is_independent base scope current.technology signer).mpr member)
  · intro item impossible
    exact False.elim (List.not_mem_nil impossible)

theorem actual_revoke
    (current : RawCurrent Party Good (State (Party := Party) (Technology := Technology)) Instrument)
    (signer : Party)
    (accepted : (law base scope).Valid current (revokeRequest scope current signer)) :
    ((law base scope).step current (revokeRequest scope current signer)).technology =
        (current.technology.1, none) ∧
      ((law base scope).step current (revokeRequest scope current signer)).claims = current.claims := by
  simp only [RawLaw.step, if_pos accepted]
  exact ⟨rfl, rfl⟩

omit [DecidableEq Good] [DecidableEq Instrument] in
theorem revoked_scope_requires_current_membership
    (technology : Technology) (actor : Party) :
    (law base scope).allowed (technology, none) scope.service actor = true ↔
      actor ∈ members scope.task := by
  simp [law, scope.separate]

omit [DecidableEq Instrument] in
theorem stale_request_is_rejected
    (current : RawCurrent Party Good (State (Party := Party) (Technology := Technology)) Instrument)
    (request : Request Party Good Port (State (Party := Party) (Technology := Technology)) Instrument)
    (revoked : current.technology.2 = none)
    (outside : request.signer ∉ members scope.task)
    (noFreshConsent : request.consents = [])
    (required : scope.service ∈ (law base scope).requiredPorts current request) :
    ¬ (law base scope).Valid current request := by
  intro accepted
  have guard := accepted.2.1 scope.service required
  have denied : (law base scope).allowed current.technology scope.service request.signer = false := by
    simp [law, scope.separate, revoked, outside]
  rcases guard with direct | consent
  · rw [denied] at direct
    cases direct
  · rw [noFreshConsent] at consent
    exact List.not_mem_nil consent

omit [DecidableEq Good] [DecidableEq Instrument] in
theorem other_port_is_preserved
    (technology : State (Party := Party) (Technology := Technology)) (port : Port) (actor : Party)
    (notService : port ≠ scope.service) (notChallenge : port ≠ scope.challenge) :
    (law base scope).allowed technology port actor = base.allowed technology.1 port actor := by
  simp [law, notService, notChallenge]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Delegation
