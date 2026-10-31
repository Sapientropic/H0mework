import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M3.FiniteExchangeFixture

/-!
# Exchange authority negative controls

Relation, actor, admission-event and process-shaped data do not by themselves
mint an exchange.  The negative compiler below has all codomain machinery but
admits no exchange seed; consequently both the exact seed carrier and the
sealed generated-exchange carrier are empty.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M3ExchangeAuthorityRegression

open ResponsibilityLifecycle
open Lifecycle Universal Relations Exchange
open Lifecycle.Universal.FixedAdapter
open M3FiniteExchangeFixture

def rejectedCompiler : SourceOwnedExchangeCompiler core V P incidence
    relationCompiler where
  ExchangeSeed := Unit
  exchangeAdmittedAt := fun _ => False
  Leg := fun _ => Leg
  legDecidableEq := fun _ => inferInstance
  legs := fun _ => [.a, .b, .c, .d]
  legs_nodup := by intro seed; decide
  leg_mem := by intro seed leg; cases leg <;> simp
  principalLeg := fun _ => .a
  counterparty := fun _ => counterparty
  counterparty_involutive := by intro seed leg; cases leg <;> rfl
  counterparty_ne := by intro seed leg; cases leg <;> decide
  relationSeed := fun _ leg => legToken leg
  relationSeed_active := by
    intro seed leg admitted
    exact admitted.elim
  responsibilitySeed := fun _ leg => legToken leg
  responsibilitySeed_active := by
    intro seed leg admitted
    exact admitted.elim
  admissionEvent := fun _ leg => legToken leg
  sourceState := fun _ =>
    NativeResponsibilityProcess.GeneratedState.initial P
  parentStateOf := fun _ => .after

theorem rejectedExactSeed_isEmpty :
    IsEmpty rejectedCompiler.ExactExchangeSeed := by
  refine ⟨fun seed => ?_⟩
  rcases seed.2 with ⟨state, inTrace, atTarget, admitted⟩
  exact admitted

def rejectedLaw : SourceOwnedExchangeLaw core V P incidence
    relationCompiler where
  compiler := rejectedCompiler
  bearerOfActor := fun actor => .target actor.1
  protectedInterestOfActor := fun _ => ()
  actorSeed_eq := by
    intro seed leg
    exact (rejectedExactSeed_isEmpty.false seed).elim
  obligation_eq := by
    intro seed leg
    exact (rejectedExactSeed_isEmpty.false seed).elim
  sourceEvent_eq := by
    intro seed leg
    exact (rejectedExactSeed_isEmpty.false seed).elim
  bearer_eq := by
    intro seed leg
    exact (rejectedExactSeed_isEmpty.false seed).elim
  beneficiary_eq := by
    intro seed leg
    exact (rejectedExactSeed_isEmpty.false seed).elim
  restriction_parent_state_eq := by
    intro seed leg
    exact (rejectedExactSeed_isEmpty.false seed).elim
  sourceEvents_ne := by
    intro seed leg
    exact (rejectedExactSeed_isEmpty.false seed).elim
  counterpartyActors_ne := by
    intro seed leg
    exact (rejectedExactSeed_isEmpty.false seed).elim

theorem rejectedGeneratedExchange_isEmpty :
    IsEmpty rejectedLaw.GeneratedExchange := by
  refine ⟨fun exchange => ?_⟩
  exact rejectedExactSeed_isEmpty.false exchange.1

/-- Even though the installed relation compiler and responsibility process
remain available, no `NativeExchangeAt`-strength carrier exists without the
source admission predicate. -/
theorem relation_and_process_do_not_mint_exchange :
    Nonempty relationCompiler.ExactRelationSeed ∧
      Nonempty P.AdmissionEvent ∧
      IsEmpty rejectedLaw.GeneratedExchange :=
  ⟨⟨exactExchangeSeed.relationExactSeed exchangeCompiler .a⟩,
    ⟨.t0⟩, rejectedGeneratedExchange_isEmpty⟩

end M3ExchangeAuthorityRegression
end Society
end ProcessGame
end SaturationMonoid
