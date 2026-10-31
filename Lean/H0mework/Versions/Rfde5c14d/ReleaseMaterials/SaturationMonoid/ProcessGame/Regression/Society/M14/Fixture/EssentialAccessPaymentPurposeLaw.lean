import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.Capture.PaymentPurpose
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccessRelationFixture

/-!
# M14 pre-emitter essential-access payment-purpose law

This fixed source law maps the exact M3 payment activation to the exact
tenure relation seed.  It is imported by the UBI root restriction so the
generated purpose authority is present before emission, not reconstructed by
a post-emission consumer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14EssentialAccessPaymentPurposeLaw

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Money UBI
open UBI.Capture
open Lifecycle.Universal.FixedAdapter
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M14EssentialAccessRelationFixture

/-- Source-owned incidence law.  It selects an exact relation restriction;
it stores no sector verdict, price, capture result, or completed future. -/
def essentialAccessPaymentPurposeCompiler :
    SourceOwnedPaymentPurposeCompiler
      (activationCompiler := residualConsumerCompiler)
      (purposeRelationCompiler := essentialAccessRelationCompiler) where
  purposeSeed := fun _paymentSeed => exactEssentialAccessSeed .tenure
  purposeActor_eq := by
    intro paymentSeed
    apply Subtype.ext
    cases paymentSeed.1
    rfl

abbrev ExactTenurePaymentPurposeAt :=
  essentialAccessPaymentPurposeCompiler.SourceGeneratedPaymentPurposeAt
    exactResidualActivation

/-- Pre-emitter generated purpose authority consumed by the root payload. -/
theorem exactTenurePaymentPurpose : ExactTenurePaymentPurposeAt :=
  SourceOwnedPaymentPurposeCompiler.SourceGeneratedPaymentPurposeAt.generate
    essentialAccessPaymentPurposeCompiler exactResidualActivation

@[simp] theorem payment_purpose_relation_is_tenure :
    essentialAccessPaymentPurposeCompiler.purposeRelation
        exactResidualActivation = tenureRelation :=
  rfl

@[simp] theorem payment_purpose_phase_is_tenure :
    essentialAccessPaymentPurposeCompiler.purposePhase
        exactResidualActivation = .tenure :=
  rfl

@[simp] theorem payment_purpose_target_role_is_tenure_provider :
    essentialAccessPaymentPurposeCompiler.purposeTargetRole
        exactResidualActivation = .tenureProvider :=
  rfl

theorem payment_purpose_has_exact_trace_provenance :
    ∃ seed : essentialAccessRelationCompiler.ExactRelationSeed,
      (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
        state = core.targetFace.state Lifecycle.actualEventGame.source ∧
          essentialAccessRelationCompiler.relationSeedAt
            Lifecycle.actualEventGame.source state seed.1 ∧
          core.targetFace.SeedAt Lifecycle.actualEventGame.source state
            (essentialAccessRelationCompiler.beneficiaryActorSeed seed.1)) ∧
      seed.actor essentialAccessRelationCompiler =
        exactCounterpartyActor exactResidualActivation ∧
      essentialAccessRelationCompiler.relationOf seed = tenureRelation := by
  rcases exactTenurePaymentPurpose.exact_relation_actor_provenance with
    ⟨seed, provenance, actorEq, relationEq⟩
  exact ⟨seed, provenance, actorEq,
    relationEq.trans payment_purpose_relation_is_tenure⟩

end
end M14EssentialAccessPaymentPurposeLaw
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14EssentialAccessPaymentPurposeLaw.exactTenurePaymentPurpose
