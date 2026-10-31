import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.UBIProofCarryingRootRestriction

/-!
# M14 installed essential-access payment-purpose regression

The unique pre-emitter purpose law is consumed by
`SourceTenureCaptureFailure` inside the UBI root disposition.  Health and
platform remain genuine generated relations with the same coarse protected-
interest readout, but neither can replace that installed tenure purpose.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14EssentialAccessPaymentPurposeFixture

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Money UBI
open UBI.Capture
open Lifecycle.Universal.FixedAdapter
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M14EssentialAccessRelationFixture
open M14EssentialAccessPaymentPurposeLaw
open M14UBIProofCarryingRootRestriction

theorem rootSourceCarriesExactTenurePaymentPurpose :
    sourceGeneratedUBIDisposition.sourceFailure.paymentPurpose =
      exactTenurePaymentPurpose :=
  Subsingleton.elim _ _

/-- A health relation may share the beneficiary readout, but it cannot be
substituted for the purpose installed in the root disposition. -/
structure HealthPaymentPurposeForgery : Prop where
  installedPurpose :
    sourceGeneratedUBIDisposition.sourceFailure.paymentPurpose =
      exactTenurePaymentPurpose
  forgedRelation :
    essentialAccessPaymentPurposeCompiler.purposeRelation
      exactResidualActivation = healthRelation

theorem healthPaymentPurposeForgery_isEmpty :
    IsEmpty HealthPaymentPurposeForgery := by
  refine ⟨fun forged => tenure_health_relations_ne ?_⟩
  exact payment_purpose_relation_is_tenure.symm.trans forged.forgedRelation

structure PlatformPaymentPurposeForgery : Prop where
  installedPurpose :
    sourceGeneratedUBIDisposition.sourceFailure.paymentPurpose =
      exactTenurePaymentPurpose
  forgedRelation :
    essentialAccessPaymentPurposeCompiler.purposeRelation
      exactResidualActivation = platformRelation

theorem platformPaymentPurposeForgery_isEmpty :
    IsEmpty PlatformPaymentPurposeForgery := by
  refine ⟨fun forged => tenure_platform_relations_ne ?_⟩
  exact payment_purpose_relation_is_tenure.symm.trans forged.forgedRelation

abbrev AnyEssentialAccessPaymentPurposeCompiler :=
  SourceOwnedPaymentPurposeCompiler
    (activationCompiler := residualConsumerCompiler)
    (purposeRelationCompiler := essentialAccessRelationCompiler)

/-- Strong health control: no lawful payment-purpose compiler satisfying the
generated accepting-counterparty incidence can map this exact payment to the
health relation. -/
theorem no_payment_purpose_compiler_maps_exact_payment_to_health :
    ¬ ∃ compiler : AnyEssentialAccessPaymentPurposeCompiler,
      compiler.purposeRelation exactResidualActivation = healthRelation := by
  rintro ⟨compiler, relationEq⟩
  let seed := compiler.purposeSeed exactResidualActivation
  have seedValueEq : seed.1 = EssentialAccessEvent.health := by
    have values := congrArg Subtype.val relationEq
    change (compiler.purposeSeed exactResidualActivation).1 =
      EssentialAccessEvent.health at values
    exact values
  have seedEq : seed = exactEssentialAccessSeed .health := by
    apply Subtype.ext
    exact seedValueEq
  have actorIsHealth :
      seed.actor essentialAccessRelationCompiler = healthActor := by
    rw [seedEq]
    rfl
  have counterpartyIsHealth :
      exactCounterpartyActor exactResidualActivation = healthActor := by
    exact (compiler.purposeActor_eq exactResidualActivation).symm.trans
      actorIsHealth
  exact tenure_health_actors_ne
    (tenure_actor_is_exact_payment_counterparty.trans counterpartyIsHealth)

/-- Independent platform control with the same universal compiler scope. -/
theorem no_payment_purpose_compiler_maps_exact_payment_to_platform :
    ¬ ∃ compiler : AnyEssentialAccessPaymentPurposeCompiler,
      compiler.purposeRelation exactResidualActivation = platformRelation := by
  rintro ⟨compiler, relationEq⟩
  let seed := compiler.purposeSeed exactResidualActivation
  have seedValueEq : seed.1 = EssentialAccessEvent.platform := by
    have values := congrArg Subtype.val relationEq
    change (compiler.purposeSeed exactResidualActivation).1 =
      EssentialAccessEvent.platform at values
    exact values
  have seedEq : seed = exactEssentialAccessSeed .platform := by
    apply Subtype.ext
    exact seedValueEq
  have actorIsPlatform :
      seed.actor essentialAccessRelationCompiler = platformActor := by
    rw [seedEq]
    rfl
  have counterpartyIsPlatform :
      exactCounterpartyActor exactResidualActivation = platformActor := by
    exact (compiler.purposeActor_eq exactResidualActivation).symm.trans
      actorIsPlatform
  exact tenure_platform_actors_ne
    (tenure_actor_is_exact_payment_counterparty.trans counterpartyIsPlatform)

theorem same_coarse_readout_cannot_change_installed_payment_purpose :
    exchangeLaw.protectedInterestOfActor tenureActor =
        exchangeLaw.protectedInterestOfActor healthActor ∧
      exchangeLaw.protectedInterestOfActor tenureActor =
        exchangeLaw.protectedInterestOfActor platformActor ∧
      IsEmpty HealthPaymentPurposeForgery ∧
      IsEmpty PlatformPaymentPurposeForgery ∧
      (¬ ∃ compiler : AnyEssentialAccessPaymentPurposeCompiler,
        compiler.purposeRelation exactResidualActivation = healthRelation) ∧
      (¬ ∃ compiler : AnyEssentialAccessPaymentPurposeCompiler,
        compiler.purposeRelation exactResidualActivation = platformRelation) :=
  ⟨tenure_health_protectedInterest_readouts_eq,
    tenure_platform_protectedInterest_readouts_eq,
    healthPaymentPurposeForgery_isEmpty,
    platformPaymentPurposeForgery_isEmpty,
    no_payment_purpose_compiler_maps_exact_payment_to_health,
    no_payment_purpose_compiler_maps_exact_payment_to_platform⟩

end
end M14EssentialAccessPaymentPurposeFixture
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14EssentialAccessPaymentPurposeFixture.rootSourceCarriesExactTenurePaymentPurpose
#print axioms SaturationMonoid.ProcessGame.Society.M14EssentialAccessPaymentPurposeFixture.healthPaymentPurposeForgery_isEmpty
