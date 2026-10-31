import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M8.Renewal.SourceInstalledRenewalProjectionRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M8.Money.PurchasingPowerStandingRegression

/-!
# M8 purchasing-power root installation

The source-backed purchasing-power standing and its arbitrary-step renewal
consumer are installed in the existing root source before emission.  Price
remains a readout on the exact open settlement; the root payload adds no
money registry or ledger.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M8MoneyRootInstallationRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Renewal Money
open Lifecycle.Universal.FixedAdapter
open Settlement.SourceOwnedSettlementCompiler
open M3FiniteExchangeFixture
open M3ExchangeSettlementPriceRegression
open M8ExactSettlementRenewalFixture
open M8AcceptanceSettlementRenewalRegression
open M8PurchasingPowerStandingRegression
open M8SourceInstalledRenewalProjectionRegression

def rootPriceObserver
    (seed : residualConsumerCompiler.ExactActivationSeed) :=
  PriceObserverAt.zero
    (OpenSettlement := OpenSettlementAt settlementCompiler
      (seed.occurrence residualConsumerCompiler))
    (Value := Int)

def RootPurchasingPowerConsumerAt
    (seed : residualConsumerCompiler.ExactActivationSeed) : Type :=
  PurchasingPowerStandingAt seed (rootPriceObserver seed)

def RootPurchasingPowerDispositionAt
    (seed : residualConsumerCompiler.ExactActivationSeed) : Type :=
  PurchasingPowerRenewalStepAt seed (rootPriceObserver seed)

def rootPurchasingPowerStanding :
    RootPurchasingPowerConsumerAt exactResidualActivation :=
  PurchasingPowerStandingAt.generate exactCounterpartyAcceptance

def rootPurchasingPowerStep :
    RootPurchasingPowerDispositionAt exactResidualActivation :=
  purchasingPowerRenewalStep exactResidualActivation
    (rootPriceObserver exactResidualActivation)
    exactCounterpartyAcceptance

def moneyRootLaw :=
  singletonRootRenewalLaw Lifecycle.actualEventGame
    residualConsumerCompiler.activationSeedAt
    RootPurchasingPowerConsumerAt RootPurchasingPowerDispositionAt
    exactResidualActivation rootPurchasingPowerStanding
    rootPurchasingPowerStep

abbrev moneyInstalledRoot := rootWithRenewalLaw moneyRootLaw
abbrev moneyRootVisit := initialVisitWithRenewalLaw moneyRootLaw
abbrev moneyRootRecognition := recognitionWithRenewalLaw moneyRootLaw

def moneyInstalledRenewal :
    SourceInstalledRenewalAt moneyRootRecognition moneyRootVisit :=
  installedAtInitialVisit moneyRootLaw PUnit.unit rfl

def moneyRootLocalFace :=
  moneyInstalledRenewal.localFace
    (fun _ seed =>
      (residualConsumerCompiler.openSettlement seed.1).obligation.lineage)
    moneyStandingOf

@[simp] theorem money_root_seed_exact :
    moneyRootLocalFace.sourceSeed = exactResidualActivation :=
  rfl

@[simp] theorem money_root_purchasing_standing_exact :
    moneyRootLocalFace.responsibilityConsumer =
      rootPurchasingPowerStanding :=
  rfl

@[simp] theorem money_root_renewal_step_exact :
    moneyRootLocalFace.exactDisposition = rootPurchasingPowerStep :=
  rfl

theorem money_root_open_price_exact :
    moneyRootLocalFace.responsibilityConsumer.priceObservation.openSettlement =
      exactOpenSettlement exactResidualActivation :=
  rfl

theorem money_root_next_is_source_generated :
    moneyRootLocalFace.exactDisposition.nextGenerated =
      PurchasingPowerStandingAt.nextGeneratedState
        moneyRootLocalFace.responsibilityConsumer :=
  moneyRootLocalFace.exactDisposition.next_eq

structure MoneyRootInstallationCertificate : Type 3 where
  installed : SourceInstalledRenewalAt moneyRootRecognition moneyRootVisit
  localFace : SourceGeneratedRenewalFace Lifecycle.actualEventGame
    residualConsumerCompiler.ActivationSeed
    residualConsumerCompiler.activationSeedAt
    (fun _ => V.Lineage)
    (fun _ seed =>
      (residualConsumerCompiler.openSettlement seed.1).obligation.lineage)
    (AdmittedObligation V) moneyStandingOf
    RootPurchasingPowerConsumerAt RootPurchasingPowerDispositionAt
  exactStanding : localFace.responsibilityConsumer =
    rootPurchasingPowerStanding
  exactRenewalStep : localFace.exactDisposition = rootPurchasingPowerStep
  rootConsumer : RenewalResponsibilityConsumerAt installed.operationalAuthority
  rootProjectionAndNext :
    let evolution := moneyInstalledRoot.canonicalCausalAnswerAndNext
      (ULift.up moneyRootVisit)
    evolution.generated =
        moneyInstalledRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
          moneyRootVisit ∧
      HEq (evolution.generated.projectionOutcome
          moneyRootRecognition.rootProjection)
        (moneyRootRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
          (moneyInstalledRoot.emitted moneyRootVisit.current)) ∧
      evolution.nextCurrent =
        moneyInstalledRoot.generatedNextCurrentAt moneyRootVisit

def moneyRootInstallationDirectConsumer :
    MoneyRootInstallationCertificate where
  installed := moneyInstalledRenewal
  localFace := moneyRootLocalFace
  exactStanding := money_root_purchasing_standing_exact
  exactRenewalStep := money_root_renewal_step_exact
  rootConsumer := moneyInstalledRenewal.rootResponsibilityConsumer
  rootProjectionAndNext :=
    moneyInstalledRenewal.rootAnswerAndNext_factorizes

end
end M8MoneyRootInstallationRegression
end Society
end ProcessGame
end SaturationMonoid
