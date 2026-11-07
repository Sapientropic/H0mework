import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.Capacity.Observation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.UBIProofCarryingRootCapacity

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.M14OriginalExitDemandDeficit

open UBI UBI.Capacity
open M14UBIExitCapacityFixture M14UBIProofCarryingRootCapacity
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression M8AcceptanceSettlementRenewalRegression

private def independentQuote (value : Int) : Price.ExchangePriceObserverAt
    (settlementCompiler := settlementCompiler) (exactResidualActivation.occurrence residualConsumerCompiler) Int :=
  ⟨fun _ => value⟩

private theorem original_demand_has_one_continuation :
    (exitRelationCompiler.actionableFutureCodesAt independentExitRelation .target).card = 1 := by
  classical
  have survives := survivingCodes_card_eq_one
  change (noCapture.survivingExitCodes independentExitRelation).card = 1 at survives
  simpa [SourceOwnedPriceCaptureCompilerAt.survivingExitCodes, noCapture] using survives

theorem the_actual_capture_keeps_the_original_paid_root_and_records_one_lost_exit :
    exitCapacityProgram.purchasingPowerStanding = capturedProgram.purchasingPowerStanding ∧
      geometryCompiler.originalDemandGeometry.leftCarrier = capturedGeometryCompiler.originalDemandGeometry.leftCarrier ∧
      maximumDeficit geometryCompiler.originalDemandGeometry = 0 ∧
      maximumDeficit capturedGeometryCompiler.originalDemandGeometry = 1 ∧
      (type_of% (proofCarrying_and_ubi_share_root_authority)) := by
  have uncaptured := geometryCompiler.actual_exit_capacity_and_original_deficit_balance_the_full_source_demand
  rw [actionableExitCapacity_eq_one] at uncaptured
  have counted : 1 + maximumDeficit geometryCompiler.originalDemandGeometry = 1 :=
    uncaptured.trans original_demand_has_one_continuation
  have captured := capturedGeometryCompiler.full_capture_leaves_all_original_exit_demand_as_an_exact_deficit
    capturedProgram_fullPriceCapture
  exact ⟨rfl, rfl, by omega, captured.trans original_demand_has_one_continuation,
    proofCarrying_and_ubi_share_root_authority⟩

theorem every_quote_keeps_the_original_paid_capacity_and_the_actual_capture_loss (value : Int) :
    let observer := independentQuote value
    let reread := SourceOwnedExitGeometryCompilerAt.reobservedProgram (program := capturedProgram) observer
    reread.purchasingPowerStanding.priceObservation.value = value ∧
      reread.payment.nextGenerated = capturedProgram.payment.nextGenerated ∧
      (geometryCompiler.reobserve observer).actionableExitCapacity = 1 ∧
      maximumDeficit (capturedGeometryCompiler.reobserve observer).originalDemandGeometry = 1 := by
  let observer := independentQuote value
  have ordinary := geometryCompiler.changing_only_the_observation_keeps_original_exit_capacity_and_shortage observer
  have captured := capturedGeometryCompiler.changing_only_the_observation_keeps_original_exit_capacity_and_shortage observer
  exact ⟨rfl, rfl, ordinary.1.trans actionableExitCapacity_eq_one,
    captured.2.trans the_actual_capture_keeps_the_original_paid_root_and_records_one_lost_exit.2.2.2.1⟩

end SaturationMonoid.ProcessGame.Society.M14OriginalExitDemandDeficit
