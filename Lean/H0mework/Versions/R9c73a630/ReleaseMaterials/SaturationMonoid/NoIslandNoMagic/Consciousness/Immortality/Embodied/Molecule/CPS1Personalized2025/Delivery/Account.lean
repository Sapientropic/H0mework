import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery.Source

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery

namespace Account

/-- 执行消耗与剩余额度: the executed record carries exactly two administered
doses at their mg/kg levels with the dose-1 nominal mass paid and the dose-2
nominal mass absent; the protocol maximum minus the executed count leaves one
remaining protocol dose allowance. -/
theorem executed_ledger_and_remaining_allowance :
    Source.deliveryAccount.executedDoses.doseOne.administered = true ∧
    Source.deliveryAccount.executedDoses.doseTwo.administered = true ∧
    Source.deliveryAccount.executedDoses.doseOne.nominalTotalRnaMg =
      some Supply.Source.account.doseOneNominalTotalRnaMg ∧
    Source.deliveryAccount.executedDoses.doseTwo.nominalTotalRnaMg = none ∧
    Source.doseThreeEligibility.remainingProtocolDoses =
      Source.protocolGate.maxTotalDoses - Source.executedDoseCount ∧
    Source.doseThreeEligibility.remainingProtocolDoses = 1 := by
  decide +kernel

/-- 递送损耗: the batch-level 97% encapsulation splits the dose-1 mRNA mass
into encapsulated and unencapsulated legs at BOTH the mass and the
residue-sum substance level; each pair sums exactly to the parent's paid
ledger value, and the unencapsulated leg is strictly positive — a real loss,
not a relabeling. -/
theorem encapsulation_split :
    Source.deliverySplit.encapsulatedMrnaMg + Source.deliverySplit.unencapsulatedMrnaMg =
      Supply.Source.account.doseOneMrnaMg ∧
    Source.deliverySplit.encapsulatedMrnaResidueSumSubstanceMol +
      Source.deliverySplit.unencapsulatedMrnaResidueSumSubstanceMol =
      Supply.Source.account.mrnaResidueSumSubstanceMol ∧
    0 < Source.deliverySplit.unencapsulatedMrnaMg ∧
    Source.deliverySplit.unencapsulatedMrnaMg <
      Source.deliverySplit.encapsulatedMrnaMg ∧
    Source.deliverySplit.mrnaEncapsulationFraction =
      Supply.Source.account.clinicalBatch.mrnaEncapsulationFraction := by
  decide +kernel

/-- 协议规定值: the gate's own constants (plan side only). -/
theorem protocol_gate_values :
    Source.protocolGate.maxTotalDoses = 3 ∧
    Source.protocolGate.minimumIntervalDays = 21 ∧
    Source.protocolGate.thirdDoseOptionsMgPerKg = [3/10, 9/20] ∧
    Source.protocolGate.plannedPremedicationMgPerKg = 1 ∧
    Source.protocolGate.ruleEvidence = Source.quoteRedoseRule ∧
    Source.protocolGate.maxDosesEvidence = Source.quoteMaxThree ∧
    Source.protocolGate.optionsEvidence = Source.quoteEscalationOptions := by
  decide +kernel

/-- 下一轮执行能力由保留状态实际支付: the eligibility verdict is GENERATED —
condition A from the retained tolerance evidence, condition B from the
retained scavenger requirement, the remaining allowance from gate minus
executed, the earliest day from dose-2 day plus the minimum interval.  The
scavenger leg alone satisfies the and/or condition B because the halved dose
5.0 is still positive. -/
theorem capability_paid_by_retained_state :
    Source.doseThreeEligibility.conditionAPreviousTolerated =
      (Source.retainedState.doseOneWellTolerated &&
        Source.retainedState.doseTwoEventResolved &&
        Source.retainedState.halvingWithoutUnacceptableAdverseEffects) ∧
    Source.doseThreeEligibility.conditionBBiochemicalFeaturesPersist =
      decide (0 < Source.retainedState.carriedScavengerMlPerM2PerDay) ∧
    0 < Source.retainedState.carriedScavengerMlPerM2PerDay ∧
    Source.retainedState.carriedScavengerMlPerM2PerDay = 5 ∧
    Source.doseThreeEligibility.conditionAPreviousTolerated = true ∧
    Source.doseThreeEligibility.conditionBBiochemicalFeaturesPersist = true ∧
    Source.doseThreeEligibility.earliestGateDay =
      Source.executedDoses.doseTwo.day + Source.protocolGate.minimumIntervalDays ∧
    Source.doseThreeEligibility.earliestGateDay = 251 ∧
    Source.doseThreeEligibility.optionsMgPerKg =
      Source.protocolGate.thirdDoseOptionsMgPerKg := ⟨rfl, rfl, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, rfl,
    by decide +kernel, rfl⟩

/-- 计划与执行严格分开: the protocol's planned premedication (methylprednisone
IV 1 mg/kg on dosing days) is a plan entry consumed from the parent's own
plan record; neither executed infusion event carries it, and the executed
record and the gate never mix. -/
theorem plan_execution_separated :
    Source.protocolGate.plannedPremedicationMgPerKg =
      Longitudinal.Source.immunePlan.methylprednisoneIvMgPerKg ∧
    Longitudinal.Source.immunePlan.planned = true ∧
    Source.executedDoses.doseOne.infusionEvent = "" ∧
    Source.executedDoses.doseTwo.infusionEvent =
      "coughing episode resolved with nasal suctioning" ∧
    Source.charsContain "methylpred".toList Source.executedDoses.doseOne.infusionEvent.toList =
      false ∧
    Source.charsContain "methylpred".toList Source.executedDoses.doseTwo.infusionEvent.toList =
      false := by
  decide +kernel

/-- 资格不是执行: dose-3 eligibility is paid by the retained state, but the
actual third dose exists only as a press statement and stays excluded — the
eligibility record itself proves it was never executed here. -/
theorem eligibility_is_capability_not_execution :
    Source.doseThreeEligibility.conditionAPreviousTolerated = true ∧
    Source.doseThreeEligibility.conditionBBiochemicalFeaturesPersist = true ∧
    Source.doseThreeEligibility.actualThirdDoseExecuted = false ∧
    Source.deliveryResiduals.thirdInfusionApril2025 = Longitudinal.NoPublicValue.absent := by
  decide +kernel

/-- The parent's OPEN delivery/energy account is preserved: nothing here
settles it, the same consumer interface is carried verbatim and the
delivery-energy residual stays `absent`. -/
theorem delivery_energy_stays_open :
    Supply.Source.physicalDelivery.settled = false ∧
    Supply.Source.physicalDelivery.energyAccountSettled = false ∧
    Supply.Source.physicalDelivery.energyAccount = Longitudinal.NoPublicValue.absent ∧
    Source.deliveryCapability.energyAccountOpen = true ∧
    Source.deliveryCapability.consumerInterface =
      Supply.Source.physicalDelivery.consumerInterface ∧
    Source.deliveryResiduals.deliveryEnergyAccount = Longitudinal.NoPublicValue.absent := by
  decide +kernel

end Account

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery
