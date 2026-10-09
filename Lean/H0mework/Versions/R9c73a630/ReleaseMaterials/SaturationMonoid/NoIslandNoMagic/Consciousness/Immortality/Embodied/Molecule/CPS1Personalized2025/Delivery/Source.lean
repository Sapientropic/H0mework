import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery.Reifier

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery

namespace Source

/-- The two actually executed infusions of the same patient.  Days, mg/kg
levels, the dose-2 interval and the infusion event come from the packet's
typed boundary; the dose-1 nominal mass is consumed from the parent's paid
supply account (never re-typed), and the dose-2 nominal mass stays `none`
because the day-230 weight was unmeasured. -/
def executedDoses : ExecutedDoses where
  doseOne :=
    { day := cps1DeliveryNat% "executed_doses" "dose_one" "day"
      doseMgPerKg := cps1DeliveryRat% "executed_doses" "dose_one" "mg_per_kg"
      nominalTotalRnaMg := some Supply.Source.account.doseOneNominalTotalRnaMg
      weightBasisDay := some (cps1DeliveryNat% "executed_doses" "dose_one" "weight_basis_day")
      nominalBasis := cps1DeliveryText% "executed_doses" "dose_one" "nominal_basis"
      infusionEvent := cps1DeliveryText% "executed_doses" "dose_one" "infusion_event"
      administered := cps1DeliveryBool% "executed_doses" "dose_one" "administered" }
  doseTwo :=
    { day := cps1DeliveryNat% "executed_doses" "dose_two" "day"
      doseMgPerKg := cps1DeliveryRat% "executed_doses" "dose_two" "mg_per_kg"
      nominalTotalRnaMg := none
      weightBasisDay := none
      nominalBasis := cps1DeliveryText% "executed_doses" "dose_two" "nominal_basis"
      infusionEvent := cps1DeliveryText% "executed_doses" "dose_two" "infusion_event"
      administered := cps1DeliveryBool% "executed_doses" "dose_two" "administered" }
  intervalDays := cps1DeliveryNat% "executed_doses" "dose_two" "interval_after_dose_one_days"

/-- The batch-level delivery split is COMPUTED from the parent's paid values:
the dose-1 mRNA mass times the clinical-batch 97% encapsulation fraction and
its complement. -/
def mrnaEncapsulationFraction : ℚ :=
  Supply.Source.account.clinicalBatch.mrnaEncapsulationFraction
def encapsulatedMrnaMg : ℚ :=
  Supply.Source.account.doseOneMrnaMg * mrnaEncapsulationFraction
def unencapsulatedMrnaMg : ℚ :=
  Supply.Source.account.doseOneMrnaMg * (1 - mrnaEncapsulationFraction)
def encapsulatedMrnaSubstanceMol : ℚ :=
  encapsulatedMrnaMg / 10 ^ 3 / Supply.Source.account.mrnaResidueSumGPerMol
def unencapsulatedMrnaSubstanceMol : ℚ :=
  unencapsulatedMrnaMg / 10 ^ 3 / Supply.Source.account.mrnaResidueSumGPerMol

def deliverySplit : DeliverySplit where
  mrnaEncapsulationFraction := mrnaEncapsulationFraction
  encapsulatedMrnaMg := encapsulatedMrnaMg
  unencapsulatedMrnaMg := unencapsulatedMrnaMg
  encapsulatedMrnaResidueSumSubstanceMol := encapsulatedMrnaSubstanceMol
  unencapsulatedMrnaResidueSumSubstanceMol := unencapsulatedMrnaSubstanceMol
  basis := cps1DeliveryText% "delivery_split" "basis"

/-- The protocol gate: plan-side rules only, each carrying its verbatim
quote.  Nothing here claims an executed event. -/
def protocolGate : ProtocolGate where
  maxTotalDoses := cps1DeliveryNat% "protocol_gate" "max_total_doses"
  minimumIntervalDays := cps1DeliveryNat% "protocol_gate" "minimum_interval_days"
  conditionA := cps1DeliveryText% "protocol_gate" "condition_a"
  conditionB := cps1DeliveryText% "protocol_gate" "condition_b"
  thirdDoseOptionsMgPerKg := cps1DeliveryRats% "protocol_gate" "third_dose_options_mg_per_kg"
  plannedPremedicationMgPerKg := cps1DeliveryRat% "protocol_gate" "planned_premedication_mg_per_kg"
  ruleEvidence := cps1DeliveryQuote% "q_redose_rule"
  maxDosesEvidence := cps1DeliveryQuote% "q_max3"
  optionsEvidence := cps1DeliveryQuote% "q_escalation_options"
  premedicationEvidence := cps1DeliveryQuote% "q_methylpred"

def quoteHalve : String := cps1DeliveryQuote% "q_halve"

/-- Kernel-reducible substring check: `String.splitOn`/`findSubstr?` are
extern primitives and never reduce in `decide`, so quote containment is
checked on character lists.  Non-recursive so no `_unsafe_rec` companion
enters the owned closure. -/
def charsContain (needle hay : List Char) : Bool :=
  !needle.isEmpty &&
    ((List.range (hay.length + 1)).any (fun start => needle.isPrefixOf (hay.drop start)))

/-- The retained post-execution state: every leg is consumed from the parent's
paid longitudinal record or checked against the reified executed event and
verbatim quotes — none is a copied constant.  `doseTwoEventResolved` is the
actual substring check on the recorded event; `halvingWithout...` is the
verbatim check on the halving quote. -/
def retainedState : RetainedState where
  carriedScavengerMlPerM2PerDay := Longitudinal.Source.capability.carriedScavengerDose
  postDoseTwoAmmonia := Longitudinal.Source.capability.carriedAmmoniaEvidence
  postDoseTwoOrotic := Longitudinal.Source.chains.escalation.response.oroticAfter
  fullProteinDietMaintained := Longitudinal.Source.capability.fullProteinDiet
  crisisFreeThroughIllnesses := Longitudinal.Source.chains.escalation.response.crisisFreeThroughIllnesses
  viralIllnessesAfterDoseTwo := cps1DeliveryNat% "retained_state" "viral_illnesses_after_dose_two"
  doseOneWellTolerated := Longitudinal.Source.chains.escalation.measurement.doseOneWellTolerated
  doseTwoEventResolved :=
    charsContain "resolved".toList executedDoses.doseTwo.infusionEvent.toList
  halvingWithoutUnacceptableAdverseEffects :=
    charsContain "without unacceptable adverse effects".toList quoteHalve.toList
  immuneMaintenanceOngoing :=
    Longitudinal.Source.chains.immuneMaintenance.response.bothDosesAdministered

/-- The executed dose count is computed from the administered flags. -/
def executedDoseCount : Nat :=
  (if executedDoses.doseOne.administered then 1 else 0) +
    (if executedDoses.doseTwo.administered then 1 else 0)

/-- The evaluated dose-3 eligibility: every field is generated — conditions
from the retained state, the remaining allowance from gate minus executed,
the earliest day from dose-2 day plus the minimum interval — and the actual
third dose is press-only, so `actualThirdDoseExecuted` is `false`. -/
def doseThreeEligibility : DoseThreeEligibility where
  conditionAPreviousTolerated :=
    retainedState.doseOneWellTolerated &&
      retainedState.doseTwoEventResolved &&
      retainedState.halvingWithoutUnacceptableAdverseEffects
  conditionBBiochemicalFeaturesPersist :=
    decide (0 < retainedState.carriedScavengerMlPerM2PerDay)
  executedDoseCount := executedDoseCount
  remainingProtocolDoses := protocolGate.maxTotalDoses - executedDoseCount
  earliestGateDay := executedDoses.doseTwo.day + protocolGate.minimumIntervalDays
  optionsMgPerKg := protocolGate.thirdDoseOptionsMgPerKg
  actualThirdDoseExecuted := false

def deliveryAccount : DeliveryAccount where
  executedDoses := executedDoses
  deliverySplit := deliverySplit
  protocolGate := protocolGate

/-- Explicit residuals: infusion duration/rate/volume, LNP lipid masses, the
gRNA encapsulation fraction, the physical remaining inventory, the day-230
weight, the in-patient liver editing fraction, the press-only third infusion
and the delivery energy account — all `absent`; no direction or magnitude is
claimed anywhere. -/
def deliveryResiduals : DeliveryResiduals where
  infusionDurationRateAndVolume := .absent
  lnpLipidComponentMasses := .absent
  grnaEncapsulationFraction := .absent
  physicalInventoryRemaining := .absent
  day230WeightKg := .absent
  inPatientLiverEditingFraction := .absent
  thirdInfusionApril2025 := .absent
  deliveryEnergyAccount := .absent

/-- 下一轮能力: the retained state plus the evaluated eligibility are carried
forward with the same named consumer interface; the energy account stays
OPEN, read off the packet's `energy_account_settled = false` flag. -/
def deliveryCapability : DeliveryCapability where
  retained := retainedState
  eligibility := doseThreeEligibility
  consumerInterface := cps1DeliveryText% "physical_delivery" "consumer_interface"
  energyAccountOpen := !(cps1DeliveryBool% "physical_delivery" "energy_account_settled")

def parentPacketSha : String := cps1DeliveryText% "parent_packet_sha256"
def grandparentPacketSha : String := cps1DeliveryText% "grandparent_packet_sha256"
def greatGrandparentPacketSha : String := cps1DeliveryText% "great_grandparent_packet_sha256"
def pdfSha : String := cps1DeliveryText% "pdf_sha256"
def clinicalReference : String := cps1DeliveryText% "clinical_reference"
def sourceVersion : String := cps1DeliveryText% "source_version"
def sourceClock : String := cps1DeliveryText% "source_clock"

def quoteDoseOne : String := cps1DeliveryQuote% "q_dose1"
def quoteEscalation : String := cps1DeliveryQuote% "q_escalation"
def quoteCough : String := cps1DeliveryQuote% "q_cough"
def quoteIllness : String := cps1DeliveryQuote% "q_illness"
def quoteIvDose : String := cps1DeliveryQuote% "q_iv_dose"
def quoteRedoseRule : String := cps1DeliveryQuote% "q_redose_rule"
def quoteCommittee : String := cps1DeliveryQuote% "q_committee"
def quoteMaxThree : String := cps1DeliveryQuote% "q_max3"
def quoteEscalationOptions : String := cps1DeliveryQuote% "q_escalation_options"
def quoteMethylpred : String := cps1DeliveryQuote% "q_methylpred"
def quoteBatchMeasured : String := cps1DeliveryQuote% "q_batch_measured"

theorem complete_inventory :
    executedDoses.doseOne.day = 208 ∧
    executedDoses.doseOne.doseMgPerKg = 1/10 ∧
    executedDoses.doseOne.nominalTotalRnaMg = some (357/500 : ℚ) ∧
    executedDoses.doseOne.weightBasisDay = some 207 ∧
    executedDoses.doseOne.administered = true ∧
    executedDoses.doseTwo.day = 230 ∧
    executedDoses.doseTwo.doseMgPerKg = 3/10 ∧
    executedDoses.doseTwo.nominalTotalRnaMg = none ∧
    executedDoses.doseTwo.weightBasisDay = none ∧
    executedDoses.doseTwo.administered = true ∧
    executedDoses.intervalDays = 22 ∧
    deliverySplit.mrnaEncapsulationFraction = 97/100 ∧
    deliverySplit.encapsulatedMrnaMg = 1649/5000 ∧
    deliverySplit.unencapsulatedMrnaMg = 51/5000 ∧
    deliverySplit.encapsulatedMrnaResidueSumSubstanceMol = 1649/8282682650000 ∧
    deliverySplit.unencapsulatedMrnaResidueSumSubstanceMol = 51/8282682650000 ∧
    protocolGate.maxTotalDoses = 3 ∧
    protocolGate.minimumIntervalDays = 21 ∧
    protocolGate.thirdDoseOptionsMgPerKg = [3/10, 9/20] ∧
    protocolGate.plannedPremedicationMgPerKg = 1 ∧
    retainedState.carriedScavengerMlPerM2PerDay = 5 ∧
    retainedState.postDoseTwoAmmonia = ⟨13,9,28⟩ ∧
    retainedState.postDoseTwoOrotic = ⟨26/10,2,36/10⟩ ∧
    retainedState.fullProteinDietMaintained = true ∧
    retainedState.crisisFreeThroughIllnesses = true ∧
    retainedState.viralIllnessesAfterDoseTwo = 2 ∧
    retainedState.doseOneWellTolerated = true ∧
    retainedState.doseTwoEventResolved = true ∧
    retainedState.halvingWithoutUnacceptableAdverseEffects = true ∧
    retainedState.immuneMaintenanceOngoing = true ∧
    doseThreeEligibility.conditionAPreviousTolerated = true ∧
    doseThreeEligibility.conditionBBiochemicalFeaturesPersist = true ∧
    doseThreeEligibility.executedDoseCount = 2 ∧
    doseThreeEligibility.remainingProtocolDoses = 1 ∧
    doseThreeEligibility.earliestGateDay = 251 ∧
    doseThreeEligibility.optionsMgPerKg = [3/10, 9/20] ∧
    doseThreeEligibility.actualThirdDoseExecuted = false ∧
    deliveryCapability.energyAccountOpen = true := by
  decide +kernel

theorem residuals_complete :
    deliveryResiduals.infusionDurationRateAndVolume = Longitudinal.NoPublicValue.absent ∧
    deliveryResiduals.lnpLipidComponentMasses = Longitudinal.NoPublicValue.absent ∧
    deliveryResiduals.grnaEncapsulationFraction = Longitudinal.NoPublicValue.absent ∧
    deliveryResiduals.physicalInventoryRemaining = Longitudinal.NoPublicValue.absent ∧
    deliveryResiduals.day230WeightKg = Longitudinal.NoPublicValue.absent ∧
    deliveryResiduals.inPatientLiverEditingFraction = Longitudinal.NoPublicValue.absent ∧
    deliveryResiduals.thirdInfusionApril2025 = Longitudinal.NoPublicValue.absent ∧
    deliveryResiduals.deliveryEnergyAccount = Longitudinal.NoPublicValue.absent := by
  decide +kernel

theorem same_source_identity :
    parentPacketSha = Supply.Reifier.packetSha ∧
    grandparentPacketSha = Longitudinal.Reifier.packetSha ∧
    greatGrandparentPacketSha = CPS1Personalized2025.Reifier.packetSha256 ∧
    pdfSha = CPS1Personalized2025.Source.sourcePdfSha ∧
    clinicalReference = CPS1Personalized2025.Source.clinical.patient ∧
    sourceClock = "day after birth; every longitudinal day is a postnatal day" ∧
    sourceVersion =
      "NEJM 392;22 (June 12, 2025) main text pages 2237-2241; protocol final version 2025-03-11, FDA IND 31438" := by
  decide +kernel

/-- The executed ledger, the delivery split and the retained state all consume
the parent's paid values directly; the dose-2 interval is the parent's own
day arithmetic. -/
theorem parent_values_used_not_rewritten :
    executedDoses.doseOne.day = CPS1Personalized2025.Clinical.first.day ∧
    executedDoses.doseOne.doseMgPerKg = CPS1Personalized2025.Clinical.first.totalRnaDose ∧
    executedDoses.doseOne.nominalTotalRnaMg =
      some Supply.Source.account.doseOneNominalTotalRnaMg ∧
    executedDoses.doseTwo.day = CPS1Personalized2025.Clinical.second.day ∧
    executedDoses.doseTwo.doseMgPerKg = CPS1Personalized2025.Clinical.second.totalRnaDose ∧
    executedDoses.intervalDays =
      CPS1Personalized2025.Clinical.second.day - CPS1Personalized2025.Clinical.first.day ∧
    deliverySplit.mrnaEncapsulationFraction =
      Supply.Source.account.clinicalBatch.mrnaEncapsulationFraction ∧
    deliverySplit.encapsulatedMrnaMg + deliverySplit.unencapsulatedMrnaMg =
      Supply.Source.account.doseOneMrnaMg ∧
    retainedState.carriedScavengerMlPerM2PerDay =
      Longitudinal.Source.capability.carriedScavengerDose ∧
    retainedState.postDoseTwoAmmonia = CPS1Personalized2025.Source.clinical.ammonia[2]! ∧
    retainedState.postDoseTwoOrotic = CPS1Personalized2025.Source.clinical.orotic[2]! ∧
    retainedState.doseOneWellTolerated =
      Longitudinal.Source.chains.escalation.measurement.doseOneWellTolerated ∧
    retainedState.immuneMaintenanceOngoing =
      Longitudinal.Source.chains.immuneMaintenance.response.bothDosesAdministered ∧
    protocolGate.plannedPremedicationMgPerKg =
      Longitudinal.Source.immunePlan.methylprednisoneIvMgPerKg := by
  decide +kernel

/-- The packet's independently computed cross-check metadata equals the values
computed here from the parent ledger and the reified gate. -/
theorem packet_crosscheck :
    (cps1DeliveryRat% "computed" "dose_one_nominal_total_rna_mg") =
      executedDoses.doseOne.nominalTotalRnaMg.getD 0 ∧
    (cps1DeliveryRat% "computed" "encapsulated_mrna_mg") =
      deliverySplit.encapsulatedMrnaMg ∧
    (cps1DeliveryRat% "computed" "unencapsulated_mrna_mg") =
      deliverySplit.unencapsulatedMrnaMg ∧
    (cps1DeliveryRat% "computed" "encapsulated_mrna_residue_sum_substance_mol") =
      deliverySplit.encapsulatedMrnaResidueSumSubstanceMol ∧
    (cps1DeliveryRat% "computed" "unencapsulated_mrna_residue_sum_substance_mol") =
      deliverySplit.unencapsulatedMrnaResidueSumSubstanceMol ∧
    (cps1DeliveryRat% "computed" "remaining_protocol_doses") =
      (doseThreeEligibility.remainingProtocolDoses : ℚ) ∧
    (cps1DeliveryRat% "computed" "earliest_gate_day") =
      (doseThreeEligibility.earliestGateDay : ℚ) ∧
    (cps1DeliveryRat% "computed" "interval_days") = (executedDoses.intervalDays : ℚ) := by
  decide +kernel

theorem quotes_present :
    quoteDoseOne.length > 0 ∧ quoteEscalation.length > 0 ∧
    quoteCough.length > 0 ∧ quoteHalve.length > 0 ∧
    quoteIllness.length > 0 ∧ quoteIvDose.length > 0 ∧
    quoteRedoseRule.length > 0 ∧ quoteCommittee.length > 0 ∧
    quoteMaxThree.length > 0 ∧ quoteEscalationOptions.length > 0 ∧
    quoteMethylpred.length > 0 ∧ quoteBatchMeasured.length > 0 := by
  decide +kernel

end Source

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery
