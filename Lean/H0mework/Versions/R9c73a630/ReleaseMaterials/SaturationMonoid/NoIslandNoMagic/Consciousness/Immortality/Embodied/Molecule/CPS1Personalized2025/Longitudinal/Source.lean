import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal.Reifier

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal

namespace Source

def chains : LongitudinalMaintenance where
  escalation :=
    { measurement :=
        { doseOneDay := cps1LongNat% "chains" "A_day22_escalation_redose" "measurement" "dose_one_day"
          doseOneMgPerKg := cps1LongRat% "chains" "A_day22_escalation_redose" "measurement" "dose_one_mg_per_kg"
          doseOneWellTolerated := cps1LongBool% "chains" "A_day22_escalation_redose" "measurement" "dose_one_well_tolerated"
          interdoseAmmonia := CPS1Personalized2025.Source.clinical.ammonia[1]!
          scavengerStillRequired := cps1LongBool% "chains" "A_day22_escalation_redose" "measurement" "scavenger_still_required"
          proteinRestrictionStillRequired :=
            cps1LongBool% "chains" "A_day22_escalation_redose" "measurement" "protein_restriction_still_required" }
      rationale :=
        { ruleDay := cps1LongNat% "chains" "A_day22_escalation_redose" "rationale" "rule_day"
          minimumIntervalDays := cps1LongNat% "chains" "A_day22_escalation_redose" "rationale" "minimum_interval_days"
          escalatedDoseMgPerKg := cps1LongRat% "chains" "A_day22_escalation_redose" "rationale" "escalated_dose_mg_per_kg"
          conditionA := cps1LongBool% "chains" "A_day22_escalation_redose" "rationale" "condition_a_initial_dose_safe_well_tolerated"
          conditionB := cps1LongBool% "chains" "A_day22_escalation_redose" "rationale" "condition_b_still_biochemical_features" }
      execution :=
        { day := cps1LongNat% "chains" "A_day22_escalation_redose" "execution" "day"
          doseMgPerKg := cps1LongRat% "chains" "A_day22_escalation_redose" "execution" "dose_mg_per_kg"
          daysAfterDoseOne := cps1LongNat% "chains" "A_day22_escalation_redose" "execution" "days_after_dose_one"
          infusionEvent := cps1LongText% "chains" "A_day22_escalation_redose" "execution" "in_fusion_event" }
      response :=
        { gpbHalveDay := cps1LongNat% "chains" "A_day22_escalation_redose" "response" "gpb_halve_day"
          gpbFrom := cps1LongRat% "chains" "A_day22_escalation_redose" "response" "gpb_from_ml_per_m2_per_day"
          gpbTo := cps1LongRat% "chains" "A_day22_escalation_redose" "response" "gpb_to_ml_per_m2_per_day"
          postAmmonia := CPS1Personalized2025.Source.clinical.ammonia[2]!
          oroticAfter := CPS1Personalized2025.Source.clinical.orotic[2]!
          crisisFreeThroughIllnesses :=
            (cps1LongBool% "chains" "A_day22_escalation_redose" "response" "hyperammonemic_crisis") == false
          fullProteinThroughIllnesses :=
            cps1LongBool% "chains" "A_day22_escalation_redose" "response" "full_protein_diet_maintained" } }
  glutamineRestore :=
    { measurement :=
        { baseline := cps1LongRat% "chains" "B_glutamine_triggered_reescalation" "measurement" "baseline_ml_per_m2_per_day"
          attempted := cps1LongRat% "chains" "B_glutamine_triggered_reescalation" "measurement" "attempted_ml_per_m2_per_day"
          glutamineRising := cps1LongBool% "chains" "B_glutamine_triggered_reescalation" "measurement" "glutamine_rising"
          window := cps1LongNats% "chains" "B_glutamine_triggered_reescalation" "measurement" "window_days" }
      rationale := { trigger := cps1LongText% "chains" "B_glutamine_triggered_reescalation" "rationale" "trigger" }
      execution :=
        { restored := cps1LongRat% "chains" "B_glutamine_triggered_reescalation" "execution" "restored_ml_per_m2_per_day"
          exactDatesUnreported := cps1LongBool% "chains" "B_glutamine_triggered_reescalation" "execution" "exact_dates_unreported" }
      response :=
        { scavengerBackAtFullDose := cps1LongBool% "chains" "B_glutamine_triggered_reescalation" "response" "scavenger_back_at_full_dose"
          redoseEvaluationContinued :=
            cps1LongBool% "chains" "B_glutamine_triggered_reescalation" "response" "day22_redose_evaluation_continued" } }
  proteinLiberalization :=
    { measurement :=
        { window := cps1LongNats% "chains" "C_post_dose1_stability_protein_liberalization" "measurement" "post_dose_one_window_days"
          intercurrentIllness := cps1LongText% "chains" "C_post_dose1_stability_protein_liberalization" "measurement" "intercurrent_illness"
          crisisFree := cps1LongBool% "chains" "C_post_dose1_stability_protein_liberalization" "measurement" "crisis_free" }
      rationale :=
        { window := cps1LongNats% "chains" "C_post_dose1_stability_protein_liberalization" "rationale" "window_days"
          discretion := cps1LongText% "chains" "C_post_dose1_stability_protein_liberalization" "rationale" "discretion" }
      execution :=
        { proteinLiberalized := cps1LongBool% "chains" "C_post_dose1_stability_protein_liberalization" "execution" "protein_liberalized"
          sickDay := cps1LongNat% "chains" "C_post_dose1_stability_protein_liberalization" "execution" "sick_day"
          sickDayManagement := cps1LongText% "chains" "C_post_dose1_stability_protein_liberalization" "execution" "sick_day_management" }
      response :=
        { fullProteinMaintainedThroughIllnesses :=
            cps1LongBool% "chains" "C_post_dose1_stability_protein_liberalization" "response" "full_protein_diet_maintained_through_illnesses" } }
  immuneMaintenance :=
    { measurement :=
        { genotype := cps1LongText% "chains" "D_immune_management_maintenance" "measurement" "genotype"
          baselineRisk := cps1LongText% "chains" "D_immune_management_maintenance" "measurement" "baseline_risk" }
      rationale := { steroidSparing := cps1LongBool% "chains" "D_immune_management_maintenance" "rationale" "steroid_sparing" }
      execution :=
        { sirolimusStartDay := cps1LongNat% "chains" "D_immune_management_maintenance" "execution" "sirolimus_start_day"
          tacrolimusStartDay := cps1LongNat% "chains" "D_immune_management_maintenance" "execution" "tacrolimus_start_day" }
      response :=
        { bothDosesAdministered := cps1LongBool% "chains" "D_immune_management_maintenance" "response" "both_doses_administered"
          chronicCorticosteroids := cps1LongBool% "chains" "D_immune_management_maintenance" "response" "chronic_corticosteroids" } }

def formulation : FormulationAccount where
  drugProduct := cps1LongText% "formulation_material_account" "drug_product"
  therapyShortName := cps1LongText% "formulation_material_account" "therapy_short_name"
  guideName := cps1LongText% "formulation_material_account" "guide" "registered_name" ++ " (" ++
    cps1LongText% "formulation_material_account" "guide" "code_name" ++ ")"
  mrnaName := cps1LongText% "formulation_material_account" "mrna" "code_name" ++ " (" ++
    cps1LongText% "formulation_material_account" "mrna" "editor" ++ ")"
  route := cps1LongText% "formulation_material_account" "route"
  doseOneNominalTotalRnaMg :=
    CPS1Personalized2025.Clinical.first.totalRnaDose * CPS1Personalized2025.Source.clinical.weights[0]!
  doseTwoNominalTotalRnaMg := none
  doseTwoWeightUnmeasured := cps1LongBool% "formulation_material_account" "dose_two_weight_unmeasured"
  doseTwoOverDoseOne := cps1LongRat% "formulation_material_account" "dose_two_over_dose_one_exact"
  citrullineMgPerKgPerDay := cps1LongRat% "formulation_material_account" "citrulline_mg_per_kg_per_day"
  citrullineUnchanged := cps1LongBool% "formulation_material_account" "citrulline_unchanged"
  supply :=
    { deliveryVehicle := cps1LongText% "formulation_material_account" "physical_supply_connection" "delivery_vehicle"
      consumerInterface := cps1LongText% "formulation_material_account" "physical_supply_connection" "consumer_interface"
      settled := false }

def residuals : Residuals where
  glutamineTriggerValue := .absent
  firstTaperDates := .absent
  proteinGramPerKgPerDayTrajectory := .absent
  day230WeightKg := .absent
  inPatientLiverEditingFraction := .absent
  thirdInfusionApril2025 := .absent

def capability : NextRoundCapability where
  carriedScavengerDose := chains.escalation.response.gpbTo
  carriedAmmoniaEvidence := chains.escalation.response.postAmmonia
  fullProteinDiet := chains.escalation.response.fullProteinThroughIllnesses

/-- Protocol-planned premedication (chain D plan facet): methylprednisone
(IV, 1 mg/kg) immediately prior to drug product infusion on dosing days.
The main text records no actual administration, so this is a plan and never
an executed event. -/
def immunePlan : ChainD.ProtocolPlan where
  methylprednisoneIvMgPerKg := cps1LongRat% "chains" "D_immune_management_maintenance" "plan" "methylprednisone_iv_mg_per_kg"
  methylprednisoneScope := cps1LongText% "chains" "D_immune_management_maintenance" "plan" "methylprednisone_scope"
  planned := cps1LongBool% "chains" "D_immune_management_maintenance" "plan" "planned"

def parentPacketSha : String := cps1LongText% "parent_packet_sha256"
def grandparentPacketSha : String := cps1LongText% "grandparent_packet_sha256"
def pdfSha : String := cps1LongText% "pdf_sha256"
def clinicalReference : String := cps1LongText% "clinical_reference"
def sourceVersion : String := cps1LongText% "source_version"

def quoteEscalation : String := cps1LongQuote% "q_escalation"
def quoteRedoseRule : String := cps1LongQuote% "q_redose_rule"
def quoteHalve : String := cps1LongQuote% "q_halve"
def quoteGlutamineRestore : String := cps1LongQuote% "q_glutamine_restore"
def quoteSickDay : String := cps1LongQuote% "q_sickday"
def quoteWindow721 : String := cps1LongQuote% "q_window721"
def quoteSteroidSparing : String := cps1LongQuote% "q_steroid_sparing"
def quoteMethylpred : String := cps1LongQuote% "q_methylpred"
def quoteCitrulline : String := cps1LongQuote% "q_citrulline"

theorem complete_inventory :
    chains.escalation.measurement.doseOneDay = 208 ∧
    chains.escalation.measurement.doseOneMgPerKg = 1/10 ∧
    chains.escalation.measurement.doseOneWellTolerated = true ∧
    chains.escalation.measurement.interdoseAmmonia = ⟨9,9,19⟩ ∧
    chains.escalation.measurement.scavengerStillRequired = true ∧
    chains.escalation.measurement.proteinRestrictionStillRequired = true ∧
    chains.escalation.rationale.ruleDay = 22 ∧
    chains.escalation.rationale.minimumIntervalDays = 21 ∧
    chains.escalation.rationale.escalatedDoseMgPerKg = 3/10 ∧
    chains.escalation.execution.day = 230 ∧
    chains.escalation.execution.doseMgPerKg = 3/10 ∧
    chains.escalation.execution.daysAfterDoseOne = 22 ∧
    chains.escalation.response.gpbHalveDay = 244 ∧
    chains.escalation.response.gpbFrom = 101/10 ∧
    chains.escalation.response.gpbTo = 5 ∧
    chains.escalation.response.postAmmonia = ⟨13,9,28⟩ ∧
    chains.escalation.response.oroticAfter = ⟨26/10,2,36/10⟩ ∧
    chains.escalation.response.crisisFreeThroughIllnesses = true ∧
    chains.escalation.response.fullProteinThroughIllnesses = true ∧
    chains.glutamineRestore.measurement.baseline = 101/10 ∧
    chains.glutamineRestore.measurement.attempted = 81/10 ∧
    chains.glutamineRestore.measurement.glutamineRising = true ∧
    chains.glutamineRestore.measurement.window = [208,230] ∧
    chains.glutamineRestore.execution.restored = 101/10 ∧
    chains.glutamineRestore.execution.exactDatesUnreported = true ∧
    chains.glutamineRestore.response.scavengerBackAtFullDose = true ∧
    chains.glutamineRestore.response.redoseEvaluationContinued = true ∧
    chains.proteinLiberalization.measurement.window = [208,230] ∧
    chains.proteinLiberalization.measurement.crisisFree = true ∧
    chains.proteinLiberalization.rationale.window = [7,21] ∧
    chains.proteinLiberalization.execution.proteinLiberalized = true ∧
    chains.proteinLiberalization.execution.sickDay = 225 ∧
    chains.proteinLiberalization.response.fullProteinMaintainedThroughIllnesses = true ∧
    chains.immuneMaintenance.rationale.steroidSparing = true ∧
    chains.immuneMaintenance.execution.sirolimusStartDay = 205 ∧
    chains.immuneMaintenance.execution.tacrolimusStartDay = 209 ∧
    immunePlan.methylprednisoneIvMgPerKg = 1 ∧
    immunePlan.planned = true ∧
    chains.immuneMaintenance.response.bothDosesAdministered = true ∧
    chains.immuneMaintenance.response.chronicCorticosteroids = false ∧
    formulation.drugProduct = "LNP.CPS1.Q335X" ∧
    formulation.route = "intravenous infusion" ∧
    formulation.doseOneNominalTotalRnaMg = 357/500 ∧
    formulation.doseTwoNominalTotalRnaMg = none ∧
    formulation.doseTwoWeightUnmeasured = true ∧
    formulation.doseTwoOverDoseOne = 3 ∧
    formulation.citrullineMgPerKgPerDay = 200 ∧
    formulation.citrullineUnchanged = true ∧
    formulation.supply.settled = false ∧
    capability.carriedScavengerDose = 5 ∧
    capability.carriedAmmoniaEvidence = ⟨13,9,28⟩ ∧
    capability.fullProteinDiet = true := by
  decide +kernel

theorem residuals_complete :
    residuals.glutamineTriggerValue = NoPublicValue.absent ∧
    residuals.firstTaperDates = NoPublicValue.absent ∧
    residuals.proteinGramPerKgPerDayTrajectory = NoPublicValue.absent ∧
    residuals.day230WeightKg = NoPublicValue.absent ∧
    residuals.inPatientLiverEditingFraction = NoPublicValue.absent ∧
    residuals.thirdInfusionApril2025 = NoPublicValue.absent := by
  decide +kernel

theorem same_source_identity :
    parentPacketSha = Ngs.Reifier.packetSha ∧
    grandparentPacketSha = CPS1Personalized2025.Reifier.packetSha256 ∧
    pdfSha = CPS1Personalized2025.Source.sourcePdfSha ∧
    clinicalReference = CPS1Personalized2025.Source.clinical.patient ∧
    sourceVersion =
      "NEJM 392;22 (June 12, 2025) main text pages 2237-2241; protocol final version 2025-03-11, FDA IND 31438" := by
  decide +kernel

theorem parent_values_used_not_rewritten :
    chains.escalation.measurement.interdoseAmmonia = CPS1Personalized2025.Source.clinical.ammonia[1]! ∧
    chains.escalation.response.postAmmonia = CPS1Personalized2025.Source.clinical.ammonia[2]! ∧
    chains.escalation.response.oroticAfter = CPS1Personalized2025.Source.clinical.orotic[2]! ∧
    chains.glutamineRestore.measurement.baseline = CPS1Personalized2025.Clinical.firstAttempt[0]! ∧
    chains.glutamineRestore.measurement.attempted = CPS1Personalized2025.Clinical.firstAttempt[1]! ∧
    chains.glutamineRestore.execution.restored = CPS1Personalized2025.Clinical.firstAttempt[2]! ∧
    chains.escalation.response.gpbFrom = CPS1Personalized2025.Clinical.firstAttempt[2]! ∧
    chains.escalation.response.gpbTo = CPS1Personalized2025.Clinical.finalMedication ∧
    formulation.doseOneNominalTotalRnaMg =
      CPS1Personalized2025.Clinical.first.totalRnaDose * CPS1Personalized2025.Source.clinical.weights[0]! := by
  decide +kernel

end Source

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal
