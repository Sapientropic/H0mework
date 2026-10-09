import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal.Execution

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal

namespace Response

/-- The ammonia course is preserved as non-monotone: the inter-dose median 9 is below
the post-dose-2 median 13, which is itself below the pre-dose median 23.  A monotone
improvement claim would be false; the recorded response keeps the rebound. -/
theorem ammonia_course_non_monotone :
    CPS1Personalized2025.Source.clinical.ammonia[1]!.median <
      CPS1Personalized2025.Source.clinical.ammonia[2]!.median ∧
    CPS1Personalized2025.Source.clinical.ammonia[2]!.median <
      CPS1Personalized2025.Source.clinical.ammonia[0]!.median ∧
    Source.chains.escalation.response.postAmmonia.median = 13 ∧
    Source.chains.escalation.measurement.interdoseAmmonia.median = 9 := by
  decide +kernel

/-- The day-244 reduction reached the recorded 5.0 from 10.1 ml/m²/day: the
exact book ratio is 50/101 via the parent's recorded values — never 1/2. -/
theorem halved_medication_ratio :
    CPS1Personalized2025.Clinical.finalMedication /
      CPS1Personalized2025.Clinical.firstAttempt[2]! = 50/101 ∧
    Source.chains.escalation.response.gpbTo /
      Source.chains.escalation.response.gpbFrom = 50/101 ∧
    Source.chains.escalation.response.gpbHalveDay = 244 := by
  decide +kernel

/-- Weight percentile improvement recorded by the parent: 7.14 kg (9th percentile,
day 207) to 8.17 kg (26th percentile, day 256). -/
theorem weight_percentile_improvement :
    CPS1Personalized2025.Source.clinical.weights[0]! = 714/100 ∧
    CPS1Personalized2025.Source.clinical.weights[1]! = 817/100 ∧
    CPS1Personalized2025.Source.clinical.weights[1]! -
      CPS1Personalized2025.Source.clinical.weights[0]! = 103/100 := by
  decide +kernel

/-- No hyperammonemic crisis through the two post-dose-2 viral illnesses and the
full-protein diet was maintained through them. -/
theorem illness_stress_test_passed :
    Source.chains.escalation.response.crisisFreeThroughIllnesses = true ∧
    Source.chains.escalation.response.fullProteinThroughIllnesses = true ∧
    Source.chains.proteinLiberalization.response.fullProteinMaintainedThroughIllnesses = true ∧
    Source.chains.proteinLiberalization.measurement.crisisFree = true := by
  decide +kernel

/-- 下一轮能力 (carried-forward capability): the executed maintenance leaves the halved
scavenger state, the post-dose-2 ammonia evidence and the full-protein diet available
to the next round.  These are the recorded values, not promises. -/
theorem capability_carried_forward :
    Source.capability.carriedScavengerDose = 5 ∧
    Source.capability.carriedAmmoniaEvidence = ⟨13,9,28⟩ ∧
    Source.capability.fullProteinDiet = true ∧
    Source.capability.carriedScavengerDose =
      CPS1Personalized2025.Clinical.finalMedication := by
  decide +kernel

/-- The formulation account's exact dose ratio and the residual day-230 weight stay
typed: the ratio is exactly 3, the second nominal mass is `none`. -/
theorem formulation_responses_and_residuals :
    Source.formulation.doseTwoOverDoseOne = 3 ∧
    CPS1Personalized2025.Clinical.second.totalRnaDose /
      CPS1Personalized2025.Clinical.first.totalRnaDose = 3 ∧
    Source.formulation.doseTwoNominalTotalRnaMg = none ∧
    Source.formulation.doseTwoWeightUnmeasured = true ∧
    Source.residuals.day230WeightKg = NoPublicValue.absent ∧
    Source.residuals.proteinGramPerKgPerDayTrajectory = NoPublicValue.absent ∧
    Source.residuals.inPatientLiverEditingFraction = NoPublicValue.absent ∧
    Source.residuals.thirdInfusionApril2025 = NoPublicValue.absent := by
  decide +kernel

/-- Dose-1 nominal total RNA mass: 0.1 mg/kg times the last public pre-dose weight
7.14 kg (day 207) equals 357/500 mg exactly. -/
theorem nominal_dose_one_mass :
    Source.formulation.doseOneNominalTotalRnaMg = 357/500 ∧
    CPS1Personalized2025.Clinical.first.totalRnaDose *
      CPS1Personalized2025.Source.clinical.weights[0]! = 357/500 := by
  decide +kernel

/-- The physical-supply connection names its consumer interface and stays OPEN: this
module never fakes the material/energy/delivery payment. -/
theorem physical_supply_connection_open :
    Source.formulation.supply.deliveryVehicle = "intravenous lipid-nanoparticle infusion" ∧
    Source.formulation.supply.consumerInterface.length > 0 ∧
    Source.formulation.supply.settled = false := by
  decide +kernel

end Response

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal
