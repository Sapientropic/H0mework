import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal.Source

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal

namespace Feedback

/-- The protocol Day-22 escalated redose rule is satisfied by the recorded measurements:
condition (a) the initial dose was safe and well tolerated, and condition (b) the patient
still demonstrated biochemical features of CPS1 deficiency requiring a protein-restricted
diet and/or ammonia scavengers (the inter-dose ammonia summary is the recorded
measurement; the continued glycerol phenylbutyrate requirement is the recorded support). -/
theorem recorded_measurements_satisfy_day22_escalation_rule :
    Source.chains.escalation.measurement.doseOneWellTolerated = true ∧
    Source.chains.escalation.measurement.scavengerStillRequired = true ∧
    Source.chains.escalation.measurement.proteinRestrictionStillRequired = true ∧
    Source.chains.escalation.measurement.interdoseAmmonia = ⟨9,9,19⟩ ∧
    Source.chains.escalation.rationale.ruleDay = 22 ∧
    Source.chains.escalation.rationale.conditionA = true ∧
    Source.chains.escalation.rationale.conditionB = true := by
  decide +kernel

/-- The executed escalation respected the protocol minimum of 21 days between doses. -/
theorem redose_respects_minimum_interval :
    Source.chains.escalation.rationale.minimumIntervalDays = 21 ∧
    Source.chains.escalation.rationale.minimumIntervalDays ≤
      Source.chains.escalation.execution.daysAfterDoseOne ∧
    Source.chains.escalation.execution.daysAfterDoseOne =
      Source.chains.escalation.execution.day - Source.chains.escalation.measurement.doseOneDay := by
  decide +kernel

/-- Chain B is rule-governed as well: the restore was triggered by a recorded rising
glutamine level, and the exact dates stay an explicit residual (never invented). -/
theorem glutamine_restore_trigger_recorded :
    Source.chains.glutamineRestore.measurement.glutamineRising = true ∧
    Source.chains.glutamineRestore.execution.exactDatesUnreported = true ∧
    Source.residuals.glutamineTriggerValue = NoPublicValue.absent ∧
    Source.residuals.firstTaperDates = NoPublicValue.absent := by
  decide +kernel

/-- Chain C: the protein-liberalization window matches the quoted protocol Days 7–21
window and the sick-day exception lies inside the recorded inter-dose window. -/
theorem liberalization_window_and_sick_day :
    Source.chains.proteinLiberalization.rationale.window = [7,21] ∧
    Source.chains.proteinLiberalization.measurement.window = [208,230] ∧
    Source.chains.proteinLiberalization.measurement.window.head? = some 208 ∧
    Source.chains.proteinLiberalization.measurement.window.getLast? = some 230 ∧
    208 < Source.chains.proteinLiberalization.execution.sickDay ∧
    Source.chains.proteinLiberalization.execution.sickDay < 230 := by
  decide +kernel

/-- Chain D rationale: the steroid-sparing choice is recorded and no chronic
corticosteroid maintenance was used. -/
theorem steroid_sparing_rule_recorded :
    Source.chains.immuneMaintenance.rationale.steroidSparing = true ∧
    Source.chains.immuneMaintenance.response.chronicCorticosteroids = false := by
  decide +kernel

/-- The quoted spans are non-empty and come from the guarded packet. -/
theorem quotes_present :
    Source.quoteEscalation.length > 0 ∧ Source.quoteRedoseRule.length > 0 ∧
    Source.quoteHalve.length > 0 ∧ Source.quoteGlutamineRestore.length > 0 ∧
    Source.quoteSickDay.length > 0 ∧ Source.quoteWindow721.length > 0 ∧
    Source.quoteSteroidSparing.length > 0 ∧ Source.quoteMethylpred.length > 0 ∧
    Source.quoteCitrulline.length > 0 := by
  decide +kernel

end Feedback

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal
