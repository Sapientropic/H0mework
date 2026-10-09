import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal.Feedback

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal

namespace Execution

/-- The executed events with their recorded days and doses.  Chain D's executed
record carries only the sirolimus/tacrolimus start days: the main text records
no actual methylprednisone administration, so no executed entry mentions it. -/
theorem executed_events :
    Source.chains.escalation.execution.day = 230 ∧
    Source.chains.escalation.execution.doseMgPerKg = 3/10 ∧
    Source.chains.escalation.execution.daysAfterDoseOne = 22 ∧
    Source.chains.escalation.response.gpbHalveDay = 244 ∧
    Source.chains.escalation.response.gpbFrom = 101/10 ∧
    Source.chains.escalation.response.gpbTo = 5 ∧
    Source.chains.glutamineRestore.execution.restored = 101/10 ∧
    Source.chains.proteinLiberalization.execution.proteinLiberalized = true ∧
    Source.chains.proteinLiberalization.execution.sickDay = 225 ∧
    Source.chains.immuneMaintenance.execution.sirolimusStartDay = 205 ∧
    Source.chains.immuneMaintenance.execution.tacrolimusStartDay = 209 := by
  decide +kernel

/-- Plan/execution separation for chain D (counterexample shape): the executed
chain-D record is exactly the two start days — it has no methylprednisone
field at all — while the methylprednisone premedication exists only in the
protocol plan, marked `planned`. -/
theorem plan_not_executed :
    Source.chains.immuneMaintenance.execution = ⟨205,209⟩ ∧
    Source.immunePlan.methylprednisoneIvMgPerKg = 1 ∧
    Source.immunePlan.planned = true ∧
    Source.immunePlan.methylprednisoneScope.length > 0 := by
  refine ⟨rfl,?_,?_,?_⟩ <;> decide +kernel

/-- Total order of every recorded maintenance event on the postnatal-day clock. -/
theorem event_order :
    Source.chains.immuneMaintenance.execution.sirolimusStartDay <
      Source.chains.escalation.measurement.doseOneDay ∧
    Source.chains.escalation.measurement.doseOneDay <
      Source.chains.immuneMaintenance.execution.tacrolimusStartDay ∧
    Source.chains.immuneMaintenance.execution.tacrolimusStartDay <
      Source.chains.proteinLiberalization.execution.sickDay ∧
    Source.chains.proteinLiberalization.execution.sickDay <
      Source.chains.escalation.execution.day ∧
    Source.chains.escalation.execution.day <
      Source.chains.escalation.response.gpbHalveDay ∧
    Source.chains.escalation.response.gpbHalveDay <
      CPS1Personalized2025.Clinical.followupDay := by
  decide +kernel

/-- The day-244 halve is exactly 14 days after the second infusion and 26 days before
the recorded day-256 follow-up weight. -/
theorem halve_day_arithmetic :
    Source.chains.escalation.response.gpbHalveDay =
      Source.chains.escalation.execution.day + 14 ∧
    CPS1Personalized2025.Clinical.followupDay =
      Source.chains.escalation.execution.day + 26 ∧
    Source.chains.escalation.response.gpbHalveDay + 12 =
      CPS1Personalized2025.Clinical.followupDay := by
  decide +kernel

/-- The glutamine-triggered restore lands exactly on the parent's recorded third taper
entry; the parent owns the taper words and this module only consumes them. -/
theorem restore_matches_parent_first_taper :
    Source.chains.glutamineRestore.execution.restored =
      CPS1Personalized2025.Clinical.firstAttempt[2]! ∧
    Source.chains.glutamineRestore.measurement.baseline =
      CPS1Personalized2025.Clinical.firstAttempt[0]! ∧
    Source.chains.glutamineRestore.measurement.attempted =
      CPS1Personalized2025.Clinical.firstAttempt[1]! := by
  decide +kernel

/-- Both infusions were actually administered: the executed dose-2 chain and the parent's
recorded two-infusion ledger agree. -/
theorem both_infusions_executed :
    Source.chains.immuneMaintenance.response.bothDosesAdministered = true ∧
    CPS1Personalized2025.Clinical.doses.length = 2 ∧
    CPS1Personalized2025.Clinical.second.day = Source.chains.escalation.execution.day := by
  decide +kernel

end Execution

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal
