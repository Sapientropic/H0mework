import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs.Consumers
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal

/-- Reusable same-patient maintenance step: one measurement is judged against a rule,
an adjustment is executed, and a functional response is recorded.  Chains A–D of the
longitudinal packet are four instances of this single relation. -/
structure MaintenanceStep (Measurement Rationale Execution Response : Type) where
  measurement : Measurement
  rationale : Rationale
  execution : Execution
  response : Response

namespace ChainA

structure Measurement where
  doseOneDay : Nat
  doseOneMgPerKg : ℚ
  doseOneWellTolerated : Bool
  interdoseAmmonia : CPS1Personalized2025.Summary
  scavengerStillRequired : Bool
  proteinRestrictionStillRequired : Bool

structure Rationale where
  ruleDay : Nat
  minimumIntervalDays : Nat
  escalatedDoseMgPerKg : ℚ
  conditionA : Bool
  conditionB : Bool

structure Execution where
  day : Nat
  doseMgPerKg : ℚ
  daysAfterDoseOne : Nat
  infusionEvent : String

structure Response where
  gpbHalveDay : Nat
  gpbFrom : ℚ
  gpbTo : ℚ
  postAmmonia : CPS1Personalized2025.Summary
  oroticAfter : CPS1Personalized2025.Summary
  crisisFreeThroughIllnesses : Bool
  fullProteinThroughIllnesses : Bool

end ChainA

namespace ChainB

structure Measurement where
  baseline : ℚ
  attempted : ℚ
  glutamineRising : Bool
  window : List Nat

structure Rationale where
  trigger : String

structure Execution where
  restored : ℚ
  exactDatesUnreported : Bool

structure Response where
  scavengerBackAtFullDose : Bool
  redoseEvaluationContinued : Bool

end ChainB

namespace ChainC

structure Measurement where
  window : List Nat
  intercurrentIllness : String
  crisisFree : Bool

structure Rationale where
  window : List Nat
  discretion : String

structure Execution where
  proteinLiberalized : Bool
  sickDay : Nat
  sickDayManagement : String

structure Response where
  fullProteinMaintainedThroughIllnesses : Bool

end ChainC

namespace ChainD

structure Measurement where
  genotype : String
  baselineRisk : String

structure Rationale where
  steroidSparing : Bool

/-- The actually executed immune-management events: sirolimus from day 205 and
tacrolimus from day 209.  The methylprednisone premedication exists only as
the protocol plan (`ProtocolPlan`); the main text records no actual
methylprednisone administration, so no executed field carries it. -/
structure Execution where
  sirolimusStartDay : Nat
  tacrolimusStartDay : Nat

/-- Protocol-planned premedication, kept apart from the executed record:
one dose of methylprednisone (IV, 1 mg/kg) immediately prior to drug product
infusion on dosing days, per the final protocol.  `planned` marks this as a
plan entry that never enters the executed events. -/
structure ProtocolPlan where
  methylprednisoneIvMgPerKg : ℚ
  methylprednisoneScope : String
  planned : Bool

structure Response where
  bothDosesAdministered : Bool
  chronicCorticosteroids : Bool

end ChainD

/-- The four recorded maintenance chains of the same patient, each an instance of
`MaintenanceStep`. -/
structure LongitudinalMaintenance where
  escalation : MaintenanceStep ChainA.Measurement ChainA.Rationale ChainA.Execution ChainA.Response
  glutamineRestore : MaintenanceStep ChainB.Measurement ChainB.Rationale ChainB.Execution ChainB.Response
  proteinLiberalization : MaintenanceStep ChainC.Measurement ChainC.Rationale ChainC.Execution ChainC.Response
  immuneMaintenance : MaintenanceStep ChainD.Measurement ChainD.Rationale ChainD.Execution ChainD.Response

/-- Explicit marker type: the public source carries no value for this field, so the
record can only be inhabited by `absent` and no numeric value can be smuggled in. -/
inductive NoPublicValue | absent deriving DecidableEq

structure Residuals where
  glutamineTriggerValue : NoPublicValue
  firstTaperDates : NoPublicValue
  proteinGramPerKgPerDayTrajectory : NoPublicValue
  day230WeightKg : NoPublicValue
  inPatientLiverEditingFraction : NoPublicValue
  thirdInfusionApril2025 : NoPublicValue

/-- Typed formulation / material-consumption account.  The parent packets own the
actual molecular words; this account only carries quantities and names. -/
structure PhysicalSupplyConnection where
  deliveryVehicle : String
  consumerInterface : String
  settled : Bool

structure FormulationAccount where
  drugProduct : String
  therapyShortName : String
  guideName : String
  mrnaName : String
  route : String
  doseOneNominalTotalRnaMg : ℚ
  doseTwoNominalTotalRnaMg : Option ℚ
  doseTwoWeightUnmeasured : Bool
  /-- Dose-2 over dose-1 ratio at the mg/kg dose level ONLY (0.3 over 0.1).
  The total-RNA-mass ratio is not payable: dose 2 was 0.3 mg/kg times the
  unmeasured day-230 weight, so no total-mass ratio is ever stated here. -/
  doseTwoOverDoseOne : ℚ
  citrullineMgPerKgPerDay : ℚ
  citrullineUnchanged : Bool
  supply : PhysicalSupplyConnection

/-- Record of the state after execution that is available to the next round:
the reduced scavenger dose (book value 50/101 of the pre-redose dose), the
post-dose-2 ammonia evidence, and the maintained full-protein diet.  This
structure only CARRIES the recorded post-execution state; the actual payment
of the next round's maintenance capability remains an OPEN responsibility
(the physical-supply connection stays `settled = false`). -/
structure NextRoundCapability where
  carriedScavengerDose : ℚ
  carriedAmmoniaEvidence : CPS1Personalized2025.Summary
  fullProteinDiet : Bool

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal
