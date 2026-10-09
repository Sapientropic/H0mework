import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Supply.Consumers
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery

/-- One actually executed infusion event of the same patient occurrence.  The
nominal total RNA mass is an `Option`: dose 1 carries the parent-paid
357/500 mg; dose 2 stays `none` because the day-230 weight was never
measured — the parent residual is preserved, not filled.  `weightBasisDay`
records which measured weight a nominal mass rests on; dose 2 has none. -/
structure ExecutedDose where
  day : Nat
  doseMgPerKg : ℚ
  nominalTotalRnaMg : Option ℚ
  weightBasisDay : Option Nat
  nominalBasis : String
  infusionEvent : String
  administered : Bool

/-- The two executed doses of the same patient, with the recorded day-count
between them. -/
structure ExecutedDoses where
  doseOne : ExecutedDose
  doseTwo : ExecutedDose
  intervalDays : Nat

/-- Batch-level delivery split: the clinical-batch 97% total mRNA
encapsulation (RiboGreen fluorescence assay) applied to the dose-1 mRNA mass
at the residue-sum level.  The gRNA encapsulation fraction is not public
(typed residual); the split is a batch-level relation and claims no actual
molecule count. -/
structure DeliverySplit where
  mrnaEncapsulationFraction : ℚ
  encapsulatedMrnaMg : ℚ
  unencapsulatedMrnaMg : ℚ
  encapsulatedMrnaResidueSumSubstanceMol : ℚ
  unencapsulatedMrnaResidueSumSubstanceMol : ℚ
  basis : String

/-- The protocol gate, kept strictly separate from the executed record: the
redose-rule conditions, the three-dose maximum, the 21-day minimum interval,
the third-dose options and the planned-only methylprednisone premedication.
Each rule field carries the verbatim quote it was read from. -/
structure ProtocolGate where
  maxTotalDoses : Nat
  minimumIntervalDays : Nat
  conditionA : String
  conditionB : String
  thirdDoseOptionsMgPerKg : List ℚ
  plannedPremedicationMgPerKg : ℚ
  ruleEvidence : String
  maxDosesEvidence : String
  optionsEvidence : String
  premedicationEvidence : String

/-- The post-execution state recorded for the same patient that a next
maintenance round can actually consume: the halved scavenger dose, the
post-dose-2 biochemistry evidence, the maintained full-protein diet, the
crisis-free illness course, the per-dose tolerance evidence and the ongoing
immune management. -/
structure RetainedState where
  carriedScavengerMlPerM2PerDay : ℚ
  postDoseTwoAmmonia : CPS1Personalized2025.Summary
  postDoseTwoOrotic : CPS1Personalized2025.Summary
  fullProteinDietMaintained : Bool
  crisisFreeThroughIllnesses : Bool
  viralIllnessesAfterDoseTwo : Nat
  doseOneWellTolerated : Bool
  doseTwoEventResolved : Bool
  halvingWithoutUnacceptableAdverseEffects : Bool
  immuneMaintenanceOngoing : Bool

/-- The evaluated next-round capability: the protocol gate applied to the
retained state.  `conditionAPreviousTolerated` is computed from the retained
tolerance evidence, `conditionBBiochemicalFeaturesPersist` from the retained
scavenger requirement (the rule's protein-restriction leg is vacated by the
restored full-protein diet; the and/or scavenger leg alone pays it),
`remainingProtocolDoses` is the gate maximum minus the executed count, and
`earliestGateDay` is the dose-2 day plus the minimum interval.  The actual
third dose is press-only and never enters the executed record. -/
structure DoseThreeEligibility where
  conditionAPreviousTolerated : Bool
  conditionBBiochemicalFeaturesPersist : Bool
  executedDoseCount : Nat
  remainingProtocolDoses : Nat
  earliestGateDay : Nat
  optionsMgPerKg : List ℚ
  actualThirdDoseExecuted : Bool

/-- The executed delivery account: the two executed infusions, the batch
delivery split and the protocol gate — actual record and plan stay typed
apart. -/
structure DeliveryAccount where
  executedDoses : ExecutedDoses
  deliverySplit : DeliverySplit
  protocolGate : ProtocolGate

/-- Typed residuals of the delivery step: the public source carries no value
for any of these fields, so the record can only be inhabited by `absent` and
no numeric value can be smuggled in.  No direction or magnitude is claimed
for any of them. -/
structure DeliveryResiduals where
  infusionDurationRateAndVolume : Longitudinal.NoPublicValue
  lnpLipidComponentMasses : Longitudinal.NoPublicValue
  grnaEncapsulationFraction : Longitudinal.NoPublicValue
  physicalInventoryRemaining : Longitudinal.NoPublicValue
  day230WeightKg : Longitudinal.NoPublicValue
  inPatientLiverEditingFraction : Longitudinal.NoPublicValue
  thirdInfusionApril2025 : Longitudinal.NoPublicValue
  deliveryEnergyAccount : Longitudinal.NoPublicValue

/-- 下一轮能力: what the paid delivery carries forward — the retained
post-execution state and the evaluated dose-3 eligibility, together with the
named OPEN consumer interface of the physics/resource chain.  This record
pays the next round's EXECUTION capability against the protocol gate; the
ENERGY account remains an OPEN responsibility (`energyAccountOpen = true`,
the delivery-energy residual stays `absent`). -/
structure DeliveryCapability where
  retained : RetainedState
  eligibility : DoseThreeEligibility
  consumerInterface : String
  energyAccountOpen : Bool

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery
