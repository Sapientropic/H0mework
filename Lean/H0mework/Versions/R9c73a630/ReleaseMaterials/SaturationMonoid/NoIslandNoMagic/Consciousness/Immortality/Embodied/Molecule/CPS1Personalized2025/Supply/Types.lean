import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal.Consumers
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Supply

/-- Public gRNA:mRNA mass ratio record, in three distinct forms (D1): the
protocol TARGET ratio, the MANUFACTURING preparation ratio, and the
clinical-batch MEASURED ratio with its assay.  The dose-1 mass allocation
uses the measured batch ratio (gRNA share 11/21, mRNA share 10/21).  Each
form carries the verbatim quoted evidence it was read from. -/
structure MassRatio where
  target : ℚ
  preparation : ℚ
  measuredBatch : ℚ
  targetEvidence : String
  preparationEvidence : String
  measuredEvidence : String

/-- Clinical-batch characterization of the drug product, with assay names. -/
structure ClinicalBatch where
  hydrodynamicDiameterNm : ℚ
  polydispersityIndex : ℚ
  mrnaEncapsulationFraction : ℚ
  diameterAssay : String
  pdiAssay : String
  encapsulationAssay : String

/-- Explicit supply-side residuals: the public source carries no value for any
of these fields, so the record can only be inhabited by `absent` and no
numeric value can be smuggled in.  The marker type is the parent's
`Longitudinal.NoPublicValue`, keeping one uninhabitable-marker discipline.
No direction or magnitude is claimed for any of them (D2). -/
structure SupplyResiduals where
  mrnaCapMass : Longitudinal.NoPublicValue
  polyATailLength : Longitudinal.NoPublicValue
  mrnaActualMolesLowerBound : Longitudinal.NoPublicValue
  grnaEndGroupAdjustment : Longitudinal.NoPublicValue
  infusionDurationRateAndVolume : Longitudinal.NoPublicValue
  lnpLipidComponentMasses : Longitudinal.NoPublicValue

/-- The delivery/energy account.  The per-species substance ledger is paid by
this module; the ENERGY account remains an OPEN connection responsibility:
`settled` and `energyAccountSettled` stay `false` and the energy account
field is the uninhabitable marker, while `consumerInterface` names the
physical/resource consumer that can directly consume the paid ledger next
(the LAlanine40K2025 feedback-resources chain). -/
structure PhysicalDelivery where
  deliveryVehicle : String
  consumerInterface : String
  settled : Bool
  energyAccountSettled : Bool
  energyAccount : Longitudinal.NoPublicValue

/-- Typed physical-supply account.  Molar masses are exact residue-sum values
in g/mol (numerically equal to Da).  Per-species masses use the measured
batch ratio; `grnaResidueSumSubstanceMol` / `mrnaResidueSumSubstanceMol` are
the exact per-species amounts of substance at the residue-sum level;
`mrnaResidueSumMolecules` is the exact molecule count at that level and
`mrnaMoleculesUpperScaled` reports its directed-rounded upper report in
units of 10^13 molecules.  Because the mRNA's 5' Cap-1 and 3' poly(A) tail
exist with strictly positive (unnumered) mass, the ACTUAL mRNA amount of
substance is strictly BELOW `mrnaResidueSumSubstanceMol` (see
`Substance.actual_mrna_moles_upper`); no positive lower bound is payable. -/
structure SupplyAccount where
  guideResidueSumGPerMol : ℚ
  mrnaResidueSumGPerMol : ℚ
  massRatio : MassRatio
  clinicalBatch : ClinicalBatch
  doseOneNominalTotalRnaMg : ℚ
  doseOneGrnaMg : ℚ
  doseOneMrnaMg : ℚ
  grnaResidueSumSubstanceMol : ℚ
  mrnaResidueSumSubstanceMol : ℚ
  mrnaResidueSumMolecules : ℚ
  moleculeScale : ℕ
  mrnaMoleculesUpperScaled : ℕ
  citrullineMgPerDay : ℚ
  rnaBodyMassFraction : ℚ

/-- 下一轮能力: what the paid physical supply carries forward — the
per-species residue-sum substance ledger, the mRNA molecule upper report and
the named OPEN consumer interface of the physics/resource chain.  This record
only CARRIES the computed ledger and the named interface; the actual payment
of the next round's capability (in particular the ENERGY account) remains an
OPEN responsibility. -/
structure SupplyCapability where
  paidGrnaResidueSumSubstanceMol : ℚ
  paidMrnaResidueSumSubstanceMol : ℚ
  paidMrnaMoleculesUpperScaled : ℕ
  consumerInterface : String
  energyAccountOpen : Bool

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Supply
