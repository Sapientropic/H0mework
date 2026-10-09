import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Supply.Reifier

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Supply

namespace Source

/-- Cited public per-residue RNA average masses, scaled to exact integer
micro-Dalton at the packet boundary (printed 0.01 Da granularity times 1e6).
Residue table: Joyner & Cowan, Nucleic Acids Res 2013, Table 1
(https://pmc.ncbi.nlm.nih.gov/articles/PMC3592410/); the same printed averages
appear in the modification table (Pourshahian & McCarthy, Mass Spectrom Rev
2021, Table 2, doi:10.1002/mas.21620).  2'-O-methyl residue masses are the
printed per-base averages from that modification table, so no uniform
modification delta is ever applied to a base it was not printed for. -/
def residueAUd : ℚ := cps1SupplyRat% "constants" "residues_ud" "rA"
def residueCUd : ℚ := cps1SupplyRat% "constants" "residues_ud" "rC"
def residueGUd : ℚ := cps1SupplyRat% "constants" "residues_ud" "rG"
def residueUUd : ℚ := cps1SupplyRat% "constants" "residues_ud" "rU"
def omethylAUd : ℚ := cps1SupplyRat% "constants" "twoprime_omethyl_ud" "A"
def omethylCUd : ℚ := cps1SupplyRat% "constants" "twoprime_omethyl_ud" "C"
def omethylGUd : ℚ := cps1SupplyRat% "constants" "twoprime_omethyl_ud" "G"
def omethylUUd : ℚ := cps1SupplyRat% "constants" "twoprime_omethyl_ud" "U"
def methylationDeltaUd : ℚ := cps1SupplyRat% "constants" "methylation_delta_ud"
def phosphorothioateDeltaUd : ℚ := cps1SupplyRat% "constants" "phosphorothioate_delta_ud"
/-- N1-methylpseudouridine residue: pseudouridine is isomeric with uridine, so
the printed methylation delta (+14.03 Da average) is added to the printed
uridine residue. -/
def m1psiResidueUd : ℚ := cps1SupplyRat% "constants" "m1psi_residue_ud"
/-- Avogadro constant, exact SI defining constant (BIPM SI Brochure, 9th ed.):
6.02214076 x 10^23 mol^-1. -/
def avogadroPerMol : ℚ :=
  (cps1SupplyRat% "constants" "avogadro") * 10 ^ (cps1SupplyNat% "constants" "avogadro_exponent")
def moleculeScale : ℕ := cps1SupplyNat% "constants" "molecule_scale"

/-- Composition counts computed from the parent molecular words, never
re-entered by hand: lowercase residues are 2'-O-methyl (`ribose2OMethyl`),
`s` entries in `sulfurAfter` are phosphorothioate linkage positions. -/
def residueCount (rna : RegisteredRna) (n : Nucleoside) (methylated : Bool) : ℕ :=
  (rna.residues.filter (fun r => r.nucleoside == n && r.ribose2OMethyl == methylated)).length

def guidePlainA : ℕ := residueCount Molecules.guide .adenosine false
def guidePlainC : ℕ := residueCount Molecules.guide .cytidine false
def guidePlainG : ℕ := residueCount Molecules.guide .guanosine false
def guidePlainU : ℕ := residueCount Molecules.guide .uridine false
def guideMethylA : ℕ := residueCount Molecules.guide .adenosine true
def guideMethylC : ℕ := residueCount Molecules.guide .cytidine true
def guideMethylG : ℕ := residueCount Molecules.guide .guanosine true
def guideMethylU : ℕ := residueCount Molecules.guide .uridine true
def guidePs : ℕ := Molecules.guide.sulfurAfter.length

def mrnaPlainA : ℕ := residueCount Molecules.mrna .adenosine false
def mrnaPlainC : ℕ := residueCount Molecules.mrna .cytidine false
def mrnaPlainG : ℕ := residueCount Molecules.mrna .guanosine false
def mrnaPlainU : ℕ := residueCount Molecules.mrna .uridine false
def mrnaPsi : ℕ := residueCount Molecules.mrna .n1Methylpseudouridine false

/-- Exact residue-sum molar masses: count-then-multiply over the cited table,
scaled in integer micro-Dalton.  These are residue-sum values; mRNA carries a
5' Cap-1 and a 3' poly(A) tail of strictly positive but unnumered mass, and
the gRNA end-group chemistry has no public direction. -/
def guideResidueSumUd : ℚ :=
  guidePlainA * residueAUd + guidePlainC * residueCUd + guidePlainG * residueGUd +
  guidePlainU * residueUUd + guideMethylA * omethylAUd + guideMethylC * omethylCUd +
  guideMethylG * omethylGUd + guideMethylU * omethylUUd + guidePs * phosphorothioateDeltaUd

def mrnaResidueSumUd : ℚ :=
  mrnaPlainA * residueAUd + mrnaPlainC * residueCUd + mrnaPlainG * residueGUd +
  mrnaPlainU * residueUUd + mrnaPsi * m1psiResidueUd

/-- g/mol equals Da numerically; µDa scaled down by 10^6. -/
def guideResidueSumGPerMol : ℚ := guideResidueSumUd / 10 ^ 6
def mrnaResidueSumGPerMol : ℚ := mrnaResidueSumUd / 10 ^ 6

/-- Formulation values consumed from the parent material account, never
retyped: dose-1 nominal total RNA mass, the mg/kg-level dose-2/dose-1 ratio,
the citrulline rate and the last public pre-dose weight all come from the
Longitudinal module (itself reified from the parent packets). -/
def doseOneNominalTotalRnaMg : ℚ := Longitudinal.Source.formulation.doseOneNominalTotalRnaMg
/-- mg/kg-level ratio ONLY (0.3 over 0.1); the total-RNA-mass ratio is not
payable because the day-230 weight was unmeasured. -/
def doseTwoOverDoseOne : ℚ := Longitudinal.Source.formulation.doseTwoOverDoseOne
def citrullineMgPerKgPerDay : ℚ := Longitudinal.Source.formulation.citrullineMgPerKgPerDay
def preDoseWeightKg : ℚ := CPS1Personalized2025.Source.clinical.weights[0]!

/-- The public gRNA:mRNA ratio in its three forms, each with its quoted
evidence: protocol target 1:1 (page 16), preparation 1:1 (Methods page 46),
clinical-batch measured 1.1 by UPLC (Methods page 46). -/
def massRatio : MassRatio where
  target := cps1SupplyRat% "mass_ratio" "target"
  preparation := cps1SupplyRat% "mass_ratio" "preparation"
  measuredBatch := cps1SupplyRat% "mass_ratio" "measured"
  targetEvidence := cps1SupplyQuote% "q_ratio_target"
  preparationEvidence := cps1SupplyQuote% "q_ratio_preparation"
  measuredEvidence := cps1SupplyQuote% "q_batch_measured"

/-- Clinical-batch characterization with assay names (Methods page 46). -/
def clinicalBatch : ClinicalBatch where
  hydrodynamicDiameterNm := cps1SupplyRat% "clinical_batch" "hydrodynamic_diameter_nm"
  polydispersityIndex := cps1SupplyRat% "clinical_batch" "polydispersity_index"
  mrnaEncapsulationFraction := cps1SupplyRat% "clinical_batch" "mrna_encapsulation_fraction"
  diameterAssay := cps1SupplyText% "clinical_batch" "diameter_assay"
  pdiAssay := cps1SupplyText% "clinical_batch" "pdi_assay"
  encapsulationAssay := cps1SupplyText% "clinical_batch" "encapsulation_assay"

/-- Dose-1 per-species masses via the measured batch ratio (gRNA 11/21,
mRNA 10/21). -/
def doseOneGrnaMg : ℚ := doseOneNominalTotalRnaMg * (massRatio.measuredBatch / (1 + massRatio.measuredBatch))
def doseOneMrnaMg : ℚ := doseOneNominalTotalRnaMg * (1 / (1 + massRatio.measuredBatch))
def grnaMassG : ℚ := doseOneGrnaMg / 10 ^ 3
def mrnaMassG : ℚ := doseOneMrnaMg / 10 ^ 3

/-- Exact per-species amounts of substance at the residue-sum level. -/
def grnaResidueSumSubstanceMol : ℚ := grnaMassG / guideResidueSumGPerMol
def mrnaResidueSumSubstanceMol : ℚ := mrnaMassG / mrnaResidueSumGPerMol
/-- Exact molecule count at the mRNA residue-sum level; the ACTUAL count is
strictly below (positive Cap-1 and poly(A) contributions). -/
def mrnaResidueSumMolecules : ℚ := mrnaResidueSumSubstanceMol * avogadroPerMol
def mrnaMoleculesUpperScaled : ℕ := 13

def citrullineMgPerDay : ℚ := citrullineMgPerKgPerDay * preDoseWeightKg
/-- (357/500 mg) / (7140 g) as an exact rational, mg over mg. -/
def rnaBodyMassFraction : ℚ := doseOneNominalTotalRnaMg / (preDoseWeightKg * 10 ^ 6)

def account : SupplyAccount where
  guideResidueSumGPerMol := guideResidueSumGPerMol
  mrnaResidueSumGPerMol := mrnaResidueSumGPerMol
  massRatio := massRatio
  clinicalBatch := clinicalBatch
  doseOneNominalTotalRnaMg := doseOneNominalTotalRnaMg
  doseOneGrnaMg := doseOneGrnaMg
  doseOneMrnaMg := doseOneMrnaMg
  grnaResidueSumSubstanceMol := grnaResidueSumSubstanceMol
  mrnaResidueSumSubstanceMol := mrnaResidueSumSubstanceMol
  mrnaResidueSumMolecules := mrnaResidueSumMolecules
  moleculeScale := moleculeScale
  mrnaMoleculesUpperScaled := mrnaMoleculesUpperScaled
  citrullineMgPerDay := citrullineMgPerDay
  rnaBodyMassFraction := rnaBodyMassFraction

/-- The material ledger is paid, the energy account stays OPEN: the consumer
interface names the physical/resource chain (LAlanine40K2025
feedback-resources resource ledger) that can consume the paid ledger next. -/
def physicalDelivery : PhysicalDelivery where
  deliveryVehicle := cps1SupplyText% "physical_delivery" "delivery_vehicle"
  consumerInterface := cps1SupplyText% "physical_delivery" "consumer_interface"
  settled := false
  energyAccountSettled := false
  energyAccount := .absent

/-- Explicit residuals (D2): the Cap-1 mass and the poly(A) tail length have
no public numbers; the actual mRNA moles therefore have no payable positive
lower bound; the gRNA end-group adjustment has no public direction.  No
magnitude or direction is claimed anywhere. -/
def supplyResiduals : SupplyResiduals where
  mrnaCapMass := .absent
  polyATailLength := .absent
  mrnaActualMolesLowerBound := .absent
  grnaEndGroupAdjustment := .absent
  infusionDurationRateAndVolume := .absent
  lnpLipidComponentMasses := .absent

def capability : SupplyCapability where
  paidGrnaResidueSumSubstanceMol := grnaResidueSumSubstanceMol
  paidMrnaResidueSumSubstanceMol := mrnaResidueSumSubstanceMol
  paidMrnaMoleculesUpperScaled := mrnaMoleculesUpperScaled
  consumerInterface := physicalDelivery.consumerInterface
  energyAccountOpen := true

def parentPacketSha : String := cps1SupplyText% "parent_packet_sha256"
def grandparentPacketSha : String := cps1SupplyText% "grandparent_packet_sha256"
def pdfSha : String := cps1SupplyText% "pdf_sha256"
def clinicalReference : String := cps1SupplyText% "clinical_reference"
def sourceVersion : String := cps1SupplyText% "source_version"

def quoteResidueTable : String := cps1SupplyQuote% "q_residue_table"
def quoteModResidues : String := cps1SupplyQuote% "q_mod_residues"
def quoteMod2ome : String := cps1SupplyQuote% "q_mod_2ome"
def quoteModMethylation : String := cps1SupplyQuote% "q_mod_methylation"
def quoteModPs : String := cps1SupplyQuote% "q_mod_ps"
def quoteAvogadro : String := cps1SupplyQuote% "q_avogadro"
def quoteRatioTarget : String := cps1SupplyQuote% "q_ratio_target"
def quoteRatioPreparation : String := cps1SupplyQuote% "q_ratio_preparation"
def quoteBatchMeasured : String := cps1SupplyQuote% "q_batch_measured"
def quoteCapPolya : String := cps1SupplyQuote% "q_cap_polya"
def quoteCap1 : String := cps1SupplyQuote% "q_cap1"
def quoteTableS2 : String := cps1SupplyQuote% "q_table_s2"

/-- The computed composition equals both the packet's independently computed
cross-check metadata and the parent module's published chemical inventory
(100 nt = 53 plain + 47 2'-O-methyl, six phosphorothioate linkages after
positions 1/2/3/97/98/99; 5113 nt with 782 N1-methylpseudouridines, no
2'-O-methyl, no phosphorothioate). -/
theorem complete_composition :
    guidePlainA = 20 ∧ guidePlainC = 6 ∧ guidePlainG = 10 ∧ guidePlainU = 17 ∧
    guideMethylA = 14 ∧ guideMethylC = 8 ∧ guideMethylG = 13 ∧ guideMethylU = 12 ∧
    guidePs = 6 ∧
    mrnaPlainA = 1192 ∧ mrnaPlainC = 1746 ∧ mrnaPlainG = 1393 ∧ mrnaPlainU = 0 ∧
    mrnaPsi = 782 ∧
    Molecules.guide.residues.length = 100 ∧
    Rna.methylCount Molecules.guide = 47 ∧
    Molecules.guide.residues.length - Rna.methylCount Molecules.guide = 53 ∧
    Molecules.guide.sulfurAfter = [1,2,3,97,98,99] ∧
    Molecules.mrna.residues.length = 5113 ∧
    Rna.pseudoCount Molecules.mrna = 782 ∧
    Rna.methylCount Molecules.mrna = 0 ∧
    Molecules.mrna.sulfurAfter = [] := by
  decide +kernel

theorem complete_inventory :
    guideResidueSumUd = 33040000000 ∧
    mrnaResidueSumUd = 1656536530000 ∧
    guideResidueSumGPerMol = 33040 ∧
    mrnaResidueSumGPerMol = 165653653/100 ∧
    doseOneNominalTotalRnaMg = 357/500 ∧
    doseTwoOverDoseOne = 3 ∧
    citrullineMgPerKgPerDay = 200 ∧
    preDoseWeightKg = 714/100 ∧
    massRatio.target = 1 ∧
    massRatio.preparation = 1 ∧
    massRatio.measuredBatch = 11/10 ∧
    clinicalBatch.hydrodynamicDiameterNm = 73 ∧
    clinicalBatch.polydispersityIndex = 7/100 ∧
    clinicalBatch.mrnaEncapsulationFraction = 97/100 ∧
    doseOneGrnaMg = 187/500 ∧
    doseOneMrnaMg = 17/50 ∧
    doseOneGrnaMg + doseOneMrnaMg = 357/500 ∧
    grnaResidueSumSubstanceMol = 187/16520000000 ∧
    mrnaResidueSumSubstanceMol = 17/82826826500 ∧
    mrnaResidueSumMolecules = 20475278584000000000000/165653653 ∧
    moleculeScale = 10000000000000 ∧
    mrnaMoleculesUpperScaled = 13 ∧
    citrullineMgPerDay = 1428 ∧
    rnaBodyMassFraction = 1/10000000 ∧
    Longitudinal.Source.formulation.supply.settled = false ∧
    physicalDelivery.settled = false ∧
    physicalDelivery.energyAccountSettled = false ∧
    capability.energyAccountOpen = true := by
  decide +kernel

theorem residuals_complete :
    supplyResiduals.mrnaCapMass = Longitudinal.NoPublicValue.absent ∧
    supplyResiduals.polyATailLength = Longitudinal.NoPublicValue.absent ∧
    supplyResiduals.mrnaActualMolesLowerBound = Longitudinal.NoPublicValue.absent ∧
    supplyResiduals.grnaEndGroupAdjustment = Longitudinal.NoPublicValue.absent ∧
    supplyResiduals.infusionDurationRateAndVolume = Longitudinal.NoPublicValue.absent ∧
    supplyResiduals.lnpLipidComponentMasses = Longitudinal.NoPublicValue.absent ∧
    physicalDelivery.energyAccount = Longitudinal.NoPublicValue.absent := by
  decide +kernel

theorem same_source_identity :
    parentPacketSha = Longitudinal.Reifier.packetSha ∧
    grandparentPacketSha = CPS1Personalized2025.Reifier.packetSha256 ∧
    pdfSha = CPS1Personalized2025.Source.sourcePdfSha ∧
    clinicalReference = CPS1Personalized2025.Source.clinical.patient ∧
    sourceVersion =
      "NEJM 392;22 (June 12, 2025) main text pages 2237-2241; protocol final version 2025-03-11, FDA IND 31438" := by
  decide +kernel

theorem parent_values_used_not_rewritten :
    doseOneNominalTotalRnaMg =
      CPS1Personalized2025.Clinical.first.totalRnaDose * CPS1Personalized2025.Source.clinical.weights[0]! ∧
    doseOneNominalTotalRnaMg = Longitudinal.Source.formulation.doseOneNominalTotalRnaMg ∧
    doseTwoOverDoseOne = Longitudinal.Source.formulation.doseTwoOverDoseOne ∧
    citrullineMgPerKgPerDay = Longitudinal.Source.formulation.citrullineMgPerKgPerDay ∧
    preDoseWeightKg = CPS1Personalized2025.Source.clinical.weights[0]! := by
  decide +kernel

/-- Cross-check against the packet's independently computed metadata: the
masses, the molecule upper report and the citrulline rate computed here from
the parent words and the cited constants equal the values recorded by
prepare.py. -/
theorem packet_crosscheck :
    (cps1SupplyNat% "computed" "molecule_scaled_upper") = 13 ∧
    (cps1SupplyRat% "computed" "guide_residue_sum_ud") = guideResidueSumUd ∧
    (cps1SupplyRat% "computed" "mrna_residue_sum_ud") = mrnaResidueSumUd ∧
    (cps1SupplyRat% "computed" "citrulline_mg_per_day") = citrullineMgPerDay := by
  decide +kernel

theorem quotes_present :
    quoteResidueTable.length > 0 ∧ quoteModResidues.length > 0 ∧
    quoteMod2ome.length > 0 ∧ quoteModMethylation.length > 0 ∧
    quoteModPs.length > 0 ∧ quoteAvogadro.length > 0 ∧
    quoteRatioTarget.length > 0 ∧ quoteRatioPreparation.length > 0 ∧
    quoteBatchMeasured.length > 0 ∧ quoteCapPolya.length > 0 ∧
    quoteCap1.length > 0 ∧ quoteTableS2.length > 0 := by
  decide +kernel

end Source

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Supply
