import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Supply.Mass
import Mathlib

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Supply

namespace Substance

/-- Per-species allocation by the clinical-batch measured ratio: gRNA
187/500 mg, mRNA 17/50 mg, summing exactly to the dose-1 nominal total
357/500 mg. -/
theorem per_species_allocation :
    Source.doseOneGrnaMg = 187/500 ∧
    Source.doseOneMrnaMg = 17/50 ∧
    Source.doseOneGrnaMg + Source.doseOneMrnaMg = Source.doseOneNominalTotalRnaMg ∧
    Source.doseOneNominalTotalRnaMg = 357/500 := by
  decide +kernel

/-- The three public ratio forms, each with its evidence: target 1:1,
preparation 1:1, clinical-batch measured 1.1 (UPLC). -/
theorem mass_ratio_recorded :
    Source.massRatio.target = 1 ∧
    Source.massRatio.preparation = 1 ∧
    Source.massRatio.measuredBatch = 11/10 ∧
    Source.massRatio.targetEvidence.length > 0 ∧
    Source.massRatio.preparationEvidence.length > 0 ∧
    Source.massRatio.measuredEvidence.length > 0 := by
  decide +kernel

/-- D2 strict upper bound: the mRNA drug substance comprises the 5' cap and
the 3' polyadenylate tail (quoted existence), whose masses are strictly
positive but carry no public numbers.  For ANY strictly positive cap and
poly(A) contributions, the actual mRNA amount of substance is strictly
smaller than the residue-sum value: a larger denominator with a fixed
positive numerator gives a smaller quotient.  No numeric value or bound is
assumed for either contribution. -/
theorem actual_mrna_moles_upper (capContribution polyAContribution : ℚ)
    (capPositive : 0 < capContribution) (polyAPositive : 0 < polyAContribution) :
    Source.mrnaMassG / (Source.mrnaResidueSumGPerMol + capContribution + polyAContribution) <
      Source.mrnaResidueSumSubstanceMol := by
  have hM : Source.mrnaMassG = 17/50000 := by decide +kernel
  have hR : Source.mrnaResidueSumGPerMol = 165653653/100 := by decide +kernel
  have hS : Source.mrnaResidueSumSubstanceMol = 17/82826826500 := by decide +kernel
  rw [hM, hR, hS]
  have hd : (0:ℚ) < 82826826500 := by norm_num
  have hs : (0:ℚ) < 165653653/100 + capContribution + polyAContribution := by linarith
  refine (div_lt_div_iff₀ (a := (17/50000 : ℚ))
    (b := (165653653/100 + capContribution + polyAContribution))
    (c := (17 : ℚ)) (d := (82826826500 : ℚ)) hs hd).mpr ?_
  have key : (17/50000 : ℚ) * 82826826500 = 17 * (165653653/100) := by norm_num
  rw [key]
  have h1 : (165653653/100 : ℚ) < 165653653/100 + capContribution :=
    lt_add_of_pos_right _ capPositive
  have h2 : (165653653/100 : ℚ) + capContribution <
      165653653/100 + capContribution + polyAContribution :=
    lt_add_of_pos_right _ polyAPositive
  exact mul_lt_mul_of_pos_left (lt_trans h1 h2) (by norm_num)

/-- Exact per-species residue-sum substance values. -/
theorem residue_sum_substances :
    Source.grnaResidueSumSubstanceMol = 187/16520000000 ∧
    Source.mrnaResidueSumSubstanceMol = 17/82826826500 := by
  decide +kernel

/-- Molecule level: the exact residue-sum mRNA molecule count and its
units-of-10^13 directed-rounded upper report 13; the ACTUAL count is strictly
below (positive Cap-1 and poly(A) contributions). -/
theorem residue_sum_molecules :
    Source.mrnaResidueSumMolecules = 20475278584000000000000/165653653 ∧
    Source.mrnaResidueSumMolecules ≤ 13 * 10 ^ 13 ∧
    Source.moleculeScale = 10000000000000 ∧
    Source.mrnaMoleculesUpperScaled = 13 := by
  decide +kernel

/-- Combined actual bound: for any strictly positive cap and poly(A)
contributions, the actual mRNA molecule count is strictly below
13 x 10^13. -/
theorem actual_mrna_molecules_upper (capContribution polyAContribution : ℚ)
    (capPositive : 0 < capContribution) (polyAPositive : 0 < polyAContribution) :
    (Source.mrnaMassG / (Source.mrnaResidueSumGPerMol + capContribution + polyAContribution)) *
      Source.avogadroPerMol < 13 * 10 ^ 13 := by
  have h1 := actual_mrna_moles_upper capContribution polyAContribution capPositive polyAPositive
  have hna : (0:ℚ) < Source.avogadroPerMol := by
    have h : Source.avogadroPerMol = 602214076 * 10 ^ 15 := by decide +kernel
    rw [h]; norm_num
  have h2 := mul_lt_mul_of_pos_right h1 hna
  have h3 : Source.mrnaResidueSumSubstanceMol * Source.avogadroPerMol ≤ 13 * 10 ^ 13 := by
    decide +kernel
  exact lt_of_lt_of_le h2 h3

/-- Clinical-batch characterization with assays: 73 nm and PDI 0.07 by
dynamic light scattering, 97% total mRNA encapsulation by the RiboGreen
fluorescence assay. -/
theorem batch_characterization :
    Source.clinicalBatch.hydrodynamicDiameterNm = 73 ∧
    Source.clinicalBatch.polydispersityIndex = 7/100 ∧
    Source.clinicalBatch.mrnaEncapsulationFraction = 97/100 ∧
    Source.clinicalBatch.diameterAssay.length > 0 ∧
    Source.clinicalBatch.pdiAssay.length > 0 ∧
    Source.clinicalBatch.encapsulationAssay.length > 0 := by
  decide +kernel

/-- Citrulline support-therapy mass rate: 200 mg/kg/day times the last public
pre-dose weight 714/100 kg (day 207; the period over which this weight applies
is a typed residual inherited from the parent) equals 1428 mg/day exactly. -/
theorem citrulline_support_rate :
    Source.citrullineMgPerDay = 1428 ∧
    Source.citrullineMgPerKgPerDay * Source.preDoseWeightKg = 1428 := by
  decide +kernel

/-- Dose-2 over dose-1 is exactly 3 at the mg/kg dose level ONLY (0.3 over
0.1); the total-RNA-mass ratio is never stated because the day-230 weight was
unmeasured — the parent residual is preserved, not filled. -/
theorem dose_two_relation :
    Source.doseTwoOverDoseOne = 3 ∧
    CPS1Personalized2025.Clinical.second.totalRnaDose /
      CPS1Personalized2025.Clinical.first.totalRnaDose = 3 ∧
    Longitudinal.Source.formulation.doseTwoNominalTotalRnaMg = none ∧
    Longitudinal.Source.formulation.doseTwoWeightUnmeasured = true := by
  decide +kernel

/-- Dose-1 RNA over body-mass fraction: (357/500 mg) / (7140 g) = 1/10^7. -/
theorem rna_body_fraction :
    Source.doseOneNominalTotalRnaMg / (Source.preDoseWeightKg * 10 ^ 6) = 1/10000000 ∧
    Source.rnaBodyMassFraction = 1/10000000 := by
  decide +kernel

/-- The material ledger is paid and the delivery/energy account stays OPEN:
`settled` and `energyAccountSettled` are false, the energy account is the
uninhabitable marker, and the consumer interface that names the next
physical/resource consumer is non-empty. -/
theorem physical_delivery_open :
    Source.physicalDelivery.settled = false ∧
    Source.physicalDelivery.energyAccountSettled = false ∧
    Source.physicalDelivery.energyAccount = Longitudinal.NoPublicValue.absent ∧
    Source.physicalDelivery.consumerInterface.length > 0 ∧
    Source.capability.energyAccountOpen = true ∧
    Source.capability.consumerInterface = Source.physicalDelivery.consumerInterface ∧
    Source.capability.consumerInterface.length > 0 := by
  decide +kernel

end Substance

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Supply
