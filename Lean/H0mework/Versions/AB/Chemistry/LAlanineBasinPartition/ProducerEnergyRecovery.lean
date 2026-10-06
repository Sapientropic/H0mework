import H0mework.Versions.AB.Chemistry.LAlanineBasinPartition.CalculationBasinIntegrals

set_option autoImplicit false
set_option maxRecDepth 4096

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinPartition.EnergyRecovery

open SourceData LAlanine40K2025.BasinPartition.Calculation Energy.Interface
open scoped BigOperators
noncomputable section

def mappedField : OldField → Field := ![0, 1, 2, 4, 5, 6, 7]

def originalIntegral : OldField → Int :=
  ![Source.oldGridElectronIntegral, oldComponentIntegral .kinetic, oldComponentIntegral .kinetic,
    oldComponentIntegral .electronNuclear, oldComponentIntegral .coulomb,
    oldComponentIntegral .b88Exchange, oldComponentIntegral .lypCorrelation]

theorem grid_to_original (field : OldField) :
    Source.globalFloatSums (mappedField field) =
      1000 * originalIntegral field + Source.gridToOldResidual field := by
  fin_cases field <;> decide

theorem partition_to_original (field : OldField) :
    (∑ bucket : Bucket, basinIntegral bucket (mappedField field)) =
      1000 * originalIntegral field + Source.gridToOldResidual field +
        Source.globalPointRoundingResidual (mappedField field) := by
  rw [allBuckets_commute, wholePoint_to_float, grid_to_original]

def electronicOldIntegral : Int :=
  oldComponentIntegral .kinetic + oldComponentIntegral .electronNuclear +
    oldComponentIntegral .coulomb + oldComponentIntegral .b88Exchange +
      oldComponentIntegral .lypCorrelation

def electronicRoundingResidual : Int :=
  Source.globalPointRoundingResidual 1 + Source.globalPointRoundingResidual 4 +
    Source.globalPointRoundingResidual 5 + Source.globalPointRoundingResidual 6 +
      Source.globalPointRoundingResidual 7

def electronicGridResidual : Int :=
  Source.gridToOldResidual 1 + Source.gridToOldResidual 3 + Source.gridToOldResidual 4 +
    Source.gridToOldResidual 5 + Source.gridToOldResidual 6

theorem wholeElectronic_partition :
    (∑ bucket : Bucket, basinElectronicIntegral bucket) =
      wholePointIntegral 1 + wholePointIntegral 4 + wholePointIntegral 5 +
        wholePointIntegral 6 + wholePointIntegral 7 := by
  simp only [basinElectronicIntegral, Finset.sum_add_distrib, allBuckets_commute]

theorem electronicRecovery :
    (∑ bucket : Bucket, basinElectronicIntegral bucket) - electronicRoundingResidual -
      electronicGridResidual = 1000 * electronicOldIntegral := by
  rw [wholeElectronic_partition]
  simp only [wholePoint_to_float]
  have h1 := grid_to_original 1
  have h4 := grid_to_original 3
  have h5 := grid_to_original 4
  have h6 := grid_to_original 5
  have h7 := grid_to_original 6
  change Source.globalFloatSums 1 = 1000 * oldComponentIntegral .kinetic + Source.gridToOldResidual 1 at h1
  change Source.globalFloatSums 4 = 1000 * oldComponentIntegral .electronNuclear + Source.gridToOldResidual 3 at h4
  change Source.globalFloatSums 5 = 1000 * oldComponentIntegral .coulomb + Source.gridToOldResidual 4 at h5
  change Source.globalFloatSums 6 = 1000 * oldComponentIntegral .b88Exchange + Source.gridToOldResidual 5 at h6
  change Source.globalFloatSums 7 = 1000 * oldComponentIntegral .lypCorrelation + Source.gridToOldResidual 6 at h7
  rw [h1, h4, h5, h6, h7]
  unfold electronicRoundingResidual electronicGridResidual electronicOldIntegral
  ring

theorem originalSixfold_recovered :
    electronicOldIntegral + oldComponentIntegral .nuclearRepulsion =
      Runtime.basinParentLedger.grandRowSum + Runtime.basinParentLedger.rowResidualSum := by
  have rows : Runtime.basinParentLedger.rowToIntegralExact :=
    Reentry.Producer.nuclearTargetEnergyRows_exact
  have hk := rows .kinetic
  have he := rows .electronNuclear
  have hc := rows .coulomb
  have hb := rows .b88Exchange
  have hl := rows .lypCorrelation
  have hn := rows .nuclearRepulsion
  unfold electronicOldIntegral oldComponentIntegral
  change _ =
    (Runtime.basinParentLedger.rowSum .kinetic + (Runtime.basinParentLedger.rowSum .electronNuclear +
      (Runtime.basinParentLedger.rowSum .coulomb + (Runtime.basinParentLedger.rowSum .b88Exchange +
        (Runtime.basinParentLedger.rowSum .lypCorrelation + (Runtime.basinParentLedger.rowSum .nuclearRepulsion + 0)))))) +
    ((Runtime.basinParentLedger.integral .kinetic).rowQuantizationResidual +
      ((Runtime.basinParentLedger.integral .electronNuclear).rowQuantizationResidual +
        ((Runtime.basinParentLedger.integral .coulomb).rowQuantizationResidual +
          ((Runtime.basinParentLedger.integral .b88Exchange).rowQuantizationResidual +
            ((Runtime.basinParentLedger.integral .lypCorrelation).rowQuantizationResidual +
              ((Runtime.basinParentLedger.integral .nuclearRepulsion).rowQuantizationResidual + 0))))))
  omega

def correctedMolecularEnergy : Int :=
  (∑ bucket : Bucket, basinElectronicIntegral bucket) - electronicRoundingResidual -
    electronicGridResidual + 1000 * oldComponentIntegral .nuclearRepulsion +
      1000 * Runtime.basinParentLedger.componentRoundingResidual +
        1000 * Runtime.basinParentLedger.scfRecomputationResidual

theorem fullMolecularEnergy_recovered :
    correctedMolecularEnergy = 1000 * Runtime.basinParentLedger.reportedSCF := by
  have whole := Reentry.Producer.nuclearTargetWholeEnergy
  change Runtime.basinParentLedger.grandRowSum + Runtime.basinParentLedger.rowResidualSum +
    Runtime.basinParentLedger.componentRoundingResidual +
      Runtime.basinParentLedger.scfRecomputationResidual = Runtime.basinParentLedger.reportedSCF at whole
  unfold correctedMolecularEnergy
  rw [electronicRecovery]
  have six := originalSixfold_recovered
  omega

theorem sourceGlobalEnergyAccounts :
    Source.gridElectronicIntegral = Source.globalFloatSums 1 + Source.globalFloatSums 4 +
      Source.globalFloatSums 5 + Source.globalFloatSums 6 + Source.globalFloatSums 7 ∧
    Source.gridWithNuclearRepulsion = Source.gridElectronicIntegral +
      1000 * oldComponentIntegral .nuclearRepulsion ∧
    Source.gridWithNuclearRepulsion = 1000 *
      (electronicOldIntegral + oldComponentIntegral .nuclearRepulsion) + Source.totalGridToOldResidual ∧
    Source.totalGridToOldResidual = electronicGridResidual := by decide

theorem originalNuclearPairs_preserved :
    Runtime.basinParentLedger.nuclearPairs = Reentry.Source.stepReadout.nuclear.targetLedger.nuclearPairs ∧
    Runtime.basinParentLedger.nuclearPairs.size = 78 :=
  ⟨rfl, Reentry.Producer.nuclearTargetEnergyCensus.2.1⟩

/-- The original unquantized potential remains distinct from the nano ledger. -/
theorem physicalPotential_resolution :
    |Runtime.basinParentFrame.potential - (Runtime.basinParentLedger.reportedSCF : ℚ) / 10 ^ 9| <
      (1 : ℚ) / (2 * 10 ^ 9) := Reentry.Producer.nuclearTargetPotential_resolution

end
end LAlanine40K2025.BasinPartition.EnergyRecovery
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
