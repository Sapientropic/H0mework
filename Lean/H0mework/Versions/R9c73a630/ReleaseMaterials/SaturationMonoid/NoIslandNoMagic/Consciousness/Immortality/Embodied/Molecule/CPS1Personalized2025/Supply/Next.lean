import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Supply.Runtime

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Supply

noncomputable section

/-- 执行后留下什么下一轮能力: the material at the generated next reproduces
every parent material verbatim — the root/Ngs reads, the four maintenance
chains, the carried-forward capability record, the formulation account and
the explicit residuals — and additionally carries the paid per-species
physical-supply ledger (measured-ratio mass allocation, residue-sum
substance values, the mRNA molecule upper report, citrulline rate,
RNA/body fraction, batch characterization), the OPEN delivery record, the
supply residuals and the carried-forward supply capability. -/
theorem next_consumes_physical_supply :
    (readMaterial afterParent).inputs = (Longitudinal.readMaterial parentRuntime).inputs ∧
    (readMaterial afterParent).sequence = (Longitudinal.readMaterial parentRuntime).sequence ∧
    (readMaterial afterParent).experiment = (Longitudinal.readMaterial parentRuntime).experiment ∧
    (readMaterial afterParent).response = (Longitudinal.readMaterial parentRuntime).response ∧
    (readMaterial afterParent).originalAlleles = Ngs.Source.rows ∧
    (readMaterial afterParent).reference = Ngs.Source.reference ∧
    (readMaterial afterParent).caption = Ngs.Source.caption ∧
    (readMaterial afterParent).provenance =
      (Ngs.Source.parentSha,Ngs.Source.pdfSha,Ngs.Source.imageSha) ∧
    (readMaterial afterParent).shownReads = 2334 ∧
    (readMaterial afterParent).originalQReads = 1488 ∧
    (readMaterial afterParent).a8Reads = 1531 ∧
    (readMaterial afterParent).openFrameReads = 1554 ∧
    ((readMaterial afterParent).consumers 11).1.2 = false ∧
    ((readMaterial afterParent).consumers 11).2 =
      some ((CPS1Personalized2025.Source.referenceProtein.set 334 "Y") ++ ["*"]) ∧
    (readMaterial afterParent).maintenance = Longitudinal.Source.chains ∧
    (readMaterial afterParent).capability.carriedScavengerDose = 5 ∧
    (readMaterial afterParent).capability.carriedAmmoniaEvidence = ⟨13,9,28⟩ ∧
    (readMaterial afterParent).capability.fullProteinDiet = true ∧
    (readMaterial afterParent).formulation.doseOneNominalTotalRnaMg = 357/500 ∧
    (readMaterial afterParent).formulation.doseTwoNominalTotalRnaMg = none ∧
    (readMaterial afterParent).formulation.doseTwoWeightUnmeasured = true ∧
    (readMaterial afterParent).formulation.doseTwoOverDoseOne = 3 ∧
    (readMaterial afterParent).formulation.supply.settled = false ∧
    (readMaterial afterParent).residuals = Longitudinal.Source.residuals ∧
    (readMaterial afterParent).supply = Source.account ∧
    (readMaterial afterParent).supply.guideResidueSumGPerMol = 33040 ∧
    (readMaterial afterParent).supply.mrnaResidueSumGPerMol = 165653653/100 ∧
    (readMaterial afterParent).supply.doseOneNominalTotalRnaMg = 357/500 ∧
    (readMaterial afterParent).supply.massRatio.target = 1 ∧
    (readMaterial afterParent).supply.massRatio.preparation = 1 ∧
    (readMaterial afterParent).supply.massRatio.measuredBatch = 11/10 ∧
    (readMaterial afterParent).supply.doseOneGrnaMg = 187/500 ∧
    (readMaterial afterParent).supply.doseOneMrnaMg = 17/50 ∧
    (readMaterial afterParent).supply.grnaResidueSumSubstanceMol = 187/16520000000 ∧
    (readMaterial afterParent).supply.mrnaResidueSumSubstanceMol = 17/82826826500 ∧
    (readMaterial afterParent).supply.mrnaResidueSumMolecules ≤ 13 * 10 ^ 13 ∧
    (readMaterial afterParent).supply.mrnaMoleculesUpperScaled = 13 ∧
    (readMaterial afterParent).supply.clinicalBatch.hydrodynamicDiameterNm = 73 ∧
    (readMaterial afterParent).supply.citrullineMgPerDay = 1428 ∧
    (readMaterial afterParent).supply.rnaBodyMassFraction = 1/10000000 ∧
    (readMaterial afterParent).delivery = Source.physicalDelivery ∧
    (readMaterial afterParent).delivery.settled = false ∧
    (readMaterial afterParent).delivery.energyAccountSettled = false ∧
    (readMaterial afterParent).supplyResiduals = Source.supplyResiduals ∧
    (readMaterial afterParent).supplyResiduals.mrnaCapMass = Longitudinal.NoPublicValue.absent ∧
    (readMaterial afterParent).supplyResiduals.grnaEndGroupAdjustment =
      Longitudinal.NoPublicValue.absent ∧
    (readMaterial afterParent).supplyCapability = Source.capability ∧
    (readMaterial afterParent).supplyCapability.energyAccountOpen = true := by
  rw [readMaterial_eq]
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_,?_,?_,?_,rfl,?_,?_,?_,?_,?_,?_,?_,?_,rfl,
          rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · exact (inherited_complete_joint_alleles afterParent).completeReadPartition.1
  · exact (inherited_complete_joint_alleles afterParent).completeReadPartition.2.1
  · exact (inherited_complete_joint_alleles afterParent).completeReadPartition.2.2.1
  · exact (inherited_complete_joint_alleles afterParent).completeReadPartition.2.2.2.1
  · exact (inherited_complete_joint_alleles afterParent).directConsumer.2.2.1
  · exact (inherited_complete_joint_alleles afterParent).directConsumer.2.2.2
  · exact (inherited_complete_longitudinal afterParent).capabilityCarried.1
  · exact (inherited_complete_longitudinal afterParent).capabilityCarried.2.1
  · exact (inherited_complete_longitudinal afterParent).capabilityCarried.2.2.1
  · exact (inherited_complete_longitudinal afterParent).nominalMass.1
  · exact (inherited_complete_longitudinal afterParent).formulationResiduals.2.2.1
  · exact (inherited_complete_longitudinal afterParent).formulationResiduals.2.2.2.1
  · exact (inherited_complete_longitudinal afterParent).formulationResiduals.1
  · exact (inherited_complete_longitudinal afterParent).supplyOpen.2.2
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Supply
