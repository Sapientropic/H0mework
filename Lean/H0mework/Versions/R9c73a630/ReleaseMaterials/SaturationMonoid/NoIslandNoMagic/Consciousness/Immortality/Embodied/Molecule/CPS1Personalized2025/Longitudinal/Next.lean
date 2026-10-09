import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal.Runtime

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal

noncomputable section

/-- 执行后留下什么下一轮能力: the material at the generated next reproduces every
parent material verbatim and additionally carries the executed maintenance chains,
the carried-forward capability, the formulation/material-consumption account and the
explicit residuals. -/
theorem next_consumes_longitudinal_maintenance :
    (readMaterial afterParent).inputs = (Ngs.readMaterial parentRuntime).inputs ∧
    (readMaterial afterParent).sequence = (Ngs.readMaterial parentRuntime).sequence ∧
    (readMaterial afterParent).experiment = (Ngs.readMaterial parentRuntime).experiment ∧
    (readMaterial afterParent).response = (Ngs.readMaterial parentRuntime).response ∧
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
    (readMaterial afterParent).maintenance = Source.chains ∧
    (readMaterial afterParent).capability.carriedScavengerDose = 5 ∧
    (readMaterial afterParent).capability.carriedAmmoniaEvidence = ⟨13,9,28⟩ ∧
    (readMaterial afterParent).capability.fullProteinDiet = true ∧
    (readMaterial afterParent).formulation.doseOneNominalTotalRnaMg = 357/500 ∧
    (readMaterial afterParent).formulation.doseTwoNominalTotalRnaMg = none ∧
    (readMaterial afterParent).formulation.doseTwoWeightUnmeasured = true ∧
    (readMaterial afterParent).formulation.doseTwoOverDoseOne = 3 ∧
    (readMaterial afterParent).formulation.supply.settled = false ∧
    (readMaterial afterParent).residuals = Source.residuals := by
  rw [readMaterial_eq]
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_,?_,?_,?_,rfl,?_,?_,?_,?_,?_,?_,?_,?_,rfl⟩
  · exact (inherited_complete_joint_alleles afterParent).completeReadPartition.1
  · exact (inherited_complete_joint_alleles afterParent).completeReadPartition.2.1
  · exact (inherited_complete_joint_alleles afterParent).completeReadPartition.2.2.1
  · exact (inherited_complete_joint_alleles afterParent).completeReadPartition.2.2.2.1
  · exact (inherited_complete_joint_alleles afterParent).directConsumer.2.2.1
  · exact (inherited_complete_joint_alleles afterParent).directConsumer.2.2.2
  · exact (readCertificate afterParent).capabilityCarried.1
  · exact (readCertificate afterParent).capabilityCarried.2.1
  · exact (readCertificate afterParent).capabilityCarried.2.2.1
  · exact (readCertificate afterParent).nominalMass.1
  · exact (readCertificate afterParent).formulationResiduals.2.2.1
  · exact (readCertificate afterParent).formulationResiduals.2.2.2.1
  · exact (readCertificate afterParent).formulationResiduals.1
  · exact (readCertificate afterParent).supplyOpen.2.2

end

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Longitudinal
