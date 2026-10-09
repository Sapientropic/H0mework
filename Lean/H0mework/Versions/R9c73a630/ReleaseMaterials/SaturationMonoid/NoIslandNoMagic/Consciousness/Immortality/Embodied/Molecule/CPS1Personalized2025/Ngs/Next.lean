import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs.Runtime

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs

noncomputable section
 theorem next_consumes_joint_alleles :
    (readMaterial afterParent).inputs = CPS1Personalized2025.Runtime.readInputs parentRuntime ∧
    (readMaterial afterParent).sequence = CPS1Personalized2025.Runtime.readSequence parentRuntime ∧
    (readMaterial afterParent).experiment = CPS1Personalized2025.Runtime.readExperiment parentRuntime ∧
    (readMaterial afterParent).response = CPS1Personalized2025.Runtime.readResponse parentRuntime ∧
    (readMaterial afterParent).originalAlleles = Source.rows ∧
    (readMaterial afterParent).shownReads = 2334 ∧
    (readMaterial afterParent).originalQReads = 1488 ∧
    (readMaterial afterParent).a8Reads = 1531 ∧
    (readMaterial afterParent).openFrameReads = 1554 ∧
    ((readMaterial afterParent).consumers 11).1.2 = false ∧
    ((readMaterial afterParent).consumers 11).2 =
      some ((CPS1Personalized2025.Source.referenceProtein.set 334 "Y") ++ ["*"]) := by
   rw [readMaterial_eq]
   exact ⟨rfl,rfl,rfl,rfl,rfl,(readCertificate afterParent).completeReadPartition.1,
     (readCertificate afterParent).completeReadPartition.2.1,
     (readCertificate afterParent).completeReadPartition.2.2.1,
     (readCertificate afterParent).completeReadPartition.2.2.2.1,
     (readCertificate afterParent).directConsumer.2.2.1,
     (readCertificate afterParent).directConsumer.2.2.2⟩
end

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs
