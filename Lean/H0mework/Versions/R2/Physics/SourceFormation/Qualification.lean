import H0mework.Versions.R2.Physics.SourceFormation.Scalar

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ArbitrarySourceFormation.Qualification

open StageNineEnrichedProofFreeSource StageNineDynamicBreakingVacuum
open SU7ExteriorBreakingYukawa SU7ExteriorMatterFullVariations SU7ExteriorYukawaMassSpectrum

noncomputable section

theorem vacuum_nonzero_iff (source : SmoothUnifiedSource) :
    sourceGeneratedVacuumBase source ≠ 0 ↔ source.stageEight.physicalPhaseAmplitude ≠ 0 := by
  rw [Scalar.vacuum_scale source, smul_ne_zero_iff]
  simp only [positive_sourceGeneratedVacuumBase_nonzero, ne_eq, Int.cast_eq_zero,
    not_false_eq_true, and_true]

theorem mass_scale (source : SmoothUnifiedSource) :
    exteriorYukawaMassMap (sourceGeneratedVacuumBase source) =
      (source.stageEight.physicalPhaseAmplitude : ℂ) •
        exteriorYukawaMassMap (sourceGeneratedVacuumBase positiveSmoothUnifiedSource) := by
  rw [Scalar.vacuum_scale source, exteriorYukawaMassMap_smul]

theorem mass_nonzero_iff (source : SmoothUnifiedSource) :
    exteriorYukawaMassMap (sourceGeneratedVacuumBase source) ≠ 0 ↔
      source.stageEight.physicalPhaseAmplitude ≠ 0 := by
  have original : exteriorYukawaMassMap (sourceGeneratedVacuumBase positiveSmoothUnifiedSource) ≠ 0 := by
    rw [positive_sourceGeneratedVacuumBase]
    exact finiteGenerationJointMassMap_ne_zero
  rw [mass_scale source, smul_ne_zero_iff]
  simp only [original, ne_eq, Int.cast_eq_zero, not_false_eq_true, and_true]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ArbitrarySourceFormation.Qualification
