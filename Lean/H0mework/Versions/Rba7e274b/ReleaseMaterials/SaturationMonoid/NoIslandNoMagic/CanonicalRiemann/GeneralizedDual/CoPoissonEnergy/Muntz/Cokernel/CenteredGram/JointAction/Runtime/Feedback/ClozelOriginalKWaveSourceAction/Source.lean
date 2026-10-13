import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRealCoordinateSourceUnit.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWaveSourceAction
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState

def actualUpperWaveSource (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h •
    (OriginalRieszFinitePairing.CoPoisson.positionSeed coordinate h +
      burnolTateReciprocalL2 (OriginalRieszFinitePairing.CoPoisson.fourierSeed coordinate h))

/-- The original two weighted reciprocal actors generate the complete upper wave on every source measurement. -/
theorem actual_original_upper_wave_source_realization
    (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h)
    (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (actualUpperWaveSource coordinate h) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (OriginalCommonInverseForcing.SourceJoint.upperSourceWave coordinate h)) test := by
  have position := OriginalRieszFinitePairing.CoPoisson.positionSeed_realizes coordinate h nonnegative test
  have fourier := burnolRemainderRealization_fourier
    (OriginalRieszFinitePairing.CoPoisson.fourierSeed coordinate h)
    (OriginalRieszFinitePairing.CoPoisson.fourierWave coordinate h)
    (OriginalRieszFinitePairing.CoPoisson.fourierSeed_realizes coordinate h nonnegative) test
  unfold actualUpperWaveSource OriginalCommonInverseForcing.SourceJoint.upperSourceWave
  rw [← burnolRemainderSourceReadCLM_apply]
  simp only [map_add, map_smul, add_apply, smul_apply,
    burnolRemainderSourceReadCLM_apply, position, fourier]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWaveSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
