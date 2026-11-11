import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcingGapAction.Source
import H0mework.Versions.R7e4da746.Arithmetic.RieszColumns.Window

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKSourceFiniteUpdate
open Complex MeasureTheory BurnolPhysicalState
open OriginalRieszFiniteSource OriginalRieszFiniteColumns
open OriginalKSourceGramAction OriginalKSourceResolventReconstruction
open OriginalRieszFinitePairing.CoPoisson.Ward
noncomputable section

private theorem nativeIntegral_add_source (lambda : ℂ) (left right : BurnolL2) (h : ℝ) :
    nativeIntegral lambda (left + right) h =
      nativeIntegral lambda left h + nativeIntegral lambda right h := by
  unfold nativeIntegral
  calc
    _ = ∫ t : ℝ in (0 : ℝ)..h,
        nativeIntegrand lambda left h t + nativeIntegrand lambda right h t := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [nativeIntegrand,map_add,smul_add]
    _ = _ := intervalIntegral.integral_add (nativeIntegrand_integrable lambda left h)
      (nativeIntegrand_integrable lambda right h)

private theorem nativeIntegral_smul_source (lambda alpha : ℂ) (value : BurnolL2) (h : ℝ) :
    nativeIntegral lambda (alpha • value) h = alpha • nativeIntegral lambda value h := by
  unfold nativeIntegral
  calc
    _ = ∫ t : ℝ in (0 : ℝ)..h, alpha • nativeIntegrand lambda value h t := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only [nativeIntegrand]
      rw [map_smul,smul_comm]
    _ = _ := intervalIntegral.integral_smul alpha _

/-- One original forcing column and the complete constant contact generate the second primitive. -/
def secondPrimitiveSource (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  fourierL2 (backwardIntegral (sourceRate c) (regularForcing c 0) h) +
    (2 * sourceRate c) • nativeIntegral (sourceRate c) (fourierL2 ConstantDual.seed) h

/-- Fourier is complex linear. The backward primitive keeps lambda and h unchanged. -/
theorem second_primitive_source (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    nativeIntegral (sourceRate c) (regularForcing c 1) h = secondPrimitiveSource c h := by
  have forcing : regularForcing c 1 =
      fourierL2 (regularForcing c 0) + (2 * sourceRate c) • fourierL2 ConstantDual.seed :=
    sub_eq_iff_eq_add.mp (OriginalKForcingGapAction.fourier_forcing0_source c).symm
  rw [forcing,nativeIntegral_add_source,nativeIntegral_smul_source,
    ← fourier_backwardIntegral]
  rfl

end
end OriginalKSourceFiniteUpdate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

