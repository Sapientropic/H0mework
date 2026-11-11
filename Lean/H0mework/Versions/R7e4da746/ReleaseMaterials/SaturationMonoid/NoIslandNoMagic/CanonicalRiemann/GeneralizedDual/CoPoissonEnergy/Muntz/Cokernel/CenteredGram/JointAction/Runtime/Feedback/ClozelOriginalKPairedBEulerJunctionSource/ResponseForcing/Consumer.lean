import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.ResponseForcing.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Spectral.Direct.ClozelBurnolPaRiemannConsumer
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPairedBEulerJunctionSource.ResponseForcing.Consumer
open Complex MeasureTheory BurnolPhysicalState
open OriginalRieszFinitePairing OriginalKPairedBEulerJunctionSource.ResponseForcing.Source
open scoped InnerProductSpace

def completeResponseNet (c:BurnolCompletedMellinCoordinate) (h:ℝ) : ℂ :=
 (pairedMellinTranslationCharacter c.value h-pairedMellinTranslationCharacter (star c.value) h)*
  kernelSelfSource c+(1/2:ℂ)*star (responseFinitePrice c h)

/-- The actual evaluator consumes the complete response and both unit legs at the same shift. -/
theorem actual_evaluator_response (c:BurnolCompletedMellinCoordinate) (h:ℝ) (nonnegative:0≤h) :
 evaluatorSource c h=completeResponseNet c h := by
 rw [OriginalKPairedBEulerJunctionSource.BandFiniteSourcePrice.original_evaluator_finite_price c h nonnegative,
  actual_finite_price]
 rfl

/-- This calls the original fixed-residual consumer before rewriting the generated response price. -/
theorem actual_original_fixed_residual (c:BurnolCompletedMellinCoordinate)
 (zero:riemannZeta c.value=0) :
 -burnolPaFixedShiftResidual c zero=completeResponseNet c (Real.log stageZeroSonineQ) := by
 rw [OriginalKPairedBEulerJunctionSource.BandFiniteSourcePrice.original_fixed_residual_finite_price c zero,
  actual_finite_price]
 rfl

/-- The installed original occurrence has exactly this complete response net as its remaining obligation. -/
theorem actual_original_fixed_consumer (c:BurnolCompletedMellinCoordinate)
 (zero:riemannZeta c.value=0) :
 BurnolPaBoundaryCancellationAt c zero ↔ completeResponseNet c (Real.log stageZeroSonineQ)=0 := by
 unfold BurnolPaBoundaryCancellationAt
 rw [installedOriginalK_fixedResidual_eq_original]
 have paid:=actual_original_fixed_residual c zero
 constructor
 · intro zeroResidual
   rw [zeroResidual,neg_zero] at paid
   exact paid.symm
 · intro zeroNet
   rw [zeroNet] at paid
   exact neg_eq_zero.mp paid

end OriginalKPairedBEulerJunctionSource.ResponseForcing.Consumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
