import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.CountingQuadraticLimit
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFourier
import H0mework.Versions.R7e4da746.Arithmetic.MellinTateSource.Isometry
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantForward
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantFourier
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.FiniteForcing
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.KCounting
import H0mework.Arithmetic.TruncatedFourier.RadiusIntegralKernel
import H0mework.Versions.R7e4da746.Arithmetic.TruncatedFourier.Overlap
import H0mework.Versions.R7e4da746.Arithmetic.RiemannResolvent.CompleteTate
import H0mework.Versions.R7e4da746.Arithmetic.RiemannSpectral.MultiplicativeDilation

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.DivisorJoint
open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.CountingQuadraticLimit
noncomputable section

def joint : BurnolL2 →L[ℂ] BurnolL2 :=
  fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.comp burnolTateReciprocalL2

theorem joint_apply (v : BurnolL2) : joint v = fourierL2 (burnolTateReciprocalL2 v) := rfl

theorem joint_dilation (h : ℝ) (v : BurnolL2) :
    joint (burnolMultiplicativeDilation h v) = burnolMultiplicativeDilation h (joint v) := by
  simp only [joint_apply]
  have reversed := burnolTateReciprocalL2_dilation_inverse (-h) v
  simp only [neg_neg] at reversed
  rw [← reversed, fourierL2_burnolMultiplicativeDilation, neg_neg]

private theorem seed_even : reflectL2 ConstantDual.seed = ConstantDual.seed := by
  change reflectL2 (burnolRadiusZeroExtension (1 / 4 : ℝ) (intervalConstant (1 / 4 : ℝ))) = _
  rw [burnolRadiusZeroExtension_reflect, reflectRestricted_intervalConstant]
  rfl

private theorem finite_forward_even (N : ℕ) :
    reflectL2 (FiniteForcing.source N ConstantDual.seed) = FiniteForcing.source N ConstantDual.seed := by
  rw [← fourierL2_fourierL2, ← KCounting.dual_fourier, ← source_fourier,
    fourierL2_fourierL2, seed_even, CountingDual.sourceCLM_apply]

private theorem forward_even : reflectL2 ConstantForward.value = ConstantForward.value := by
  have reflected := (reflectL2.continuous.tendsto ConstantForward.value).comp ConstantForward.original_tendsto
  have same := reflected.congr' (Eventually.of_forall (fun N => finite_forward_even N))
  exact tendsto_nhds_unique same ConstantForward.original_tendsto

theorem original_forward_joint : ConstantForward.value = joint ConstantDual.value := by
  rw [joint_apply, ← ConstantFourier.original_square, fourierL2_fourierL2, forward_even]

end
end OriginalGamma.Source.DivisorJoint
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
