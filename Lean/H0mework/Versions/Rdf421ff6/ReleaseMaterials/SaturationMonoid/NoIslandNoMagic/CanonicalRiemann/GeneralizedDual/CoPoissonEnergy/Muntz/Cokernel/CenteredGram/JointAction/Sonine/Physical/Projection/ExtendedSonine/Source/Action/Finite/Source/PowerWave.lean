import H0mework.Versions.V2.Arithmetic.RieszFiniteSource.SourceProfile
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.SingularCounting

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalPrimitiveRankBalance
def conjugateCoordinate (coordinate : BurnolCompletedMellinCoordinate) : BurnolCompletedMellinCoordinate :=
  ⟨star coordinate.value,by simpa only [Complex.star_def,Complex.conj_re] using coordinate.rightHalf,
    by simpa only [Complex.star_def,Complex.conj_re] using coordinate.belowOne⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalPrimitiveRankBalance
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open Complex BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace
local instance powerWaveQuarterComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
local instance powerWavePhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

namespace OriginalKDirectRCofinalOutsideVolterraSource
def hPowerBColumn (coordinate : BurnolCompletedMellinCoordinate) : BurnolQuarterMeanZeroCarrier :=
  burnolMeanZeroBlockInverse (SingularCounting.centeredPower coordinate)
def hPowerBSecond (coordinate : BurnolCompletedMellinCoordinate) : BurnolQuarterMeanZeroCarrier :=
  -burnolMeanZeroTruncatedFourier (hPowerBColumn coordinate)
def hPowerPhysicalCorrection (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolAmbientEvenPart (burnolQuarterZeroExtension (hPowerBColumn coordinate : BurnolQuarterIntervalL2)+
    fourierL2 (burnolQuarterZeroExtension (hPowerBSecond coordinate : BurnolQuarterIntervalL2)))
end OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKDirectRCofinalOutsideVolterraSource

namespace OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
def physicalOutsideColumn (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  fourierL2.symm (hPowerPhysicalCorrection (OriginalPrimitiveRankBalance.conjugateCoordinate c))
end OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
namespace OriginalKCrossParameterRAdjointSource.CayleyEnergySource
def sourceDamping (c : BurnolCompletedMellinCoordinate) : ℝ := c.value.re-1/2
def sourceCayley (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  ContinuousLinearMap.id ℂ BurnolL2+(sourceDamping c:ℂ) • burnolDirectRightResolventCLM c
end OriginalKCrossParameterRAdjointSource.CayleyEnergySource
namespace OriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
def sourceSigma (c : BurnolCompletedMellinCoordinate) : ℂ :=
  -inner ℂ ((evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ.starProjection
    (CayleyEnergySource.sourceCayley c (hPowerPhysicalCorrection c)))
    (PhysicalOutsideSource.physicalOutsideColumn c)
end OriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
namespace OriginalKCrossParameterRAdjointSource.UnweightedCayleySource
def sourceAdjointRatio (c : BurnolCompletedMellinCoordinate) : ℂ :=
  star (CayleyIntertwiningSource.sourceSigma c)/((‖hPowerPhysicalCorrection c‖^2:ℝ):ℂ)
end OriginalKCrossParameterRAdjointSource.UnweightedCayleySource

namespace OriginalWholeDebtRPowerWaveDilationSource
def damping (c : BurnolCompletedMellinCoordinate) : ℝ := c.value.re-1/2
def returnRatio (c : BurnolCompletedMellinCoordinate) : ℂ :=
  OriginalKCrossParameterRAdjointSource.UnweightedCayleySource.sourceAdjointRatio
    (OriginalPrimitiveRankBalance.conjugateCoordinate c)/(damping c:ℂ)
def coupling0 (c : BurnolCompletedMellinCoordinate) : ℂ :=
  returnRatio c*Kernel.beta (OriginalPrimitiveRankBalance.conjugateCoordinate c)+
    (damping c:ℂ)⁻¹*Kernel.A c
def coupling1 (c : BurnolCompletedMellinCoordinate) : ℂ :=
  returnRatio c*Kernel.A (OriginalPrimitiveRankBalance.conjugateCoordinate c)+
    (damping c:ℂ)⁻¹*Kernel.beta c
end OriginalWholeDebtRPowerWaveDilationSource

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
