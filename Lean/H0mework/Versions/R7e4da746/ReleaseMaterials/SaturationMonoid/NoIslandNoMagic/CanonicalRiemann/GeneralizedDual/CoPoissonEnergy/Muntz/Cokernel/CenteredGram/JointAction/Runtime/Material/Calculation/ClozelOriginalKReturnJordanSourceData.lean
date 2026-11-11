import H0mework.Versions.R7e4da746.Arithmetic.RieszSourceKernel.Generated
import H0mework.Versions.R7e4da746.Arithmetic.RieszFiniteSource.FourierEdge
import H0mework.Versions.R7e4da746.Arithmetic.RieszResponse.ResponseRead
import H0mework.Versions.R7e4da746.Arithmetic.RiemannFirstSource.GeneratorResolventOperator

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalRieszSource OriginalRieszFiniteSource
namespace OriginalKSourceResolventReconstruction
open OriginalKSourceResolventReconstruction
local notation "q" => (1/4:ℝ)
def sourceRate (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  star coordinate.value - 1/2

def sourceResolvent (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) : BurnolL2 :=
  burnolDirectRightResolvent (star coordinate.value/2) value

def sourceY0 (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  -(1/2 : ℂ) • sourceResolvent coordinate (fourierL2 Response.wholeU - Response.wholeV) -
    edgePrimitive coordinate

def sourceY1 (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  -(1/2 : ℂ) • sourceResolvent coordinate (Response.wholeU - fourierL2 Response.wholeV) +
    sourceRate coordinate • sourceResolvent coordinate (fourierPrimitive coordinate) +
    fourierPrimitive coordinate

/-- The source traces retain their original inverse/edge provenance. -/
def generatedK (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  Kernel.A coordinate • sourceY0 coordinate + Kernel.beta coordinate • sourceY1 coordinate

end OriginalKSourceResolventReconstruction

namespace OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKSourceResolventReconstruction
local notation "q" => (1/4:ℝ)
def hQuarterGap (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  burnolQuarterMeanCoefficient (burnolQuarterRestriction (generatedK coordinate))

def hQuarterAmplitude (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  -2*(burnolRadiusMellinTailEvaluator q (by norm_num) (star coordinate.value)
    (by simpa only [Complex.star_def,Complex.conj_re] using coordinate.rightHalf) (generatedK coordinate)+
    hQuarterGap coordinate*(q:ℂ)^(1-star coordinate.value)/(1-star coordinate.value))

end OriginalKDirectRCofinalOutsideVolterraSource

namespace OriginalKCrossParameterRAdjointSource.SharedOutsideSource
open OriginalKSourceResolventReconstruction
local notation "q" => (1/4:ℝ)
def jQuarterGap (c : BurnolCompletedMellinCoordinate) : ℂ :=
  burnolQuarterMeanCoefficient (burnolQuarterRestriction (fourierL2 (generatedK c)))
def jQuarterAmplitude (c : BurnolCompletedMellinCoordinate) : ℂ :=
  -2*(burnolRadiusMellinTailEvaluator q (by norm_num) (star c.value)
    (by simpa only [Complex.star_def,Complex.conj_re] using c.rightHalf) (fourierL2 (generatedK c))+
    jQuarterGap c*(q:ℂ)^(1-star c.value)/(1-star c.value))

end OriginalKCrossParameterRAdjointSource.SharedOutsideSource

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
