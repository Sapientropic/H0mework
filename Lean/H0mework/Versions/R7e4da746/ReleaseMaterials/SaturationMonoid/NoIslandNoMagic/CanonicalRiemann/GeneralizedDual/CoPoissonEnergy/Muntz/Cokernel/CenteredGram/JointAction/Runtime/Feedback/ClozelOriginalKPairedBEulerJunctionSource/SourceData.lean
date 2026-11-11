import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Spectral.Direct.Fourier.ClozelBurnolPaFourierPairedAction
import H0mework.Versions.R7e4da746.Arithmetic.RieszFinitePairing.Phi
import H0mework.Versions.R7e4da746.Arithmetic.RieszFinitePairing.ExteriorRaw
import H0mework.Versions.R7e4da746.Arithmetic.RieszSourceKernel.Generated

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPairedBEulerJunctionSource
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing
open scoped ENNReal Topology BigOperators FourierTransform
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "Eq" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction

def junctionShift : ℝ := Real.log stageZeroSonineQ
def junctionPoint : ℝ := q*Real.exp (-junctionShift)

def sourceAction (c:BurnolCompletedMellinCoordinate) : BurnolL2 :=
  pairedBurnolMultiplicativeDilation junctionShift (burnolCompletedMellinRieszVector c:BurnolL2)

def sourceFirst (c:BurnolCompletedMellinCoordinate) : M :=
  burnolAmbientMeanZeroFirstCorrection (sourceAction c)

def sourceSecond (c:BurnolCompletedMellinCoordinate) : M :=
  burnolAmbientMeanZeroSecondCorrection (sourceAction c)

def sourceDrive (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : M :=
  ![burnolAmbientMeanZeroPosition (sourceAction c),burnolAmbientMeanZeroFourier (sourceAction c)] i

def sourceCorrection (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : M :=
  ![sourceFirst c,sourceSecond c] i

def sourcePartner (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : M :=
  ![sourceSecond c,sourceFirst c] i

def sourceFace (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : BurnolL2 :=
  ![sourceAction c,fourierL2 (sourceAction c)] i

def sourceMean (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : ℂ :=
  burnolQuarterMeanCoefficient (Rq (burnolAmbientEvenPart (sourceFace c i)))

def originalGap (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : ℂ :=
  ![positionMean c,fourierMean c] i

def originalOuter (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) : ℂ :=
  ![burnolRieszStatePositiveOuterRaw c x,burnolRieszSingleFourierSourceRaw c x+fourierMean c] i

def originalCharge (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : ℂ :=
  ![-Kernel.A c,Kernel.beta c] i

def sourceInnerRaw (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) : ℂ :=
  (((Real.exp (junctionShift/2):ℂ)+(Real.exp (-junctionShift/2):ℂ))/2)*originalGap c i-
    sourceMean c i-burnolMeanZeroFourierRaw (sourcePartner c i) x

def sourceOuterRaw (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) : ℂ :=
  ((Real.exp (junctionShift/2):ℂ)*originalOuter c i (Real.exp junctionShift*x)+
    (Real.exp (-junctionShift/2):ℂ)*originalGap c i)/2-
      sourceMean c i-burnolMeanZeroFourierRaw (sourcePartner c i) x

def sourceRaw (c:BurnolCompletedMellinCoordinate) (i:Fin 2) (x:ℝ) : ℂ :=
  if |x|≤junctionPoint then sourceInnerRaw c i |x| else sourceOuterRaw c i |x|

def sourceJump (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : ℂ :=
  (Real.exp (junctionShift/2):ℂ)/2*originalCharge c i

def sourceTrace (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : ℂ := sourceOuterRaw c i q

end OriginalKPairedBEulerJunctionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
