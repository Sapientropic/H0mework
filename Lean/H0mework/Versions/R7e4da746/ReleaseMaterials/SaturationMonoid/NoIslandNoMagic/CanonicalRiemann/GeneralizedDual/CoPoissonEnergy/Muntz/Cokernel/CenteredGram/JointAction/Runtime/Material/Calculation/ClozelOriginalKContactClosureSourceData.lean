import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.SourceData

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open Complex MeasureTheory Set Filter FourierTransform BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing
open scoped ENNReal Topology InnerProductSpace FourierTransform
local notation "q" => (1/4 : ℝ)
local notation "p" => OriginalKPairedBEulerJunctionSource.junctionPoint
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "Eq" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
namespace OriginalKPairedBEulerJunctionSource
namespace TwoPieceFourierAction
def eta (point:ℝ) : M := Constructor.endpointColumn point+Constructor.endpointColumn (-point)
end TwoPieceFourierAction

def sourceContact (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : M :=
  sourceTrace c i • TwoPieceFourierAction.eta q-
    (((junctionPoint/q:ℝ):ℂ)*sourceJump c i) • TwoPieceFourierAction.eta junctionPoint

namespace PsiDrive
def gapRegular : BurnolL2 := (2*q:ℂ) • burnolAmbientGapRieszVector q

def psiPositionField : BurnolL2 := fourierL2 Response.wholeU-Response.wholeV+gapRegular

def psiFourierField : BurnolL2 := Response.wholeU-fourierL2 Response.wholeV+fourierL2 gapRegular

def phasePair (x:ℝ) : ℂ := Constructor.phase q x+Constructor.phase (-q) x

def pairedPhase (x:ℝ) : ℂ :=
  ((Real.exp (junctionShift/2):ℂ)*phasePair (Real.exp junctionShift*x)+
    (Real.exp (-junctionShift/2):ℂ)*phasePair (Real.exp (-junctionShift)*x))/2

theorem paired_phase_continuous_source : Continuous pairedPhase := by
  have positive:=Constructor.phaseContinuous q
  have negative:=Constructor.phaseContinuous (-q)
  unfold pairedPhase phasePair
  fun_prop

local notation "paired_phase_continuous" => paired_phase_continuous_source

def psiQuarter (i:Fin 2) : Hq :=
  ![Rq (pairedBurnolMultiplicativeDilation junctionShift psiPositionField),
    Rq (pairedBurnolMultiplicativeDilation junctionShift psiFourierField)-
      (q:ℂ) • Constructor.compact pairedPhase paired_phase_continuous] i

def psiColumn (i:Fin 2) : M := Constructor.zeroMean (psiQuarter i)

def psiU : M := burnolMeanZeroBlockFirst (psiColumn 0,psiColumn 1)

def psiV : M := burnolMeanZeroBlockSecond (psiColumn 0,psiColumn 1)

def contactU (c:BurnolCompletedMellinCoordinate) : M :=
  burnolMeanZeroBlockInverse (sourceContact c 1+S (sourceContact c 0))

def contactV (c:BurnolCompletedMellinCoordinate) : M := sourceContact c 0+S (contactU c)

end PsiDrive

namespace BandSourceAction
def sourceForce (c:BurnolCompletedMellinCoordinate) (i:Fin 2) : M :=
 ![Kernel.A c • PsiDrive.psiU+Kernel.beta c • PsiDrive.psiV-PsiDrive.contactU c,
   (-Kernel.A c) • PsiDrive.psiV+(-Kernel.beta c) • PsiDrive.psiU-PsiDrive.contactV c] i
end BandSourceAction

namespace BandFullStockEuler
def regularSource (c:BurnolCompletedMellinCoordinate) : BurnolL2 :=
 Eq (BandSourceAction.sourceForce c 0:Hq)-fourierL2 (Eq (BandSourceAction.sourceForce c 1:Hq))+
 (sourceTrace c 0-((p/q:ℝ):ℂ)*sourceJump c 0) • Eq (intervalConstant q)-
 (sourceTrace c 1-((p/q:ℝ):ℂ)*sourceJump c 1) • fourierL2 (Eq (intervalConstant q))
end BandFullStockEuler
end OriginalKPairedBEulerJunctionSource

namespace OriginalWholeDebtRAdjointContactSource
def step (radius : ℝ) : BurnolL2 := ((2*radius : ℝ) : ℂ) • burnolAmbientGapRieszVector radius
end OriginalWholeDebtRAdjointContactSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
