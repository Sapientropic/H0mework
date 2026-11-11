import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.Lower
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.SourceData
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKJointMobiusSourceProgram
import H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitShell.Weighted
import H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitFourier.Realization

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusSource
open Complex MeasureTheory Set Filter FourierTransform BurnolPhysicalState OriginalRieszSource SourceOperationEffects
open scoped Topology InnerProductSpace FourierTransform BigOperators ContDiff
namespace J
export OriginalKPairedBEulerJunctionSource
  (junctionShift junctionPoint sourceAction sourceFirst sourceSecond)
end J
namespace Flux
export FiniteMobiusResolventFlux (coefficient actualMean)
end Flux
local notation "q" => (1 / 4 : ℝ)
local notation "h" => J.junctionShift
local notation "Hq" => BurnolQuarterIntervalL2
local notation "K" => burnolCompletedMellinRieszVector
local notation "P" => burnolEvenAmbientProjection

def jointValue (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier :=
  P ((OriginalKJointMobiusSourceCalculation.sourceCode c).eval
    OriginalKJointMobiusSourceCalculation.sourceEnvironment)

def jointMean (c : BurnolCompletedMellinCoordinate) : ℂ :=
  burnolConstantGapCoefficient burnolUnscaledCommonGapRadius (jointValue c)

def character (c : BurnolCompletedMellinCoordinate) : ℂ :=
  pairedMellinTranslationCharacter c.value h

def kernelOuter (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * (x : ℂ) ^ (-star c.value) -
    (burnolRieszReturnRaw c x +
      burnolQuarterMeanCoefficient (burnolTruncatedFourier (burnolRieszSingleFourierSource c : Hq)))

def jointOuter (c : BurnolCompletedMellinCoordinate) (branch : Fin 2) (x : ℝ) : ℂ :=
  character c * kernelOuter c x -
    ((Real.exp (h / 2) : ℂ) * kernelOuter c (Real.exp h * x) +
      (Real.exp (-h / 2) : ℂ) *
        (if branch = 0 then OriginalRieszFinitePairing.positionMean c
         else kernelOuter c (Real.exp (-h) * x))) / 2 +
    Constructor.fourierRaw (J.sourceSecond c : Hq) x

def jointRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  if |x| ≤ q then jointMean c
  else if |x| ≤ q * Real.exp h then jointOuter c 0 |x| else jointOuter c 1 |x|

def lower (n : ℕ+) (branch : Fin 2) : ℝ :=
  if branch = 0 then (n : ℕ) * q else (n : ℕ) * q * Real.exp h

def upper (n : ℕ+) (branch : Fin 2) : ℝ :=
  if branch = 0 then min 4 ((n : ℕ) * q * Real.exp h) else 4

def rowWeight (c : BurnolCompletedMellinCoordinate) (n : ℕ+) (branch : Fin 2) (t : ℝ) : ℂ :=
  ((t : ℂ)⁻¹) * (jointOuter c branch (t⁻¹ / (n : ℕ)) - jointMean c)

def rowSlope (c : BurnolCompletedMellinCoordinate) (n : ℕ+) (branch : Fin 2) (t : ℝ) : ℂ :=
  deriv (rowWeight c n branch) (max (upper n branch)⁻¹ (min (lower n branch)⁻¹ t))

def rowSource (c : BurnolCompletedMellinCoordinate) (n : ℕ+) (branch : Fin 2) : BurnolL2 :=
  if lower n branch < upper n branch then
    burnolWeightedReciprocalStepSource (upper n branch)⁻¹ (lower n branch)⁻¹
      (rowWeight c n branch) (rowSlope c n branch) else 0

def rowWave (c : BurnolCompletedMellinCoordinate) (n : ℕ+) (branch : Fin 2) : BurnolL2 :=
  if lower n branch < upper n branch then
    burnolWeightedReciprocalStepWave (upper n branch)⁻¹ (lower n branch)⁻¹
      (rowWeight c n branch) (rowSlope c n branch) else 0

def inverseSource (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,
    Flux.coefficient n • (rowSource c n 0 + rowSource c n 1)

def paWave (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,
    Flux.coefficient n • (rowWave c n 0 + rowWave c n 1)

def sourceRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (symmetricInterval (4 : ℝ)).indicator
    (fun x => ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,
      Flux.coefficient n * (jointRaw c (x / (n : ℕ)) - jointMean c)) x

end OriginalWholeDebtRJointMobiusSource
namespace OriginalWholeDebtRJointMobiusProgramme
open Complex MeasureTheory Set Filter BurnolPhysicalState
namespace J
export OriginalWholeDebtRJointMobiusSource (jointRaw jointMean sourceRaw)
end J
def fullSourceRaw (c : BurnolCompletedMellinCoordinate) : ℝ → ℂ :=
  burnolCenteredMobiusInverse (J.jointRaw c)

def outsideSourceRaw (c : BurnolCompletedMellinCoordinate) : ℝ → ℂ :=
  (symmetricInterval (4 : ℝ))ᶜ.indicator (fullSourceRaw c)

def sourceMean (c : BurnolCompletedMellinCoordinate) : ℂ :=
  ∫ u : ℝ in Ioi 0, (u : ℂ)⁻¹ * J.sourceRaw c u

def outsideResponseRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  burnolInnerGapForward (outsideSourceRaw c) x + J.jointMean c + sourceMean c

end OriginalWholeDebtRJointMobiusProgramme
namespace OriginalWholeDebtRJointMobiusUnitSource
open Complex MeasureTheory Set Filter BurnolPhysicalState
namespace J
export OriginalWholeDebtRJointMobiusSource (jointValue jointMean paWave)
end J
namespace Q
export OriginalWholeDebtRJointMobiusProgramme (outsideSourceRaw outsideResponseRaw sourceMean)
end Q
def actualGap (c : BurnolCompletedMellinCoordinate) : ℂ := J.jointMean c + Q.sourceMean c

def unitRaw (c : BurnolCompletedMellinCoordinate) : ℝ → ℂ := burnolRadiusUnitTailRaw c.value 4

def unitGap (c : BurnolCompletedMellinCoordinate) : ℂ := (4 : ℂ) ^ (-c.value) / c.value

def unitCoefficient (c : BurnolCompletedMellinCoordinate) : ℂ :=
  actualGap c * c.value * (4 : ℂ) ^ c.value

def sourceRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  Q.outsideSourceRaw c x - unitCoefficient c * unitRaw c x

def responseRaw (c : BurnolCompletedMellinCoordinate) : ℝ → ℂ :=
  burnolInnerGapForward (sourceRaw c)

abbrev canonicalRaw := sourceRaw
end OriginalWholeDebtRJointMobiusUnitSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
