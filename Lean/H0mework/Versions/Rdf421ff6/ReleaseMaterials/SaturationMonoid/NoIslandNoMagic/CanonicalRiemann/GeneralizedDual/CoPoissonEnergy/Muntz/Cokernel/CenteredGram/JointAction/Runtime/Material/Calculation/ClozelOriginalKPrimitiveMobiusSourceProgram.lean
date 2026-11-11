import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKPowerWaveSourceProgram
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.Lower
import H0mework.Arithmetic.MellinProjection.TailKernel

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPrimitiveMobiusSourceCalculation
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open OriginalRieszFinitePairing.CoPoisson.Ward

abbrev Value := OriginalKPowerWaveSourceCalculation.Value
abbrev Var := OriginalKPowerWaveSourceCalculation.Var
abbrev Base := OriginalKPowerWaveSourceCalculation.Base
abbrev Half := OriginalKPowerWaveSourceCalculation.Half
abbrev E := OriginalKPowerWaveSourceCalculation.E
abbrev sourceEnvironment := OriginalKPowerWaveSourceCalculation.sourceEnvironment
abbrev coordinate := OriginalKPowerWaveSourceCalculation.coordinate
abbrev conjugateCoordinate := OriginalPrimitiveRankBalance.conjugateCoordinate

open private linear scale sub fourier dilation from
  H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKPowerWaveSourceProgram

namespace Wave
export OriginalKPowerWaveSourceCalculation (profileCode fourierProfileCode)
end Wave
namespace Coefficient
export OriginalKBFiniteCalculation (coefficientAActionCode coefficientBetaActionCode)
end Coefficient
namespace Flux
export FiniteMobiusResolventFlux (M actualMean)
end Flux

def spread : ℝ := -Real.log 16
def sourceFactor (c : BurnolCompletedMellinCoordinate) : ℂ := (star c.value-c.value)/2

def primitiveIncrementCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) : E :=
  sub (scale (-1) (Coefficient.coefficientAActionCode c
    (Wave.profileCode (conjugateCoordinate c) h)))
    (Coefficient.coefficientBetaActionCode c
      (Wave.fourierProfileCode (conjugateCoordinate c) h))

def kernelIncrementCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) : E :=
  .add (Coefficient.coefficientAActionCode c (Wave.profileCode c h))
    (Coefficient.coefficientBetaActionCode c (Wave.fourierProfileCode c h))

def fourierKernelIncrementCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) : E :=
  fourier (kernelIncrementCode c (-h))

def fourierPrimitiveIncrementCode (c : BurnolCompletedMellinCoordinate) (h : ℝ) : E :=
  fourier (primitiveIncrementCode c (-h))

def fourierKernelCode (c : BurnolCompletedMellinCoordinate) : E :=
  fourier (OriginalKCoefficientBSelfCalculation.sourceKernelCode c)

/-- The tail functional receives the same actual Fourier-kernel subtree as the mean. -/
def tailRead (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] ℂ :=
  burnolRadiusMellinTailEvaluator (1/4 : ℝ) (by norm_num)
    (star (conjugateCoordinate c).value)
    (by simpa only [conjugateCoordinate,
      OriginalPrimitiveRankBalance.conjugateCoordinate, star_star] using c.rightHalf)

def constantUnitAction (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  (ContinuousLinearMap.toSpanSingleton ℂ
    (burnolQuarterZeroExtension (intervalConstant (1/4 : ℝ)))).comp
      (((2*sourceFactor c/(1-star (conjugateCoordinate c).value))-1) • Flux.actualMean)

def powerUnitAction (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  (ContinuousLinearMap.toSpanSingleton ℂ
    (burnolQuarterZeroExtension (SingularCounting.powerL2 (conjugateCoordinate c)))).comp
      ((-2*sourceFactor c) •
        (tailRead c+((1/4 : ℂ)^(1-star (conjugateCoordinate c).value)/
          (1-star (conjugateCoordinate c).value)) • Flux.actualMean))

/-- Both original quarter feet are computed before dilation and the complete Mobius action. -/
def unitCode (c : BurnolCompletedMellinCoordinate) : E :=
  .add (linear (constantUnitAction c) (fourierKernelCode c))
    (linear (powerUnitAction c) (fourierKernelCode c))

def mobiusCode (input : E) : E := linear Flux.M input

def code (c : BurnolCompletedMellinCoordinate) : Fin 3 → E :=
  ![scale (-1) (mobiusCode (primitiveIncrementCode c spread)),
    scale (-1) (mobiusCode (fourierKernelIncrementCode c spread)),
    sub (mobiusCode (dilation spread (unitCode c)))
      (mobiusCode (fourierPrimitiveIncrementCode c spread))]

theorem operation_budget (c : BurnolCompletedMellinCoordinate) (index : Fin 3) :
    0 < remaining (code c index) := by
  fin_cases index
  · change 0 < remaining (mobiusCode (primitiveIncrementCode c spread))+1
    omega
  · change 0 < remaining (mobiusCode (fourierKernelIncrementCode c spread))+1
    omega
  · change 0 < remaining (mobiusCode (dilation spread (unitCode c)))+
      (remaining (mobiusCode (fourierPrimitiveIncrementCode c spread))+1)+1
    omega

def reader (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
    (half : Half observation) (index : Fin 3) {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := Value) (Var := Var) (sort := ()) :=
  { environment := sourceEnvironment
    expression := code (coordinate observation nontrivial half occurrence) index }

theorem reader_source (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
    (half : Half observation) (index : Fin 3) {current : CanonicalUnitArithmeticRoot.V.Current}
    (occurrence : Base.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    (reader observation nontrivial half index occurrence).environment = sourceEnvironment ∧
      (coordinate observation nontrivial half occurrence).value = observation.coordinate ∧
      (reader observation nontrivial half index occurrence).expression =
        code (coordinate observation nontrivial half occurrence) index := ⟨rfl, rfl, rfl⟩

end OriginalKPrimitiveMobiusSourceCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
