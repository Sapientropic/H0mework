import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKPrimitiveMobiusSourceProgram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKPowerWaveSourceCalculation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandFiniteMaterial
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRPrimitiveMobiusFiniteSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPrimitiveMobiusSourceCalculation
open Complex BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open OriginalRieszSource OriginalRieszFiniteSource
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction

open private linear scale sub fourier dilation sub_eval from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKPowerWaveSourceProgram
open private coefficient_A_source_eval coefficient_beta_source_eval from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedBEulerJunctionSource.BandFiniteMaterial

theorem primitive_increment_code_value (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    (primitiveIncrementCode c h).eval sourceEnvironment =
      -(Kernel.A c) • profileIntegral (conjugateCoordinate c) h-
        Kernel.beta c • fourierProfileIntegral (conjugateCoordinate c) h := by
  rw [primitiveIncrementCode, sub_eval]
  change (-1 : ℂ) •
    (Coefficient.coefficientAActionCode c (Wave.profileCode (conjugateCoordinate c) h)).eval
      sourceEnvironment-
    (Coefficient.coefficientBetaActionCode c
      (Wave.fourierProfileCode (conjugateCoordinate c) h)).eval sourceEnvironment = _
  rw [coefficient_A_source_eval, coefficient_beta_source_eval,
    OriginalKPowerWaveSourceCalculation.profile_code_eval,
    OriginalKPowerWaveSourceCalculation.fourier_profile_code_eval]
  rw [smul_smul, neg_one_mul]

theorem kernel_increment_code_value (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    (kernelIncrementCode c h).eval sourceEnvironment = forcingIntegral c h := by
  change (Coefficient.coefficientAActionCode c (Wave.profileCode c h)).eval sourceEnvironment+
    (Coefficient.coefficientBetaActionCode c (Wave.fourierProfileCode c h)).eval sourceEnvironment = _
  rw [coefficient_A_source_eval, coefficient_beta_source_eval,
    OriginalKPowerWaveSourceCalculation.profile_code_eval,
    OriginalKPowerWaveSourceCalculation.fourier_profile_code_eval]
  rfl

theorem fourier_kernel_increment_code_value (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    (fourierKernelIncrementCode c h).eval sourceEnvironment = fourierL2 (forcingIntegral c (-h)) := by
  change fourierL2 ((kernelIncrementCode c (-h)).eval sourceEnvironment) = _
  rw [kernel_increment_code_value]

theorem fourier_primitive_increment_code_value (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    (fourierPrimitiveIncrementCode c h).eval sourceEnvironment =
      fourierL2 (-(Kernel.A c) • profileIntegral (conjugateCoordinate c) (-h)-
        Kernel.beta c • fourierProfileIntegral (conjugateCoordinate c) (-h)) := by
  change fourierL2 ((primitiveIncrementCode c (-h)).eval sourceEnvironment) = _
  rw [primitive_increment_code_value]

theorem fourier_kernel_code_value (c : BurnolCompletedMellinCoordinate) :
    (fourierKernelCode c).eval sourceEnvironment =
      fourierL2 (burnolCompletedMellinRieszVector c : BurnolL2) := by
  change fourierL2
    ((OriginalKCoefficientBSelfCalculation.sourceKernelCode c).eval sourceEnvironment) = _
  rw [OriginalKCoefficientBSelfCalculation.Semantics.kernel_code_eval, sourceKernel_original]

theorem tail_read_value (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    tailRead c value =
      OriginalKFiniteOrderRelease.UnitPowerJordanSource.sourceTail (conjugateCoordinate c) value := rfl

theorem unit_code_value (c : BurnolCompletedMellinCoordinate) :
    let kernel := fourierL2 (burnolCompletedMellinRieszVector c : BurnolL2)
    (unitCode c).eval sourceEnvironment =
      (((2*sourceFactor c/(1-star (conjugateCoordinate c).value))-1)*Flux.actualMean kernel) •
        burnolQuarterZeroExtension (intervalConstant (1/4 : ℝ))+
      ((-2*sourceFactor c)*(tailRead c kernel+
        ((1/4 : ℂ)^(1-star (conjugateCoordinate c).value)/
          (1-star (conjugateCoordinate c).value))*Flux.actualMean kernel)) •
        burnolQuarterZeroExtension (SingularCounting.powerL2 (conjugateCoordinate c)) := by
  change constantUnitAction c ((fourierKernelCode c).eval sourceEnvironment)+
    powerUnitAction c ((fourierKernelCode c).eval sourceEnvironment) = _
  rw [fourier_kernel_code_value]
  rfl

theorem position_code_value (c : BurnolCompletedMellinCoordinate) :
    (code c 0).eval sourceEnvironment =
      -Flux.M (-(Kernel.A c) • profileIntegral (conjugateCoordinate c) spread-
        Kernel.beta c • fourierProfileIntegral (conjugateCoordinate c) spread) := by
  change (-1 : ℂ) • Flux.M ((primitiveIncrementCode c spread).eval sourceEnvironment) = _
  rw [primitive_increment_code_value, neg_one_smul]

theorem fourier_code_value (c : BurnolCompletedMellinCoordinate) :
    (code c 1).eval sourceEnvironment = -Flux.M (fourierL2 (forcingIntegral c (-spread))) := by
  change (-1 : ℂ) • Flux.M ((fourierKernelIncrementCode c spread).eval sourceEnvironment) = _
  rw [fourier_kernel_increment_code_value, neg_one_smul]

theorem power_code_value (c : BurnolCompletedMellinCoordinate) :
    (code c 2).eval sourceEnvironment =
      Flux.M (burnolMultiplicativeDilation spread ((unitCode c).eval sourceEnvironment))-
        Flux.M (fourierL2 (-(Kernel.A c) • profileIntegral (conjugateCoordinate c) (-spread)-
          Kernel.beta c • fourierProfileIntegral (conjugateCoordinate c) (-spread))) := by
  change (sub (mobiusCode (dilation spread (unitCode c)))
    (mobiusCode (fourierPrimitiveIncrementCode c spread))).eval sourceEnvironment = _
  rw [sub_eval]
  change Flux.M (burnolMultiplicativeDilation spread ((unitCode c).eval sourceEnvironment))-
    Flux.M ((fourierPrimitiveIncrementCode c spread).eval sourceEnvironment) = _
  rw [fourier_primitive_increment_code_value]

namespace Math
export OriginalWholeDebtRPrimitiveMobiusSource
  (spread primitiveIncrement fourierKernelIncrement kernelWindowSource
   primitiveQuarterConstant primitiveUnitCoefficient primitiveUnitWindow
   fourierPrimitiveIncrement fourierPrimitiveWindowSource spread_flat_zero)
end Math

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

theorem unit_code_field :
    (unitCode c).eval sourceEnvironment =
      Math.primitiveQuarterConstant observation nontrivial half •
        burnolQuarterZeroExtension (intervalConstant (1/4 : ℝ))+
      Math.primitiveUnitCoefficient observation nontrivial half •
        burnolQuarterZeroExtension (SingularCounting.powerL2 (conjugateCoordinate c)) := by
  have factor : sourceFactor c=FiniteMobiusResolventFlux.sourceA observation := by
    unfold sourceFactor FiniteMobiusResolventFlux.sourceA
    rw [OriginalKCombCofinalTwoDirection.coordinate_value]
  have sameKernel : (burnolCompletedMellinRieszVector c : BurnolL2)=
      OriginalKCombCofinalTwoDirection.originalK observation nontrivial half := rfl
  rw [unit_code_value]
  rw [sameKernel, tail_read_value, factor]
  unfold Math.primitiveQuarterConstant Math.primitiveUnitCoefficient
  simp only [conjugateCoordinate]
  push_cast
  congr 1 <;> congr 1 <;> ring

/-- All three runtime fields retain their source programs and the complete original power unit. -/
theorem actual_code_field (index : Fin 3) :
    (code c index).eval sourceEnvironment =
      ![-Flux.M (Math.primitiveIncrement observation nontrivial half Math.spread),
        Math.kernelWindowSource observation nontrivial half,
        Math.fourierPrimitiveWindowSource observation nontrivial half] index := by
  fin_cases index
  · change (code c 0).eval sourceEnvironment =
      -Flux.M (Math.primitiveIncrement observation nontrivial half Math.spread)
    exact position_code_value c
  · change (code c 1).eval sourceEnvironment = Math.kernelWindowSource observation nontrivial half
    exact fourier_code_value c
  · have constantZero : Flux.M (burnolMultiplicativeDilation spread
        (burnolQuarterZeroExtension (intervalConstant (1/4 : ℝ))))=0 := Math.spread_flat_zero
      (burnolQuarterZeroExtension (intervalConstant (1/4 : ℝ))) 1
      (by rw [burnolQuarterRestriction_zeroExtension, one_smul])
    have unitWindow :
        Flux.M (burnolMultiplicativeDilation spread ((unitCode c).eval sourceEnvironment)) =
          Math.primitiveUnitCoefficient observation nontrivial half •
            Flux.M (Math.primitiveUnitWindow observation nontrivial half) := by
      rw [unit_code_field, map_add, map_smul, map_smul, map_add, map_smul, map_smul,
        constantZero, smul_zero, zero_add]
      rfl
    change (code c 2).eval sourceEnvironment =
      Math.fourierPrimitiveWindowSource observation nontrivial half
    rw [power_code_value, unitWindow]
    rfl

end OriginalKPrimitiveMobiusSourceCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
