import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRReciprocalCotestSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceBalance.Actual

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRPrimitiveMobiusSource
open Complex MeasureTheory Set FourierTransform BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalWholeDebtRPowerWaveDilationSource OriginalKSourceResolventReconstruction
open scoped InnerProductSpace BigOperators FourierTransform
namespace Flux
export FiniteMobiusResolventFlux
  (M D Rplus sourceA primitiveSource defectForcing defectFlux coefficient actualMean
   lowerPullback lowerWindow Window lower_source_cutoff lower_window_read
   original_return_source_equation)
end Flux
namespace F
export FiniteMobiusResolventFlux (cutoff box fullPullback)
end F
open private actual_R_euler from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRReciprocalCotestSource
open private mean_smul mean_constant from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcingGapAction.Source
local notation "DT" => TemperedDistribution ℝ ℂ
local notation "FL" => fourierL2
local notation "Tate" => burnolTateReciprocalL2
local notation "q" => (1/4 : ℝ)
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "p" => Flux.primitiveSource observation nontrivial half
local notation "K" => OriginalKCombCofinalTwoDirection.originalK observation nontrivial half
local notation "aa" => Flux.sourceA observation

/-- The original source p, without a replacement primitive or a global L2 bulk assumption. -/
theorem primitive_euler :
    GapEuler.euler (p : DT) + frequency c • (p : DT) =
      -(Kernel.A c • Response.Psi + Kernel.beta c • 𝓕 Response.Psi) := by
  have source := Flux.original_return_source_equation observation nontrivial half
  have acted := actual_R_euler c K
  have kernel := Kernel.original_kernel_euler c
  have parameter := OriginalKCombCofinalTwoDirection.coordinate_value observation nontrivial half
  rw [OriginalKCombCofinalRAction.original_R_direct] at source
  change aa • burnolDirectRightResolventCLM c K - K = p at source
  have same : K = (burnolCompletedMellinRieszVector c : BurnolL2) := rfl
  rw [←same] at kernel
  rw [←source]
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2
      (aa • burnolDirectRightResolventCLM c K-K)) + frequency c •
      Lp.toTemperedDistributionCLM ℂ volume 2 (aa • burnolDirectRightResolventCLM c K-K) = _
  simp only [map_sub, map_smul, Lp.toTemperedDistributionCLM_apply]
  have scalar : aa = (star observation.coordinate-observation.coordinate)/2 := rfl
  rw [scalar]
  simp only [frequency, parameter] at acted ⊢
  rw [parameter] at kernel
  linear_combination (norm := module)
    ((star observation.coordinate-observation.coordinate)/2) • acted-kernel

theorem primitive_fourier_euler :
    GapEuler.euler (FL p : DT) - frequency c • (FL p : DT) =
      Kernel.A c • 𝓕 Response.Psi + Kernel.beta c • 𝓕 (𝓕 Response.Psi) := by
  have generated := congrArg (fun value : DT => 𝓕 value)
    (primitive_euler observation nontrivial half)
  have read : 𝓕 (p : DT) = (FL p : DT) := Lp.fourier_toTemperedDistribution_eq _
  simp only [FourierAdd.fourier_add, FourierSMul.fourier_smul, FourierTransform.fourier_neg,
    read] at generated
  have anti := GapEuler.euler_fourier (p : DT)
  rw [read] at anti
  linear_combination (norm := module) anti-generated

private theorem mean_of_gap (value : BurnolL2) (k : ℂ)
    (gap : burnolQuarterRestriction value=k • intervalConstant q) :
    Flux.actualMean value=k := by
  have normalized : Flux.actualMean value=
      burnolQuarterMeanCoefficient (burnolQuarterRestriction value) := by
    change (‖intervalConstant q‖^2 : ℂ)⁻¹ *
      inner ℂ (intervalConstant q) (burnolQuarterRestriction value)=
        inner ℂ (intervalConstant q) (burnolQuarterRestriction value)/
          ((‖intervalConstant q‖^2 : ℝ) : ℂ)
    rw [Complex.ofReal_pow]
    ring
  rw [normalized,gap,mean_smul,mean_constant,mul_one]

private theorem inward_gap (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (k : ℂ)
    (gap : burnolQuarterRestriction value=k • intervalConstant q) :
    burnolQuarterRestriction (burnolDirectRightResolventCLM coordinate value)=
      (-2*k/coordinate.value) • intervalConstant q := by
  have right : 1/4<(coordinate.value/2).re := by
    rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
  have actual:=OriginalKForcingGapAction.right_resolvent_quarter_constant
    (coordinate.value/2) right value k gap
  change burnolQuarterRestriction (burnolDirectRightResolventCLM coordinate value)=_ at actual
  rw [actual]
  congr 1
  ring

/-- This is the original p's computed constant gap, with its actual source mean. -/
theorem primitive_quarter :
    burnolQuarterRestriction p=Flux.actualMean p • intervalConstant q := by
  let kg:=burnolConstantGapCoefficient q (burnolCompletedMellinRieszVector c)
  have kernelGap : burnolQuarterRestriction K=kg • intervalConstant q :=
    (burnolGenericPhysicalValue_gap (burnolCompletedMellinRieszVector c)).symm
  have acted:=inward_gap c K kg kernelGap
  have source:=Flux.original_return_source_equation observation nontrivial half
  rw [OriginalKCombCofinalRAction.original_R_direct] at source
  change aa • burnolDirectRightResolventCLM c K-K=p at source
  have gap : burnolQuarterRestriction p=
      (aa*(-2*kg/(OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value)-kg) • intervalConstant q := by
    rw [←source,map_sub,map_smul,acted,kernelGap,smul_smul,←sub_smul]
  rw [mean_of_gap p _ gap]
  exact gap


end OriginalWholeDebtRPrimitiveMobiusSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
