import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRPrimitiveMobiusWindowSource

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
open private profile_action from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRPowerWaveDilationSource
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

/-- The input is the paid universal Psi source, not p or an M-value. -/
def primitiveIncrement (h : ℝ) : BurnolL2 :=
  -(Kernel.A c) • OriginalRieszFiniteSource.profileIntegral
    (OriginalPrimitiveRankBalance.conjugateCoordinate c) h-
  Kernel.beta c • OriginalRieszFiniteSource.fourierProfileIntegral
    (OriginalPrimitiveRankBalance.conjugateCoordinate c) h

def primitivePhase (h : ℝ) : ℂ := Complex.exp (-frequency c*(h : ℂ))

theorem primitive_finite_source (h : ℝ) :
    burnolMultiplicativeDilation h p=primitivePhase observation nontrivial half h • p+
      primitiveIncrement observation nontrivial half h := by
  have original:=primitive_euler observation nontrivial half
  have action:=profile_action (OriginalPrimitiveRankBalance.conjugateCoordinate c) p
    (-(Kernel.A c)) (-(Kernel.beta c))
    (by
      simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]
      unfold frequency at original
      linear_combination (norm := module) original) h
  simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star] at action
  unfold primitivePhase primitiveIncrement frequency
  simp only [OriginalPrimitiveRankBalance.conjugateCoordinate]
  linear_combination (norm := module) action

/-- All fifteen original slots are retained; the actual increment pays the whole M field. -/
theorem primitive_window_source :
    primitivePhase observation nontrivial half spread • Flux.M p=
      -Flux.M (primitiveIncrement observation nontrivial half spread) := by
  have empty:=spread_flat_zero p (Flux.actualMean p) (primitive_quarter observation nontrivial half)
  have action:=congrArg Flux.M (primitive_finite_source observation nontrivial half spread)
  rw [map_add,map_smul,empty] at action
  exact eq_neg_of_add_eq_zero_left action.symm


/-- The true Fourier/negative-time action of the original K source. -/
def fourierKernelIncrement (h : ℝ) : BurnolL2 :=
  FL (OriginalRieszFiniteSource.forcingIntegral c (-h))
def fourierKernelPhase (h : ℝ) : ℂ :=
  fullMellinTranslationCharacter (star observation.coordinate) (-h)

theorem fourier_kernel_finite_source (h : ℝ) :
    burnolMultiplicativeDilation h (FL K)=fourierKernelPhase observation h • FL K+
      fourierKernelIncrement observation nontrivial half h := by
  have source:=OriginalRieszFiniteSource.original_finite_action c (-h)
  have action:=congrArg FL source
  simp only [map_add,map_smul,fourierL2_burnolMultiplicativeDilation,neg_neg] at action
  have literal:=OriginalKCombCofinalTwoDirection.coordinate_value observation nontrivial half
  rw [literal] at action
  exact action

/-- No original MFK bulk is an input to this source constructor. -/
def kernelWindowSource : BurnolL2 :=
  -Flux.M (fourierKernelIncrement observation nontrivial half spread)

theorem fourier_kernel_window_source :
    fourierKernelPhase observation spread • Flux.M (FL K)=
      kernelWindowSource observation nontrivial half := by
  have empty:=spread_flat_zero (FL K) (Flux.actualMean (FL K))
    (fourier_kernel_quarter observation nontrivial half)
  have action:=congrArg Flux.M (fourier_kernel_finite_source observation nontrivial half spread)
  rw [map_add,map_smul,empty] at action
  exact eq_neg_of_add_eq_zero_left action.symm

namespace J
export OriginalKFiniteOrderRelease.UnitPowerJordanSource
  (sourceStep sourceTail source_quarter_step quarterStep_constant)
end J

/-- The original Fourier tail remains the L2 power unit, with no Pa assumption. -/
def primitiveUnitCoefficient : ℂ :=
  aa*(-2*(J.sourceTail (OriginalPrimitiveRankBalance.conjugateCoordinate c) (FL K)+
    Flux.actualMean (FL K)*(q : ℂ)^(1-star (OriginalPrimitiveRankBalance.conjugateCoordinate c).value)/
      (1-star (OriginalPrimitiveRankBalance.conjugateCoordinate c).value)))
def primitiveQuarterConstant : ℂ :=
  aa*(2*Flux.actualMean (FL K)/(1-star (OriginalPrimitiveRankBalance.conjugateCoordinate c).value))-
    Flux.actualMean (FL K)

theorem primitive_fourier_quarter :
    burnolQuarterRestriction (FL p)=
      primitiveQuarterConstant observation nontrivial half • intervalConstant q+
        primitiveUnitCoefficient observation nontrivial half •
          SingularCounting.powerL2 (OriginalPrimitiveRankBalance.conjugateCoordinate c) := by
  have kernelEven : reflectL2 K=K :=
    mem_evenL2ClosedFace_iff.mp (burnolCompletedMellinRieszVector c).property.2
  have fourierEven : reflectL2 (FL K)=FL K := by
    rw [←fourierL2_reflectL2_commute,kernelEven]
  have quarter:=J.source_quarter_step (OriginalPrimitiveRankBalance.conjugateCoordinate c)
    (FL K) fourierEven
  rw [fourier_kernel_quarter,map_smul,J.quarterStep_constant] at quarter
  have starRight : 1/4<(star (OriginalPrimitiveRankBalance.conjugateCoordinate c).value/2).re := by
    simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]
    rw [Complex.div_re];norm_num;linarith [(OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf]
  have native : Flux.Rplus (star (OriginalPrimitiveRankBalance.conjugateCoordinate c).value/2) (FL K)=
      J.sourceStep (OriginalPrimitiveRankBalance.conjugateCoordinate c) (FL K) :=
    FiniteMobiusResolventFlux.Rplus_tate _ starRight _
  have literal:=OriginalKCombCofinalTwoDirection.coordinate_value observation nontrivial half
  have originalParameter : star (OriginalPrimitiveRankBalance.conjugateCoordinate c).value=
      observation.coordinate := by
    simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star,literal]
  rw [originalParameter] at native
  have source:=Flux.original_return_source_equation observation nontrivial half
  rw [OriginalKCombCofinalRAction.original_R_direct] at source
  have transformed:=congrArg FL source
  simp only [map_smul,map_sub] at transformed
  rw [FiniteMobiusResolventFlux.fourier_R _
    (OriginalKCombCofinalRAction.parameter_rightQuarter observation half),native] at transformed
  have quarters:=congrArg burnolQuarterRestriction transformed
  simp only [map_sub,map_smul] at quarters
  rw [quarter,fourier_kernel_quarter] at quarters
  rw [←quarters]
  unfold primitiveQuarterConstant primitiveUnitCoefficient
  module

/-- This full unit is generated from the original admissible quarter power and dilation. -/
def primitiveUnitWindow : BurnolL2 :=
  burnolMultiplicativeDilation spread (burnolQuarterZeroExtension
    (SingularCounting.powerL2 (OriginalPrimitiveRankBalance.conjugateCoordinate c)))

def fourierPrimitiveIncrement (h : ℝ) : BurnolL2 :=
  FL (primitiveIncrement observation nontrivial half (-h))
def fourierPrimitivePhase (h : ℝ) : ℂ :=
  primitivePhase observation nontrivial half (-h)

theorem fourier_primitive_finite_source (h : ℝ) :
    burnolMultiplicativeDilation h (FL p)=
      fourierPrimitivePhase observation nontrivial half h • FL p+
        fourierPrimitiveIncrement observation nontrivial half h := by
  have source:=congrArg FL (primitive_finite_source observation nontrivial half (-h))
  simp only [map_add,map_smul,fourierL2_burnolMultiplicativeDilation,neg_neg] at source
  exact source

/-- Native unit plus whole Psi source; the original MFp field is not a constructor input. -/
def fourierPrimitiveWindowSource : BurnolL2 :=
  primitiveUnitCoefficient observation nontrivial half • Flux.M (primitiveUnitWindow observation nontrivial half)-
    Flux.M (fourierPrimitiveIncrement observation nontrivial half spread)

theorem fourier_primitive_window_source :
    fourierPrimitivePhase observation nontrivial half spread • Flux.M (FL p)=
      fourierPrimitiveWindowSource observation nontrivial half := by
  have base:=spread_flat_zero (burnolQuarterZeroExtension (intervalConstant q)) 1
    (by rw [burnolQuarterRestriction_zeroExtension,one_smul])
  have actual : Flux.M (burnolMultiplicativeDilation spread (FL p))=
      primitiveUnitCoefficient observation nontrivial half • Flux.M (primitiveUnitWindow observation nontrivial half) := by
    rw [window_spread,primitive_fourier_quarter,map_add,map_smul,map_smul,map_add,
      map_smul,map_smul,map_add,map_smul,map_smul,base,smul_zero,zero_add]
    rfl
  have action:=congrArg Flux.M (fourier_primitive_finite_source observation nontrivial half spread)
  rw [map_add,map_smul,actual] at action
  exact eq_sub_of_add_eq action.symm

/-- These are explicit source units; no original arithmetic multiplier is divided. -/
def returnPhase : ℂ :=
  primitivePhase observation nontrivial half spread*fourierKernelPhase observation spread*
    fourierPrimitivePhase observation nontrivial half spread

theorem return_phase_ne_zero : returnPhase observation nontrivial half≠0 := by
  unfold returnPhase primitivePhase fourierKernelPhase fourierPrimitivePhase
    fullMellinTranslationCharacter
  exact mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))
    (Complex.exp_ne_zero _)


end OriginalWholeDebtRPrimitiveMobiusSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
