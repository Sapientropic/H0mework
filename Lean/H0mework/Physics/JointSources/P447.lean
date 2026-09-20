import H0mework.Physics.SourceForms.P446

/-!
# Proposition 447: irreducible grand-unification producer kernel

P445/P446 show that all current grand-unification front doors are equivalent:
central constants, the SU(7)-resolved opened synthesis surface, the raw
matrix-only producer, and the single-source receipt all name one remaining
existence problem.

This file turns the bottom SU(7)-resolved surface into one explicit record.
That is the current "holy grail" front door in its least ambiguous form:
to inhabit it, a proof must supply the generated 19-slot surface, completeness,
Yukawa consolidation law, RG flow, CKM/H¹ calculation, pinned constants,
running sigma, selected seed, sampled Yukawa clocks, and the physical sigma
corridor.  No physical instance is manufactured here.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

namespace GrandUnificationProducerNormalForm

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-! ## One-record producer kernel -/

/-- The irreducible producer kernel for the current grand-unification target.

This is P444's SU(7)-resolved front door as a single record instead of a long
nested existential.  The SU(7) breaking field has already been supplied by
`canonicalSU7SectorBreakingChain`; all remaining fields are genuine producer
obligations. -/
structure IrreducibleGrandUnificationProducerKernel
    (Index A CKMCarrier : Type*) [AddCommGroup A] where
  generated : DiscreteStandardModelSeed -> ParameterVector ℝ
  constraints : ParameterVector ℝ -> Prop
  generated_satisfies :
    ∀ seed : DiscreteStandardModelSeed, constraints (generated seed)
  complete :
    ∀ p : ParameterVector ℝ, constraints p -> ∃ seed, generated seed = p
  yukawaLaw : ConsolidationYukawaLaw DiscreteStandardModelSeed ℝ
  yukawa_generated :
    ∀ seed y,
      generated seed (yukawaSlot y) =
        yukawaLaw.depthToYukawa y (yukawaLaw.depth seed y)
  rg : RenormalizationGroupFlow StandardModelScaleCode ℝ
  rg_preserves_constraints :
    ∀ s p, constraints p -> constraints (rg.evolve s p)
  ckm : CKMCohomologyCalculation Index A ℝ CKMCarrier
  ckmInput : DiscreteStandardModelSeed -> CKMCarrier
  ckm_generated :
    ∀ seed a, generated seed (ckmSlot a) = ckm.angle (ckmInput seed) a
  gutWeakMixingSquared : ParameterVector ℝ -> ℝ
  thetaQCD_zero :
    ∀ seed : DiscreteStandardModelSeed,
      generated seed StandardModelParameter.qcd_theta = 0
  gutWeakMixingSquared_eq_threeEighths :
    ∀ seed : DiscreteStandardModelSeed,
      gutWeakMixingSquared (generated seed) = threeEighths ℝ
  yukawaAmplitude : YukawaParameter -> ℝ
  yukawaSigma : DiscreteStandardModelSeed -> YukawaParameter -> ℝ
  yukawaExponent : DiscreteStandardModelSeed -> YukawaParameter -> Nat
  yukawa_residual_power :
    ∀ seed y,
      generated seed (yukawaSlot y) =
        yukawaAmplitude y *
          (((1 : ℝ) - yukawaSigma seed y) ^ yukawaExponent seed y)
  gutScale : StandardModelScaleCode
  weakScale : StandardModelScaleCode
  sigma : StandardModelScaleCode -> ℝ
  gaugeCoupling : StandardModelScaleCode -> ℝ
  fourPi : ℝ
  sigma_eq_alpha :
    ∀ scale : StandardModelScaleCode,
      sigma scale = alphaFromGaugeCoupling fourPi (gaugeCoupling scale)
  sigma_gut_nominal : sigma gutScale = sigmaGUTNominal ℝ
  sigma_weak_nominal : sigma weakScale = sigmaWeakNominal ℝ
  higgsLambdaAtGUT : DiscreteStandardModelSeed -> ℝ
  higgsLambdaAtGUT_eq_rg_slot :
    ∀ seed : DiscreteStandardModelSeed,
      higgsLambdaAtGUT seed =
        rg.evolve gutScale (generated seed) StandardModelParameter.higgs_lambda
  higgsLambdaAtGUT_zero :
    ∀ seed : DiscreteStandardModelSeed, higgsLambdaAtGUT seed = 0
  approx : ℝ -> ℝ -> Prop
  higgsLambdaAtGUT_near_sigmaCriticalProxy :
    ∀ seed : DiscreteStandardModelSeed,
      approx (higgsLambdaAtGUT seed)
        (sigmaCriticalProxy (sigma gutScale))
  yukawaScale :
    DiscreteStandardModelSeed -> YukawaParameter -> StandardModelScaleCode
  yukawaSigma_is_runningSigma :
    ∀ seed y, yukawaSigma seed y = sigma (yukawaScale seed y)
  selectedSeed : DiscreteStandardModelSeed
  constraints_exact_selected :
    ∀ p : ParameterVector ℝ, constraints p <-> p = generated selectedSeed
  gutScale_is_gut : gutScale = StandardModelScaleCode.gut
  weakScale_is_weak : weakScale = StandardModelScaleCode.weak
  selected_yukawaScale_is_discrete :
    ∀ y : YukawaParameter,
      yukawaScale selectedSeed y = StandardModelScaleCode.yukawa y
  alphaEM : ℝ
  alphaEM_integerConstraint : alphaEM = alphaEMFromIntegerConstraint ℝ
  yukawaLambda : YukawaParameter -> ℝ
  yukawaStep : YukawaParameter -> ℝ
  selected_yukawa_sigma_sampled :
    ∀ y : YukawaParameter,
      sigma (StandardModelScaleCode.yukawa y) =
        AffineRelaxation.realDecayRate (yukawaLambda y) (yukawaStep y)
  fourPi_eq_realFourPi : fourPi = realFourPi
  selected_yukawa_sigma_le_weak :
    ∀ y : YukawaParameter,
      sigma (StandardModelScaleCode.yukawa y) ≤
        sigma StandardModelScaleCode.weak

namespace IrreducibleGrandUnificationProducerKernel

/-- Reassemble the kernel's bottom fields into P273's synthesis certificate,
using P444's concrete SU(7) sector chain. -/
noncomputable def toBaseSynthesis
    (K : IrreducibleGrandUnificationProducerKernel Index A CKMCarrier) :
    StandardModelConstraintSynthesisCertificate
      DiscreteStandardModelSeed StandardModelScaleCode Index A ℝ CKMCarrier
    where
  su7 := canonicalSU7SectorBreakingChain
  generated := K.generated
  constraints := K.constraints
  generated_satisfies := K.generated_satisfies
  complete := K.complete
  yukawaLaw := K.yukawaLaw
  yukawa_generated := K.yukawa_generated
  rg := K.rg
  rg_preserves_constraints := K.rg_preserves_constraints
  ckm := K.ckm
  ckmInput := K.ckmInput
  ckm_generated := K.ckm_generated

/-- Reassemble the kernel as P378's primitive producer atoms. -/
noncomputable def toPrimitiveAtoms
    (K : IrreducibleGrandUnificationProducerKernel Index A CKMCarrier) :
    GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier
    where
  base := K.toBaseSynthesis
  gutWeakMixingSquared := K.gutWeakMixingSquared
  thetaQCD_zero := K.thetaQCD_zero
  gutWeakMixingSquared_eq_threeEighths :=
    K.gutWeakMixingSquared_eq_threeEighths
  yukawaAmplitude := K.yukawaAmplitude
  yukawaSigma := K.yukawaSigma
  yukawaExponent := K.yukawaExponent
  yukawa_residual_power := K.yukawa_residual_power
  gutScale := K.gutScale
  weakScale := K.weakScale
  sigma := K.sigma
  gaugeCoupling := K.gaugeCoupling
  fourPi := K.fourPi
  sigma_eq_alpha := K.sigma_eq_alpha
  sigma_gut_nominal := K.sigma_gut_nominal
  sigma_weak_nominal := K.sigma_weak_nominal
  higgsLambdaAtGUT := K.higgsLambdaAtGUT
  higgsLambdaAtGUT_eq_rg_slot := K.higgsLambdaAtGUT_eq_rg_slot
  higgsLambdaAtGUT_zero := K.higgsLambdaAtGUT_zero
  approx := K.approx
  higgsLambdaAtGUT_near_sigmaCriticalProxy :=
    K.higgsLambdaAtGUT_near_sigmaCriticalProxy
  yukawaScale := K.yukawaScale
  yukawaSigma_is_runningSigma := K.yukawaSigma_is_runningSigma
  selectedSeed := K.selectedSeed
  constraints_exact_selected := K.constraints_exact_selected
  gutScale_is_gut := K.gutScale_is_gut
  weakScale_is_weak := K.weakScale_is_weak
  selected_yukawaScale_is_discrete := K.selected_yukawaScale_is_discrete
  alphaEM := K.alphaEM
  alphaEM_integerConstraint := K.alphaEM_integerConstraint
  yukawaLambda := K.yukawaLambda
  yukawaStep := K.yukawaStep
  selected_yukawa_sigma_sampled := K.selected_yukawa_sigma_sampled

/-- THEOREM 1: an irreducible kernel supplies the naked primitive front door. -/
theorem supplies_nakedPrimitive
    (K : IrreducibleGrandUnificationProducerKernel Index A CKMCarrier) :
    ExistsNakedPrimitiveAtomNativeSigmaCorridor Index A CKMCarrier := by
  exact
    ⟨K.toPrimitiveAtoms,
      K.fourPi_eq_realFourPi,
      K.selected_yukawa_sigma_le_weak⟩

end IrreducibleGrandUnificationProducerKernel

/-! ## Equivalence with the current front doors -/

/-- THEOREM 2: P444's SU(7)-resolved front door is exactly nonemptiness of
the irreducible producer kernel. -/
theorem su7Resolved_iff_irreducibleProducerKernel :
    ExistsSU7ResolvedProducerRelativeHolyGrailFrontDoor Index A CKMCarrier ↔
      Nonempty
        (IrreducibleGrandUnificationProducerKernel Index A CKMCarrier) := by
  constructor
  · rintro ⟨generated, constraints, generated_satisfies, complete,
      yukawaLaw, yukawa_generated, rg, rg_preserves_constraints,
      ckm, ckmInput, ckm_generated, gutWeakMixingSquared,
      thetaQCD_zero, gutWeakMixingSquared_eq_threeEighths,
      yukawaAmplitude, yukawaSigma, yukawaExponent, yukawa_residual_power,
      gutScale, weakScale, sigma, gaugeCoupling, fourPi, sigma_eq_alpha,
      sigma_gut_nominal, sigma_weak_nominal, higgsLambdaAtGUT,
      higgsLambdaAtGUT_eq_rg_slot, higgsLambdaAtGUT_zero, approx,
      higgsLambdaAtGUT_near_sigmaCriticalProxy, yukawaScale,
      yukawaSigma_is_runningSigma, selectedSeed, constraints_exact_selected,
      gutScale_is_gut, weakScale_is_weak, selected_yukawaScale_is_discrete,
      alphaEM, alphaEM_integerConstraint, yukawaLambda, yukawaStep,
      selected_yukawa_sigma_sampled, fourPi_eq_realFourPi,
      selected_yukawa_sigma_le_weak⟩
    exact
      ⟨{ generated := generated
         constraints := constraints
         generated_satisfies := generated_satisfies
         complete := complete
         yukawaLaw := yukawaLaw
         yukawa_generated := yukawa_generated
         rg := rg
         rg_preserves_constraints := rg_preserves_constraints
         ckm := ckm
         ckmInput := ckmInput
         ckm_generated := ckm_generated
         gutWeakMixingSquared := gutWeakMixingSquared
         thetaQCD_zero := thetaQCD_zero
         gutWeakMixingSquared_eq_threeEighths :=
           gutWeakMixingSquared_eq_threeEighths
         yukawaAmplitude := yukawaAmplitude
         yukawaSigma := yukawaSigma
         yukawaExponent := yukawaExponent
         yukawa_residual_power := yukawa_residual_power
         gutScale := gutScale
         weakScale := weakScale
         sigma := sigma
         gaugeCoupling := gaugeCoupling
         fourPi := fourPi
         sigma_eq_alpha := sigma_eq_alpha
         sigma_gut_nominal := sigma_gut_nominal
         sigma_weak_nominal := sigma_weak_nominal
         higgsLambdaAtGUT := higgsLambdaAtGUT
         higgsLambdaAtGUT_eq_rg_slot := higgsLambdaAtGUT_eq_rg_slot
         higgsLambdaAtGUT_zero := higgsLambdaAtGUT_zero
         approx := approx
         higgsLambdaAtGUT_near_sigmaCriticalProxy :=
           higgsLambdaAtGUT_near_sigmaCriticalProxy
         yukawaScale := yukawaScale
         yukawaSigma_is_runningSigma := yukawaSigma_is_runningSigma
         selectedSeed := selectedSeed
         constraints_exact_selected := constraints_exact_selected
         gutScale_is_gut := gutScale_is_gut
         weakScale_is_weak := weakScale_is_weak
         selected_yukawaScale_is_discrete :=
           selected_yukawaScale_is_discrete
         alphaEM := alphaEM
         alphaEM_integerConstraint := alphaEM_integerConstraint
         yukawaLambda := yukawaLambda
         yukawaStep := yukawaStep
         selected_yukawa_sigma_sampled := selected_yukawa_sigma_sampled
         fourPi_eq_realFourPi := fourPi_eq_realFourPi
         selected_yukawa_sigma_le_weak := selected_yukawa_sigma_le_weak }⟩
  · rintro ⟨K⟩
    exact
      ⟨K.generated, K.constraints, K.generated_satisfies, K.complete,
        K.yukawaLaw, K.yukawa_generated, K.rg, K.rg_preserves_constraints,
        K.ckm, K.ckmInput, K.ckm_generated, K.gutWeakMixingSquared,
        K.thetaQCD_zero, K.gutWeakMixingSquared_eq_threeEighths,
        K.yukawaAmplitude, K.yukawaSigma, K.yukawaExponent,
        K.yukawa_residual_power, K.gutScale, K.weakScale, K.sigma,
        K.gaugeCoupling, K.fourPi, K.sigma_eq_alpha, K.sigma_gut_nominal,
        K.sigma_weak_nominal, K.higgsLambdaAtGUT,
        K.higgsLambdaAtGUT_eq_rg_slot, K.higgsLambdaAtGUT_zero, K.approx,
        K.higgsLambdaAtGUT_near_sigmaCriticalProxy, K.yukawaScale,
        K.yukawaSigma_is_runningSigma, K.selectedSeed,
        K.constraints_exact_selected, K.gutScale_is_gut, K.weakScale_is_weak,
        K.selected_yukawaScale_is_discrete, K.alphaEM,
        K.alphaEM_integerConstraint, K.yukawaLambda, K.yukawaStep,
        K.selected_yukawa_sigma_sampled, K.fourPi_eq_realFourPi,
        K.selected_yukawa_sigma_le_weak⟩

/-- THEOREM 3: the current central holy-grail constants are exactly
nonemptiness of the irreducible producer kernel. -/
theorem currentCentralHolyGrailConstants_iff_irreducibleProducerKernel :
    CurrentFormalExactGeometryCentralHolyGrailConstants Index A CKMCarrier ↔
      Nonempty
        (IrreducibleGrandUnificationProducerKernel Index A CKMCarrier) := by
  exact
    (currentFormalExactGeometryCentralHolyGrailConstants_iff_su7Resolved
      (Index := Index) (A := A) (CKMCarrier := CKMCarrier)).trans
      (su7Resolved_iff_irreducibleProducerKernel
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier))

/-- THEOREM 4: the irreducible kernel is equivalent to the single-source
physical holy-grail receipt. -/
theorem irreducibleProducerKernel_iff_singleSourcePhysicalHolyGrailReceipt :
    Nonempty
        (IrreducibleGrandUnificationProducerKernel Index A CKMCarrier) ↔
      Nonempty
        (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
          Index A CKMCarrier) := by
  exact
    (su7Resolved_iff_irreducibleProducerKernel
      (Index := Index) (A := A) (CKMCarrier := CKMCarrier)).symm.trans
      (su7Resolved_iff_singleSourcePhysicalHolyGrailReceipt
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier))

/-- THEOREM 5: compact final front-door package.  The present grand-unification
target has one remaining Lean obligation: inhabit the irreducible producer
kernel. -/
theorem currentGrandUnificationFrontDoor_irreducibleKernelPackage :
    (CurrentFormalExactGeometryCentralHolyGrailConstants
        Index A CKMCarrier ↔
      Nonempty
        (IrreducibleGrandUnificationProducerKernel Index A CKMCarrier)) ∧
    (ExistsSU7ResolvedProducerRelativeHolyGrailFrontDoor
        Index A CKMCarrier ↔
      Nonempty
        (IrreducibleGrandUnificationProducerKernel Index A CKMCarrier)) ∧
    (Nonempty
        (IrreducibleGrandUnificationProducerKernel Index A CKMCarrier) ↔
      Nonempty
        (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
          Index A CKMCarrier)) := by
  exact
    ⟨currentCentralHolyGrailConstants_iff_irreducibleProducerKernel
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier),
      su7Resolved_iff_irreducibleProducerKernel
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier),
      irreducibleProducerKernel_iff_singleSourcePhysicalHolyGrailReceipt
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier)⟩

end GrandUnificationProducerNormalForm

end StandardModelConstraint
end SaturationMonoid
