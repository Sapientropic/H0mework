import H0mework.Physics.SourceForms.P377

/-!
# Proposition 378: grand-unification primitive producer normal form

P377 reduced the current unified-formula spine to a zero-free certificate plus
sampled Yukawa clocks.  This file opens that zero-free certificate all the way
down to the primitive producer atoms already named in P273/P274:

* the structural 19-slot synthesis certificate;
* the pinned theta / weak-mixing / Yukawa residual-power slice;
* the running-sigma data and endpoint equations;
* the selected discrete seed and singleton constraint surface;
* the sampled Yukawa clocks.

This is the "no hidden wrapper" theorem for the current Standard-Model
projection.  It still does not construct the physical producers themselves:
RG beta functions, threshold/Higgs representation content, CKM/H¹ calculation,
and the unique selected seed remain real producer obligations.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Primitive producer atoms -/

/-- The fully opened primitive producer payload for the current grand-
unification target.

All fields are copied from the producer obligations named by P273/P274/P276,
without the intermediate `ZeroContinuousFree...`, `RealSampled...`, or spine
wrappers. -/
structure GrandUnificationPrimitiveProducerAtoms
    (Index A CKMCarrier : Type*) [AddCommGroup A] where
  base :
    StandardModelConstraintSynthesisCertificate
      DiscreteStandardModelSeed StandardModelScaleCode Index A ℝ CKMCarrier
  gutWeakMixingSquared : ParameterVector ℝ -> ℝ
  thetaQCD_zero :
    ∀ seed, base.generated seed StandardModelParameter.qcd_theta = 0
  gutWeakMixingSquared_eq_threeEighths :
    ∀ seed, gutWeakMixingSquared (base.generated seed) = threeEighths ℝ
  yukawaAmplitude : YukawaParameter -> ℝ
  yukawaSigma : DiscreteStandardModelSeed -> YukawaParameter -> ℝ
  yukawaExponent : DiscreteStandardModelSeed -> YukawaParameter -> Nat
  yukawa_residual_power :
    ∀ seed y,
      base.generated seed (yukawaSlot y) =
        yukawaAmplitude y *
          (((1 : ℝ) - yukawaSigma seed y) ^ yukawaExponent seed y)
  gutScale : StandardModelScaleCode
  weakScale : StandardModelScaleCode
  sigma : StandardModelScaleCode -> ℝ
  gaugeCoupling : StandardModelScaleCode -> ℝ
  fourPi : ℝ
  sigma_eq_alpha :
    ∀ scale, sigma scale =
      alphaFromGaugeCoupling fourPi (gaugeCoupling scale)
  sigma_gut_nominal :
    sigma gutScale = sigmaGUTNominal ℝ
  sigma_weak_nominal :
    sigma weakScale = sigmaWeakNominal ℝ
  higgsLambdaAtGUT : DiscreteStandardModelSeed -> ℝ
  higgsLambdaAtGUT_eq_rg_slot :
    ∀ seed,
      higgsLambdaAtGUT seed =
        base.rg.evolve gutScale (base.generated seed)
          StandardModelParameter.higgs_lambda
  higgsLambdaAtGUT_zero :
    ∀ seed, higgsLambdaAtGUT seed = 0
  approx : ℝ -> ℝ -> Prop
  higgsLambdaAtGUT_near_sigmaCriticalProxy :
    ∀ seed,
      approx (higgsLambdaAtGUT seed)
        (sigmaCriticalProxy (sigma gutScale))
  yukawaScale : DiscreteStandardModelSeed -> YukawaParameter ->
    StandardModelScaleCode
  yukawaSigma_is_runningSigma :
    ∀ seed y, yukawaSigma seed y = sigma (yukawaScale seed y)
  selectedSeed : DiscreteStandardModelSeed
  constraints_exact_selected :
    ∀ p : ParameterVector ℝ,
      base.constraints p <-> p = base.generated selectedSeed
  gutScale_is_gut : gutScale = StandardModelScaleCode.gut
  weakScale_is_weak : weakScale = StandardModelScaleCode.weak
  selected_yukawaScale_is_discrete :
    ∀ y, yukawaScale selectedSeed y = StandardModelScaleCode.yukawa y
  alphaEM : ℝ
  alphaEM_integerConstraint :
    alphaEM = alphaEMFromIntegerConstraint ℝ
  yukawaLambda : YukawaParameter -> ℝ
  yukawaStep : YukawaParameter -> ℝ
  selected_yukawa_sigma_sampled :
    ∀ y : YukawaParameter,
      sigma (StandardModelScaleCode.yukawa y) =
        AffineRelaxation.realDecayRate (yukawaLambda y) (yukawaStep y)

namespace GrandUnificationPrimitiveProducerAtoms

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- Repack the primitive atoms as P273's pinned Standard-Model slice. -/
def toPinned
    (P : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) :
    PinnedStandardModelConstraintCertificate
      DiscreteStandardModelSeed StandardModelScaleCode Index A ℝ CKMCarrier where
  base := P.base
  gutWeakMixingSquared := P.gutWeakMixingSquared
  thetaQCD_zero := P.thetaQCD_zero
  gutWeakMixingSquared_eq_threeEighths :=
    P.gutWeakMixingSquared_eq_threeEighths
  yukawaAmplitude := P.yukawaAmplitude
  yukawaSigma := P.yukawaSigma
  yukawaExponent := P.yukawaExponent
  yukawa_residual_power := P.yukawa_residual_power

/-- Repack the primitive atoms as P274's running-sigma certificate. -/
def toRunning
    (P : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) :
    RunningSigmaStandardModelCertificate
      DiscreteStandardModelSeed StandardModelScaleCode Index A ℝ CKMCarrier where
  pinned := P.toPinned
  gutScale := P.gutScale
  weakScale := P.weakScale
  sigma := P.sigma
  gaugeCoupling := P.gaugeCoupling
  fourPi := P.fourPi
  sigma_eq_alpha := P.sigma_eq_alpha
  sigma_gut_nominal := P.sigma_gut_nominal
  sigma_weak_nominal := P.sigma_weak_nominal
  higgsLambdaAtGUT := P.higgsLambdaAtGUT
  higgsLambdaAtGUT_eq_rg_slot := P.higgsLambdaAtGUT_eq_rg_slot
  higgsLambdaAtGUT_zero := P.higgsLambdaAtGUT_zero
  approx := P.approx
  higgsLambdaAtGUT_near_sigmaCriticalProxy :=
    P.higgsLambdaAtGUT_near_sigmaCriticalProxy
  yukawaScale := P.yukawaScale
  yukawaSigma_is_runningSigma := P.yukawaSigma_is_runningSigma

/-- Repack the primitive atoms as P276's zero-free certificate. -/
def toZeroFree
    (P : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) :
    ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier where
  running := P.toRunning
  selectedSeed := P.selectedSeed
  constraints_exact_selected := P.constraints_exact_selected
  gutScale_is_gut := P.gutScale_is_gut
  weakScale_is_weak := P.weakScale_is_weak
  selected_yukawaScale_is_discrete :=
    P.selected_yukawaScale_is_discrete
  alphaEM := P.alphaEM
  alphaEM_integerConstraint := P.alphaEM_integerConstraint

/-- Repack the primitive atoms as P376's minimal producer kernel. -/
def toMinimalProducerKernel
    (P : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) :
    MinimalGrandUnificationProducerKernel Index A CKMCarrier where
  zeroFree := P.toZeroFree
  yukawaLambda := P.yukawaLambda
  yukawaStep := P.yukawaStep
  selected_yukawa_sigma_sampled :=
    P.selected_yukawa_sigma_sampled

/-- Open P376's minimal producer kernel back into primitive atoms. -/
def ofMinimalProducerKernel
    (M : MinimalGrandUnificationProducerKernel Index A CKMCarrier) :
    GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier where
  base := M.zeroFree.running.pinned.base
  gutWeakMixingSquared := M.zeroFree.running.pinned.gutWeakMixingSquared
  thetaQCD_zero := M.zeroFree.running.pinned.thetaQCD_zero
  gutWeakMixingSquared_eq_threeEighths :=
    M.zeroFree.running.pinned.gutWeakMixingSquared_eq_threeEighths
  yukawaAmplitude := M.zeroFree.running.pinned.yukawaAmplitude
  yukawaSigma := M.zeroFree.running.pinned.yukawaSigma
  yukawaExponent := M.zeroFree.running.pinned.yukawaExponent
  yukawa_residual_power := M.zeroFree.running.pinned.yukawa_residual_power
  gutScale := M.zeroFree.running.gutScale
  weakScale := M.zeroFree.running.weakScale
  sigma := M.zeroFree.running.sigma
  gaugeCoupling := M.zeroFree.running.gaugeCoupling
  fourPi := M.zeroFree.running.fourPi
  sigma_eq_alpha := M.zeroFree.running.sigma_eq_alpha
  sigma_gut_nominal := M.zeroFree.running.sigma_gut_nominal
  sigma_weak_nominal := M.zeroFree.running.sigma_weak_nominal
  higgsLambdaAtGUT := M.zeroFree.running.higgsLambdaAtGUT
  higgsLambdaAtGUT_eq_rg_slot :=
    M.zeroFree.running.higgsLambdaAtGUT_eq_rg_slot
  higgsLambdaAtGUT_zero := M.zeroFree.running.higgsLambdaAtGUT_zero
  approx := M.zeroFree.running.approx
  higgsLambdaAtGUT_near_sigmaCriticalProxy :=
    M.zeroFree.running.higgsLambdaAtGUT_near_sigmaCriticalProxy
  yukawaScale := M.zeroFree.running.yukawaScale
  yukawaSigma_is_runningSigma :=
    M.zeroFree.running.yukawaSigma_is_runningSigma
  selectedSeed := M.zeroFree.selectedSeed
  constraints_exact_selected := M.zeroFree.constraints_exact_selected
  gutScale_is_gut := M.zeroFree.gutScale_is_gut
  weakScale_is_weak := M.zeroFree.weakScale_is_weak
  selected_yukawaScale_is_discrete :=
    M.zeroFree.selected_yukawaScale_is_discrete
  alphaEM := M.zeroFree.alphaEM
  alphaEM_integerConstraint := M.zeroFree.alphaEM_integerConstraint
  yukawaLambda := M.yukawaLambda
  yukawaStep := M.yukawaStep
  selected_yukawa_sigma_sampled :=
    M.selected_yukawa_sigma_sampled

/-- THEOREM 1: primitive atoms and P376's minimal producer kernel have the
same existence content. -/
theorem nonempty_iff_minimalProducerKernel_nonempty :
    Nonempty (GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) ↔
      Nonempty (MinimalGrandUnificationProducerKernel Index A CKMCarrier) := by
  constructor
  · intro h
    rcases h with ⟨P⟩
    exact ⟨P.toMinimalProducerKernel⟩
  · intro h
    rcases h with ⟨M⟩
    exact ⟨ofMinimalProducerKernel M⟩

/-- THEOREM 2: the current unified-formula spine exists exactly when the
primitive producer atoms exist.  This is the fully opened normal form for the
current grand-unification target. -/
theorem unifiedFormulaSpine_nonempty_iff_primitiveProducerAtoms_nonempty :
    Nonempty (StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier) ↔
      Nonempty (GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) := by
  rw [MinimalGrandUnificationProducerKernel.unifiedFormulaSpine_nonempty_iff_minimalProducerKernel_nonempty]
  exact nonempty_iff_minimalProducerKernel_nonempty.symm

/-- THEOREM 3: primitive atoms canonically build the current unified-formula
spine. -/
noncomputable def toUnifiedFormulaSpine
    (P : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) :
    StandardModelUnifiedFormulaSpineCertificate Index A CKMCarrier :=
  P.toMinimalProducerKernel.toProducerKernel.toUnifiedFormulaSpine

/-- THEOREM 4: the primitive-atom spine carries the P374 compact receipt. -/
theorem primitiveAtoms_unified_formula_spine_receipt
    (P : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier) :
    (alphaEMFromIntegerConstraint ℝ = (1 : ℝ) / (137 : ℝ) ∧
      gutWeakMixingFromStructuralCards ℝ = threeEighths ℝ ∧
      alphaGUTInverseFromStructuralCards ℝ = ((133 : ℝ) / (3 : ℝ))) ∧
    (∀ p : ParameterVector ℝ,
      (toUnifiedFormulaSpine P).target.sampled.zeroFree.running.pinned.base.constraints p ->
        ∀ y : YukawaParameter,
          p (yukawaSlot y) =
            (toUnifiedFormulaSpine P).target.sampled.zeroFree.running.pinned.yukawaAmplitude y *
              AffineRelaxation.realDecayResidual
                ((toUnifiedFormulaSpine P).target.sampled.yukawaLambda y)
                (((toUnifiedFormulaSpine P).target.sampled.zeroFree.running.pinned.yukawaExponent
                    (toUnifiedFormulaSpine P).target.sampled.zeroFree.selectedSeed y : ℝ) *
                  (toUnifiedFormulaSpine P).target.sampled.yukawaStep y)) ∧
    AffineRelaxation.unitComplexPhaseWithRate
        (toUnifiedFormulaSpine P).target.cpRunningSigma
        (ckmCPDepthSum : ℝ) =
      AffineRelaxation.unitComplexPhase (cpRawPhaseClaim ℝ) ∧
    alphaStrongTwoLoopSMInverseCorrection ℝ +
        (toUnifiedFormulaSpine P).target.strongResidualProducer.inverseCorrection =
      alphaStrongDisplayedInverseCorrectionFromCorrectedGUT ℝ :=
  (toUnifiedFormulaSpine P).unified_formula_spine_receipt

end GrandUnificationPrimitiveProducerAtoms

end StandardModelConstraint
end SaturationMonoid
