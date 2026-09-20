import H0mework.Physics.SourceContracts.P441

/-!
# Proposition 442: opened pinned-parameter holy-grail front door

P441 opens `ZeroContinuousFreeStandardModelCertificate` and
`RunningSigmaStandardModelCertificate`.  The remaining large Standard-Model
wrapper is `PinnedStandardModelConstraintCertificate`.

This file opens that wrapper too.  The current formal-exact holy-grail front
door is now expressed in terms of:

* the base 19-slot synthesis certificate;
* the pinned theta / weak-mixing / Yukawa residual-power fields;
* the running sigma/gauge-alpha fields;
* selected seed, singleton constraints, integer alpha, sampled clocks, and the
  physical sigma corridor.

This is still not a construction of the physical producers.  It is a normal
form theorem: the remaining obligations are explicit fields, not hidden record
wrappers.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

namespace GrandUnificationProducerNormalForm

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- The current formal-exact holy-grail producer obligation with `zeroFree`,
`running`, and `pinned` all opened into their actual field content. -/
def ExistsOpenedPinnedRunningSigmaZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ base :
      StandardModelConstraintSynthesisCertificate
        DiscreteStandardModelSeed StandardModelScaleCode Index A ℝ CKMCarrier,
    ∃ gutWeakMixingSquared : ParameterVector ℝ -> ℝ,
      ∃ _thetaQCD_zero :
        ∀ seed : DiscreteStandardModelSeed,
          base.generated seed StandardModelParameter.qcd_theta = 0,
        ∃ _gutWeakMixingSquared_eq_threeEighths :
          ∀ seed : DiscreteStandardModelSeed,
            gutWeakMixingSquared (base.generated seed) = threeEighths ℝ,
          ∃ yukawaAmplitude : YukawaParameter -> ℝ,
            ∃ yukawaSigma :
                DiscreteStandardModelSeed -> YukawaParameter -> ℝ,
              ∃ yukawaExponent :
                  DiscreteStandardModelSeed -> YukawaParameter -> Nat,
                ∃ _yukawa_residual_power :
                  ∀ seed y,
                    base.generated seed (yukawaSlot y) =
                      yukawaAmplitude y *
                        (((1 : ℝ) - yukawaSigma seed y) ^
                          yukawaExponent seed y),
                  ∃ gutScale : StandardModelScaleCode,
                    ∃ weakScale : StandardModelScaleCode,
                      ∃ sigma : StandardModelScaleCode -> ℝ,
                        ∃ gaugeCoupling : StandardModelScaleCode -> ℝ,
                          ∃ fourPi : ℝ,
                            ∃ _sigma_eq_alpha :
                              ∀ scale : StandardModelScaleCode,
                                sigma scale =
                                  alphaFromGaugeCoupling fourPi
                                    (gaugeCoupling scale),
                              ∃ _sigma_gut_nominal :
                                sigma gutScale = sigmaGUTNominal ℝ,
                                ∃ _sigma_weak_nominal :
                                  sigma weakScale = sigmaWeakNominal ℝ,
                                  ∃ higgsLambdaAtGUT :
                                      DiscreteStandardModelSeed -> ℝ,
                                    ∃ _higgsLambdaAtGUT_eq_rg_slot :
                                      ∀ seed : DiscreteStandardModelSeed,
                                        higgsLambdaAtGUT seed =
                                          base.rg.evolve gutScale
                                            (base.generated seed)
                                            StandardModelParameter.higgs_lambda,
                                      ∃ _higgsLambdaAtGUT_zero :
                                        ∀ seed : DiscreteStandardModelSeed,
                                          higgsLambdaAtGUT seed = 0,
                                        ∃ approx : ℝ -> ℝ -> Prop,
                                          ∃ _higgsLambdaAtGUT_near_sigmaCriticalProxy :
                                            ∀ seed : DiscreteStandardModelSeed,
                                              approx (higgsLambdaAtGUT seed)
                                                (sigmaCriticalProxy
                                                  (sigma gutScale)),
                                            ∃ yukawaScale :
                                                DiscreteStandardModelSeed ->
                                                  YukawaParameter ->
                                                    StandardModelScaleCode,
                                              ∃ _yukawaSigma_is_runningSigma :
                                                ∀ seed y,
                                                  yukawaSigma seed y =
                                                    sigma (yukawaScale seed y),
                                                ∃ selectedSeed :
                                                    DiscreteStandardModelSeed,
                                                  ∃ _constraints_exact_selected :
                                                    ∀ p : ParameterVector ℝ,
                                                      base.constraints p <->
                                                        p =
                                                          base.generated
                                                            selectedSeed,
                                                    ∃ _gutScale_is_gut :
                                                      gutScale =
                                                        StandardModelScaleCode.gut,
                                                      ∃ _weakScale_is_weak :
                                                        weakScale =
                                                          StandardModelScaleCode.weak,
                                                        ∃ _selected_yukawaScale_is_discrete :
                                                          ∀ y : YukawaParameter,
                                                            yukawaScale
                                                                selectedSeed y =
                                                              StandardModelScaleCode.yukawa y,
                                                          ∃ alphaEM : ℝ,
                                                            ∃ _alphaEM_integerConstraint :
                                                              alphaEM =
                                                                alphaEMFromIntegerConstraint ℝ,
                                                              ∃ yukawaLambda :
                                                                  YukawaParameter ->
                                                                    ℝ,
                                                                ∃ yukawaStep :
                                                                    YukawaParameter ->
                                                                      ℝ,
                                                                  (∀ y : YukawaParameter,
                                                                    sigma
                                                                        (StandardModelScaleCode.yukawa y) =
                                                                      AffineRelaxation.realDecayRate
                                                                        (yukawaLambda y)
                                                                        (yukawaStep y)) ∧
                                                                  fourPi =
                                                                    realFourPi ∧
                                                                  ∀ y : YukawaParameter,
                                                                    sigma
                                                                        (StandardModelScaleCode.yukawa y) ≤
                                                                      sigma
                                                                        StandardModelScaleCode.weak

/-- THEOREM 1: P441's running-sigma-opened surface is exactly the same surface
with the pinned-parameter certificate opened into fields. -/
theorem openedRunningSigma_iff_openedPinned :
    ExistsOpenedRunningSigmaZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        Index A CKMCarrier ↔
      ExistsOpenedPinnedRunningSigmaZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        Index A CKMCarrier := by
  constructor
  · rintro
      ⟨pinned,
        gutScale,
        weakScale,
        sigma,
        gaugeCoupling,
        fourPi,
        sigma_eq_alpha,
        sigma_gut_nominal,
        sigma_weak_nominal,
        higgsLambdaAtGUT,
        higgsLambdaAtGUT_eq_rg_slot,
        higgsLambdaAtGUT_zero,
        approx,
        higgsLambdaAtGUT_near_sigmaCriticalProxy,
        yukawaScale,
        yukawaSigma_is_runningSigma,
        selectedSeed,
        constraints_exact_selected,
        gutScale_is_gut,
        weakScale_is_weak,
        selected_yukawaScale_is_discrete,
        alphaEM,
        alphaEM_integerConstraint,
        yukawaLambda,
        yukawaStep,
        hsampled,
        hfour,
        hyukawa⟩
    exact
      ⟨pinned.base,
        pinned.gutWeakMixingSquared,
        pinned.thetaQCD_zero,
        pinned.gutWeakMixingSquared_eq_threeEighths,
        pinned.yukawaAmplitude,
        pinned.yukawaSigma,
        pinned.yukawaExponent,
        pinned.yukawa_residual_power,
        gutScale,
        weakScale,
        sigma,
        gaugeCoupling,
        fourPi,
        sigma_eq_alpha,
        sigma_gut_nominal,
        sigma_weak_nominal,
        higgsLambdaAtGUT,
        higgsLambdaAtGUT_eq_rg_slot,
        higgsLambdaAtGUT_zero,
        approx,
        higgsLambdaAtGUT_near_sigmaCriticalProxy,
        yukawaScale,
        yukawaSigma_is_runningSigma,
        selectedSeed,
        constraints_exact_selected,
        gutScale_is_gut,
        weakScale_is_weak,
        selected_yukawaScale_is_discrete,
        alphaEM,
        alphaEM_integerConstraint,
        yukawaLambda,
        yukawaStep,
        hsampled,
        hfour,
        hyukawa⟩
  · rintro
      ⟨base,
        gutWeakMixingSquared,
        thetaQCD_zero,
        gutWeakMixingSquared_eq_threeEighths,
        yukawaAmplitude,
        yukawaSigma,
        yukawaExponent,
        yukawa_residual_power,
        gutScale,
        weakScale,
        sigma,
        gaugeCoupling,
        fourPi,
        sigma_eq_alpha,
        sigma_gut_nominal,
        sigma_weak_nominal,
        higgsLambdaAtGUT,
        higgsLambdaAtGUT_eq_rg_slot,
        higgsLambdaAtGUT_zero,
        approx,
        higgsLambdaAtGUT_near_sigmaCriticalProxy,
        yukawaScale,
        yukawaSigma_is_runningSigma,
        selectedSeed,
        constraints_exact_selected,
        gutScale_is_gut,
        weakScale_is_weak,
        selected_yukawaScale_is_discrete,
        alphaEM,
        alphaEM_integerConstraint,
        yukawaLambda,
        yukawaStep,
        hsampled,
        hfour,
        hyukawa⟩
    let pinned :
        PinnedStandardModelConstraintCertificate
          DiscreteStandardModelSeed StandardModelScaleCode Index A ℝ CKMCarrier :=
      { base := base
        gutWeakMixingSquared := gutWeakMixingSquared
        thetaQCD_zero := thetaQCD_zero
        gutWeakMixingSquared_eq_threeEighths :=
          gutWeakMixingSquared_eq_threeEighths
        yukawaAmplitude := yukawaAmplitude
        yukawaSigma := yukawaSigma
        yukawaExponent := yukawaExponent
        yukawa_residual_power := yukawa_residual_power }
    exact
      ⟨pinned,
        gutScale,
        weakScale,
        sigma,
        gaugeCoupling,
        fourPi,
        sigma_eq_alpha,
        sigma_gut_nominal,
        sigma_weak_nominal,
        higgsLambdaAtGUT,
        by
          intro seed
          simpa [pinned] using higgsLambdaAtGUT_eq_rg_slot seed,
        higgsLambdaAtGUT_zero,
        approx,
        higgsLambdaAtGUT_near_sigmaCriticalProxy,
        yukawaScale,
        by
          intro seed y
          simpa [pinned] using yukawaSigma_is_runningSigma seed y,
        selectedSeed,
        by
          intro p
          simpa [pinned] using constraints_exact_selected p,
        gutScale_is_gut,
        weakScale_is_weak,
        selected_yukawaScale_is_discrete,
        alphaEM,
        alphaEM_integerConstraint,
        yukawaLambda,
        yukawaStep,
        hsampled,
        hfour,
        hyukawa⟩

/-- THEOREM 2: under the P435 formal-exact geometry audit, the current strict
good-cover holy-grail output exists exactly when the pinned-parameter-opened
field tuple exists. -/
theorem goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_openedPinned_under_currentFormalExactGeometry
    {CoverIndex E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    Nonempty
        (StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier
          (GoodCoverPoincarePhysicalGeometry CoverIndex E F)
          GoodCoverPoincarePhysicalGeometry.adapter) ↔
      ExistsOpenedPinnedRunningSigmaZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        Index A CKMCarrier := by
  exact
    goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_openedRunningSigma_under_currentFormalExactGeometry.trans
      openedRunningSigma_iff_openedPinned

/-- THEOREM 3: the fully opened pinned-parameter tuple directly supplies the
current formal-exact strict good-cover holy-grail output. -/
theorem openedPinnedRunningSigmaZeroFreeSampledYukawaClocksPhysicalSigmaCorridor_supplies_currentFormalExactGeometry_holyGrailOutput
    {CoverIndex E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    ExistsOpenedPinnedRunningSigmaZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        Index A CKMCarrier ->
      Nonempty
        (StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier
          (GoodCoverPoincarePhysicalGeometry CoverIndex E F)
          GoodCoverPoincarePhysicalGeometry.adapter) := by
  intro h
  exact
    (goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_openedPinned_under_currentFormalExactGeometry).mpr h

end GrandUnificationProducerNormalForm

end StandardModelConstraint
end SaturationMonoid
