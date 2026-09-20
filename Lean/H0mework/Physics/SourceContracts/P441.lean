import H0mework.Physics.SourceContracts.P440

/-!
# Proposition 441: opened running-sigma holy-grail front door

P440 opens the zero-free wrapper.  One large producer box still remains there:
`RunningSigmaStandardModelCertificate`.  This file opens that box as well.

The current formal-exact holy-grail front door is therefore equivalent to an
explicit tuple containing:

* the pinned 19-slot Standard-Model certificate;
* the running sigma/gauge-alpha fields and endpoint equations;
* the Higgs-at-GUT critical bridge;
* the Yukawa-scale-to-running-sigma bridge;
* the selected seed, singleton constraint equation, scale pins, integer alpha
  field, sampled Yukawa clocks, `fourPi = realFourPi`, and the weak sigma
  corridor.

This remains producer-relative.  It names the physical obligations rather than
solving beta functions, selecting the seed, or constructing the representation
content.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

namespace GrandUnificationProducerNormalForm

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- The current formal-exact holy-grail producer obligation with both the
`zeroFree` and `running` wrappers opened. -/
def ExistsOpenedRunningSigmaZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ pinned :
      PinnedStandardModelConstraintCertificate
        DiscreteStandardModelSeed StandardModelScaleCode Index A ℝ CKMCarrier,
    ∃ gutScale : StandardModelScaleCode,
      ∃ weakScale : StandardModelScaleCode,
        ∃ sigma : StandardModelScaleCode -> ℝ,
          ∃ gaugeCoupling : StandardModelScaleCode -> ℝ,
            ∃ fourPi : ℝ,
              ∃ _sigma_eq_alpha :
                ∀ scale : StandardModelScaleCode,
                  sigma scale =
                    alphaFromGaugeCoupling fourPi (gaugeCoupling scale),
                ∃ _sigma_gut_nominal :
                  sigma gutScale = sigmaGUTNominal ℝ,
                  ∃ _sigma_weak_nominal :
                    sigma weakScale = sigmaWeakNominal ℝ,
                    ∃ higgsLambdaAtGUT :
                        DiscreteStandardModelSeed -> ℝ,
                      ∃ _higgsLambdaAtGUT_eq_rg_slot :
                        ∀ seed : DiscreteStandardModelSeed,
                          higgsLambdaAtGUT seed =
                            pinned.base.rg.evolve gutScale
                              (pinned.base.generated seed)
                              StandardModelParameter.higgs_lambda,
                        ∃ _higgsLambdaAtGUT_zero :
                          ∀ seed : DiscreteStandardModelSeed,
                            higgsLambdaAtGUT seed = 0,
                          ∃ approx : ℝ -> ℝ -> Prop,
                            ∃ _higgsLambdaAtGUT_near_sigmaCriticalProxy :
                              ∀ seed : DiscreteStandardModelSeed,
                                approx (higgsLambdaAtGUT seed)
                                  (sigmaCriticalProxy (sigma gutScale)),
                              ∃ yukawaScale :
                                  DiscreteStandardModelSeed ->
                                    YukawaParameter -> StandardModelScaleCode,
                                ∃ _yukawaSigma_is_runningSigma :
                                  ∀ seed y,
                                    pinned.yukawaSigma seed y =
                                      sigma (yukawaScale seed y),
                                  ∃ selectedSeed : DiscreteStandardModelSeed,
                                    ∃ _constraints_exact_selected :
                                      ∀ p : ParameterVector ℝ,
                                        pinned.base.constraints p <->
                                          p = pinned.base.generated selectedSeed,
                                      ∃ _gutScale_is_gut :
                                        gutScale = StandardModelScaleCode.gut,
                                        ∃ _weakScale_is_weak :
                                          weakScale = StandardModelScaleCode.weak,
                                          ∃ _selected_yukawaScale_is_discrete :
                                            ∀ y : YukawaParameter,
                                              yukawaScale selectedSeed y =
                                                StandardModelScaleCode.yukawa y,
                                            ∃ alphaEM : ℝ,
                                              ∃ _alphaEM_integerConstraint :
                                                alphaEM =
                                                  alphaEMFromIntegerConstraint ℝ,
                                                ∃ yukawaLambda :
                                                    YukawaParameter -> ℝ,
                                                  ∃ yukawaStep :
                                                      YukawaParameter -> ℝ,
                                                    (∀ y : YukawaParameter,
                                                      sigma
                                                          (StandardModelScaleCode.yukawa y) =
                                                        AffineRelaxation.realDecayRate
                                                          (yukawaLambda y)
                                                          (yukawaStep y)) ∧
                                                    fourPi = realFourPi ∧
                                                    ∀ y : YukawaParameter,
                                                      sigma
                                                          (StandardModelScaleCode.yukawa y) ≤
                                                        sigma StandardModelScaleCode.weak

/-- THEOREM 1: P440's opened-zero-free surface is exactly the surface with the
running-sigma certificate opened into fields. -/
theorem openedZeroFree_iff_openedRunningSigma :
    ExistsOpenedZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        Index A CKMCarrier ↔
      ExistsOpenedRunningSigmaZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        Index A CKMCarrier := by
  constructor
  · rintro
      ⟨running,
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
      ⟨running.pinned,
        running.gutScale,
        running.weakScale,
        running.sigma,
        running.gaugeCoupling,
        running.fourPi,
        running.sigma_eq_alpha,
        running.sigma_gut_nominal,
        running.sigma_weak_nominal,
        running.higgsLambdaAtGUT,
        running.higgsLambdaAtGUT_eq_rg_slot,
        running.higgsLambdaAtGUT_zero,
        running.approx,
        running.higgsLambdaAtGUT_near_sigmaCriticalProxy,
        running.yukawaScale,
        running.yukawaSigma_is_runningSigma,
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
    let running :
        RunningSigmaStandardModelCertificate
          DiscreteStandardModelSeed StandardModelScaleCode Index A ℝ CKMCarrier :=
      { pinned := pinned
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
        yukawaSigma_is_runningSigma := yukawaSigma_is_runningSigma }
    exact
      ⟨running,
        selectedSeed,
        by
          intro p
          simpa [running] using constraints_exact_selected p,
        by
          simpa [running] using gutScale_is_gut,
        by
          simpa [running] using weakScale_is_weak,
        by
          intro y
          simpa [running] using selected_yukawaScale_is_discrete y,
        alphaEM,
        alphaEM_integerConstraint,
        yukawaLambda,
        yukawaStep,
        by
          intro y
          simpa [running] using hsampled y,
        by
          simpa [running] using hfour,
        by
          intro y
          simpa [running] using hyukawa y⟩

/-- THEOREM 2: under the P435 formal-exact geometry audit, the current strict
good-cover holy-grail output exists exactly when the running-sigma-opened
field tuple exists. -/
theorem goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_openedRunningSigma_under_currentFormalExactGeometry
    {CoverIndex E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    Nonempty
        (StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier
          (GoodCoverPoincarePhysicalGeometry CoverIndex E F)
          GoodCoverPoincarePhysicalGeometry.adapter) ↔
      ExistsOpenedRunningSigmaZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        Index A CKMCarrier := by
  exact
    goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_openedZeroFree_under_currentFormalExactGeometry.trans
      openedZeroFree_iff_openedRunningSigma

/-- THEOREM 3: the fully opened running-sigma tuple directly supplies the
current formal-exact strict good-cover holy-grail output. -/
theorem openedRunningSigmaZeroFreeSampledYukawaClocksPhysicalSigmaCorridor_supplies_currentFormalExactGeometry_holyGrailOutput
    {CoverIndex E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    ExistsOpenedRunningSigmaZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        Index A CKMCarrier ->
      Nonempty
        (StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier
          (GoodCoverPoincarePhysicalGeometry CoverIndex E F)
          GoodCoverPoincarePhysicalGeometry.adapter) := by
  intro h
  exact
    (goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_openedRunningSigma_under_currentFormalExactGeometry).mpr h

end GrandUnificationProducerNormalForm

end StandardModelConstraint
end SaturationMonoid
