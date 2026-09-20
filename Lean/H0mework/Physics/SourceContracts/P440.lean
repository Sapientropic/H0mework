import H0mework.Physics.SourceForms.P439

/-!
# Proposition 440: opened zero-free holy-grail front door

P439 identifies the current formal-exact holy-grail front door with a
`ZeroContinuousFreeStandardModelCertificate`, sampled Yukawa clocks, and two
physical sigma-corridor equations.

This file opens the `zeroFree` wrapper itself.  The remaining front door is now
the explicit tuple:

* one running-sigma certificate;
* one selected discrete seed;
* the singleton constraint equation for the accepted 19-slot surface;
* the GUT/weak/selected-Yukawa scale identifications;
* the integer electromagnetic-alpha field;
* sampled Yukawa clocks;
* `fourPi = realFourPi`;
* selected Yukawa sigmas below the weak endpoint.

This is still producer-relative: it does not solve the RG equations, derive the
selected seed, or construct the physical representation content.  It only makes
the current Lean holy-grail obligation maximally explicit at the zero-free
surface.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

namespace GrandUnificationProducerNormalForm

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- The current formal-exact holy-grail producer obligation with the
`ZeroContinuousFreeStandardModelCertificate` wrapper opened into its actual
fields. -/
def ExistsOpenedZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ running :
      RunningSigmaStandardModelCertificate
        DiscreteStandardModelSeed StandardModelScaleCode Index A ℝ CKMCarrier,
    ∃ selectedSeed : DiscreteStandardModelSeed,
      ∃ _constraints_exact_selected :
        ∀ p : ParameterVector ℝ,
          running.pinned.base.constraints p <->
            p = running.pinned.base.generated selectedSeed,
        ∃ _gutScale_is_gut :
          running.gutScale = StandardModelScaleCode.gut,
          ∃ _weakScale_is_weak :
            running.weakScale = StandardModelScaleCode.weak,
            ∃ _selected_yukawaScale_is_discrete :
              ∀ y : YukawaParameter,
                running.yukawaScale selectedSeed y =
                  StandardModelScaleCode.yukawa y,
              ∃ alphaEM : ℝ,
                ∃ _alphaEM_integerConstraint :
                  alphaEM = alphaEMFromIntegerConstraint ℝ,
                  ∃ yukawaLambda : YukawaParameter -> ℝ,
                    ∃ yukawaStep : YukawaParameter -> ℝ,
                      (∀ y : YukawaParameter,
                        running.sigma (StandardModelScaleCode.yukawa y) =
                          AffineRelaxation.realDecayRate
                            (yukawaLambda y) (yukawaStep y)) ∧
                      running.fourPi = realFourPi ∧
                      ∀ y : YukawaParameter,
                        running.sigma (StandardModelScaleCode.yukawa y) ≤
                          running.sigma StandardModelScaleCode.weak

/-- THEOREM 1: P439's zero-free sampled-clock physical sigma-corridor surface
is exactly the opened field tuple above. -/
theorem zeroFreeSampledYukawaClocksPhysicalSigmaCorridor_iff_openedZeroFree :
    ExistsZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        Index A CKMCarrier ↔
      ExistsOpenedZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        Index A CKMCarrier := by
  constructor
  · rintro ⟨zeroFree, yukawaLambda, yukawaStep, hsampled, hfour, hyukawa⟩
    exact
      ⟨zeroFree.running,
        zeroFree.selectedSeed,
        zeroFree.constraints_exact_selected,
        zeroFree.gutScale_is_gut,
        zeroFree.weakScale_is_weak,
        zeroFree.selected_yukawaScale_is_discrete,
        zeroFree.alphaEM,
        zeroFree.alphaEM_integerConstraint,
        yukawaLambda,
        yukawaStep,
        hsampled,
        hfour,
        hyukawa⟩
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
    let zeroFree :
        ZeroContinuousFreeStandardModelCertificate
          Index A ℝ CKMCarrier :=
      { running := running
        selectedSeed := selectedSeed
        constraints_exact_selected := constraints_exact_selected
        gutScale_is_gut := gutScale_is_gut
        weakScale_is_weak := weakScale_is_weak
        selected_yukawaScale_is_discrete :=
          selected_yukawaScale_is_discrete
        alphaEM := alphaEM
        alphaEM_integerConstraint := alphaEM_integerConstraint }
    exact
      ⟨zeroFree,
        yukawaLambda,
        yukawaStep,
        by
          intro y
          simpa [zeroFree] using hsampled y,
        by
          simpa [zeroFree] using hfour,
        by
          intro y
          simpa [zeroFree] using hyukawa y⟩

/-- THEOREM 2: under the P435 formal-exact geometry audit, the current strict
good-cover holy-grail output exists exactly when the opened zero-free
sampled-clock physical sigma-corridor tuple exists. -/
theorem goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_openedZeroFree_under_currentFormalExactGeometry
    {CoverIndex E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    Nonempty
        (StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier
          (GoodCoverPoincarePhysicalGeometry CoverIndex E F)
          GoodCoverPoincarePhysicalGeometry.adapter) ↔
      ExistsOpenedZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        Index A CKMCarrier := by
  exact
    goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_zeroFreeSampledYukawaClocksPhysicalSigmaCorridor_under_currentFormalExactGeometry.trans
      zeroFreeSampledYukawaClocksPhysicalSigmaCorridor_iff_openedZeroFree

/-- THEOREM 3: the fully opened zero-free tuple directly supplies the current
formal-exact strict good-cover holy-grail output. -/
theorem openedZeroFreeSampledYukawaClocksPhysicalSigmaCorridor_supplies_currentFormalExactGeometry_holyGrailOutput
    {CoverIndex E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    ExistsOpenedZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        Index A CKMCarrier ->
      Nonempty
        (StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier
          (GoodCoverPoincarePhysicalGeometry CoverIndex E F)
          GoodCoverPoincarePhysicalGeometry.adapter) := by
  intro h
  exact
    (goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_openedZeroFree_under_currentFormalExactGeometry).mpr h

end GrandUnificationProducerNormalForm

end StandardModelConstraint
end SaturationMonoid
