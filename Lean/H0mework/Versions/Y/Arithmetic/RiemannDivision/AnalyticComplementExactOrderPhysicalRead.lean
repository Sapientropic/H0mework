import H0mework.Versions.Y.Arithmetic.RiemannDivision.AnalyticComplementDivisionPhysicality
import H0mework.Versions.Y.Arithmetic.RiemannAnnulus.AnalyticComplementPhysicalPairing

/-! # Exact-order physical read of the analytic-complement source -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex MeasureTheory Set Filter FourierTransform
open SourceGeneratedComplexFeaturePerfectification
open ClozelGeneralizedDual
open ClozelGeneralizedDual.BurnolPhysicalState
open scoped ENNReal InnerProductSpace Topology

noncomputable section

/-- At the exact order, the normalized Mellin read of the actual raw state
is the source-generated finite part. -/
theorem burnolAnalyticComplementDivisionExactOrder_normalizedHeat_eq_finitePart
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolDivisionNormalizedPhysicalHeatMellin
        ⟨burnolAnalyticComplementDivisionAdditiveState observation nontrivial
            (generatedRiemannXiZeroOrder owner observation.coordinate),
          burnolAnalyticComplementDivisionAdditiveState_mem_evenBurnolClosedFace
            observation nontrivial rightHalf
              (generatedRiemannXiZeroOrder owner observation.coordinate)
              (le_refl _)⟩
        (burnolAnalyticComplementDivisionCenter observation) =
      burnolAnalyticComplementIteratedResolventFinitePart owner observation
        ((1 / 2 : ℂ) - observation.coordinate / 2) := by
  let order := generatedRiemannXiZeroOrder owner observation.coordinate
  let physical :=
    burnolAnalyticComplementDivisionAdditiveState_mem_evenBurnolClosedFace
      observation nontrivial rightHalf order (le_refl order)
  have centerPositive :
      0 < (burnolAnalyticComplementDivisionCenter observation).re := by
    unfold burnolAnalyticComplementDivisionCenter
    simp only [Complex.sub_re, Complex.div_re, Complex.one_re]
    norm_num
    linarith [observation.coordinate_re_lt_one]
  have centerBelowHalf :
      (burnolAnalyticComplementDivisionCenter observation).re < 1 / 2 := by
    unfold burnolAnalyticComplementDivisionCenter
    simp only [Complex.sub_re, Complex.div_re, Complex.one_re]
    norm_num
    linarith
  have continuation := burnolDivisionNormalizedPhysicalHeatMellin_eq_jet
    observation nontrivial rightHalf order (le_refl order) physical
    ⟨centerPositive, centerBelowHalf⟩
  rw [burnolAnalyticComplementDivisionJet_at_order observation] at continuation
  simpa only [order, physical] using continuation

theorem burnolAnalyticComplementDivisionExactOrder_normalizedHeat_ne_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolDivisionNormalizedPhysicalHeatMellin
        ⟨burnolAnalyticComplementDivisionAdditiveState observation nontrivial
            (generatedRiemannXiZeroOrder owner observation.coordinate),
          burnolAnalyticComplementDivisionAdditiveState_mem_evenBurnolClosedFace
            observation nontrivial rightHalf
              (generatedRiemannXiZeroOrder owner observation.coordinate)
              (le_refl _)⟩
        (burnolAnalyticComplementDivisionCenter observation) ≠ 0 := by
  rw [burnolAnalyticComplementDivisionExactOrder_normalizedHeat_eq_finitePart
    observation nontrivial rightHalf]
  exact burnolAnalyticComplementIteratedResolventFinitePart_at_ne_zero
    observation nontrivial

/-- Exact-order physical Fourier read: the generated finite part is carried
to the genuine Fourier completed-Mellin evaluator with the two gamma factors
made explicit. -/
theorem burnolAnalyticComplementDivisionExactOrder_fourierRead_identity
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    Gammaℝ observation.coordinate *
        burnolCompletedMellinEvaluator
          (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)
          (evenFaceFourier burnolUnscaledCommonGapRadius
            ⟨burnolAnalyticComplementDivisionAdditiveState observation nontrivial
                (generatedRiemannXiZeroOrder owner observation.coordinate),
              burnolAnalyticComplementDivisionAdditiveState_mem_evenBurnolClosedFace
                observation nontrivial rightHalf
                  (generatedRiemannXiZeroOrder owner observation.coordinate)
                  (le_refl _)⟩) =
      (1 / 2 : ℂ) * Gammaℝ (1 - observation.coordinate) *
        burnolAnalyticComplementIteratedResolventFinitePart owner observation
          ((1 / 2 : ℂ) - observation.coordinate / 2) := by
  let order := generatedRiemannXiZeroOrder owner observation.coordinate
  let physical :=
    burnolAnalyticComplementDivisionAdditiveState_mem_evenBurnolClosedFace
      observation nontrivial rightHalf order (le_refl order)
  let raw : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius :=
    ⟨burnolAnalyticComplementDivisionAdditiveState observation nontrivial order,
      physical⟩
  let coordinate :=
    burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  let center := burnolAnalyticComplementDivisionCenter observation
  let finitePart :=
    burnolAnalyticComplementIteratedResolventFinitePart owner observation
      ((1 / 2 : ℂ) - observation.coordinate / 2)
  have normalizedEq :
      burnolDivisionNormalizedPhysicalHeatMellin raw center = finitePart := by
    simpa only [raw, physical, order, center, finitePart] using
      (burnolAnalyticComplementDivisionExactOrder_normalizedHeat_eq_finitePart
        observation nontrivial rightHalf)
  have doubledCenter : 2 * center = 1 - observation.coordinate := by
    dsimp only [center, burnolAnalyticComplementDivisionCenter]
    ring
  have complementGammaNe : Gammaℝ (2 * center) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    rw [doubledCenter]
    simp only [Complex.sub_re, Complex.one_re]
    linarith [observation.coordinate_re_lt_one]
  unfold burnolDivisionNormalizedPhysicalHeatMellin at normalizedEq
  have heatEq :
      mellin (burnolGenericGaussianHeatPairTotal (raw : BurnolL2)) center =
        Gammaℝ (2 * center) * finitePart := by
    field_simp [complementGammaNe] at normalizedEq
    exact normalizedEq
  have bridge := burnolGenericHomogeneousGammaMellinBridge
    (evenFaceFourier burnolUnscaledCommonGapRadius raw) coordinate
  have fourier := burnolGenericGaussianFourierHomogeneousIdentity
    raw observation.coordinate
  change Gammaℝ observation.coordinate *
      burnolCompletedMellinEvaluator coordinate
        (evenFaceFourier burnolUnscaledCommonGapRadius raw) =
    (1 / 2 : ℂ) *
      mellin
        (burnolGenericGaussianHeatPairTotal
          (fourierL2 (raw : BurnolL2)))
        (observation.coordinate / 2) at bridge
  rw [fourier] at bridge
  rw [show (1 - observation.coordinate) / 2 = center by
    dsimp only [center, burnolAnalyticComplementDivisionCenter]
    ring, heatEq, doubledCenter] at bridge
  simpa only [order, physical, raw, coordinate, finitePart, mul_assoc] using bridge

/-- The exact-order Fourier completed-Mellin read is nonzero, without a
simple-zero or target-read premise. -/
theorem burnolAnalyticComplementDivisionExactOrder_fourierRead_ne_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolCompletedMellinEvaluator
        (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)
        (evenFaceFourier burnolUnscaledCommonGapRadius
          ⟨burnolAnalyticComplementDivisionAdditiveState observation nontrivial
              (generatedRiemannXiZeroOrder owner observation.coordinate),
            burnolAnalyticComplementDivisionAdditiveState_mem_evenBurnolClosedFace
              observation nontrivial rightHalf
                (generatedRiemannXiZeroOrder owner observation.coordinate)
                (le_refl _)⟩) ≠ 0 := by
  intro readZero
  have identity :=
    burnolAnalyticComplementDivisionExactOrder_fourierRead_identity
      observation nontrivial rightHalf
  rw [readZero, mul_zero] at identity
  have complementGammaNe : Gammaℝ (1 - observation.coordinate) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.sub_re, Complex.one_re]
    linarith [observation.coordinate_re_lt_one]
  have finitePartNe :=
    burnolAnalyticComplementIteratedResolventFinitePart_at_ne_zero
      observation nontrivial
  have rightNe :
      (1 / 2 : ℂ) * Gammaℝ (1 - observation.coordinate) *
        burnolAnalyticComplementIteratedResolventFinitePart owner observation
          ((1 / 2 : ℂ) - observation.coordinate / 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) complementGammaNe) finitePartNe
  exact rightNe identity.symm

/-! ## Public exact-order state and read assembly -/

/-- The public exact-order projected state is now literally the raw additive
division state: generated physicality makes its orthogonal projection the
identity. -/
theorem burnolAnalyticComplementExactOrderPhysicalState_coe_eq_raw
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    (burnolAnalyticComplementExactOrderPhysicalState
        observation nontrivial : BurnolL2) =
      burnolAnalyticComplementExactOrderAdditiveState observation nontrivial := by
  let order := generatedRiemannXiZeroOrder owner observation.coordinate
  have physical :=
    burnolAnalyticComplementDivisionAdditiveState_mem_evenBurnolClosedFace
      observation nontrivial rightHalf order (le_refl order)
  have exactPhysical :
      burnolAnalyticComplementExactOrderAdditiveState observation nontrivial ∈
        evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
    simpa only [order, burnolAnalyticComplementDivisionAdditiveState,
      burnolAnalyticComplementDivisionState,
      burnolAnalyticComplementExactOrderAdditiveState,
      burnolAnalyticComplementExactOrderCompletionResolvent] using physical
  unfold burnolAnalyticComplementExactOrderPhysicalState
    burnolSourceFeatureCompletionPhysicalMap
    burnolAnalyticComplementExactOrderAdditiveState
  simp only [ContinuousLinearMap.comp_apply]
  unfold burnolEvenAmbientProjection
  exact Submodule.starProjection_eq_self_iff.mpr exactPhysical

private theorem divisionJet_exactOrderPhysicalState_eq_rawCarrier
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolAnalyticComplementExactOrderPhysicalState observation nontrivial =
      ⟨burnolAnalyticComplementDivisionAdditiveState observation nontrivial
          (generatedRiemannXiZeroOrder owner observation.coordinate),
        burnolAnalyticComplementDivisionAdditiveState_mem_evenBurnolClosedFace
          observation nontrivial rightHalf
            (generatedRiemannXiZeroOrder owner observation.coordinate)
            (le_refl _)⟩ := by
  apply Subtype.ext
  rw [burnolAnalyticComplementExactOrderPhysicalState_coe_eq_raw
    observation nontrivial rightHalf]
  rfl

private theorem divisionJet_completedMellinCoordinate_eq
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolAnalyticComplementCompletedMellinCoordinate observation rightHalf =
      burnolDivisionZeroCompletedMellinCoordinate observation rightHalf := by
  rfl

/-- The actual public exact-order Fourier read equals the expected scalar;
this is obtained by solving the generated gamma identity. -/
theorem burnolAnalyticComplementExactOrderPhysicalFourierRead_eq_expected
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolCompletedMellinEvaluator
        (burnolAnalyticComplementCompletedMellinCoordinate
          observation rightHalf)
        (burnolAnalyticComplementExactOrderPhysicalFourierState
          observation nontrivial) =
      burnolAnalyticComplementExpectedPhysicalFourierRead owner observation := by
  have identity :=
    burnolAnalyticComplementDivisionExactOrder_fourierRead_identity
      observation nontrivial rightHalf
  rw [divisionJet_completedMellinCoordinate_eq observation rightHalf]
  unfold burnolAnalyticComplementExactOrderPhysicalFourierState
  rw [divisionJet_exactOrderPhysicalState_eq_rawCarrier
    observation nontrivial rightHalf]
  unfold burnolAnalyticComplementExpectedPhysicalFourierRead
  have gammaNe : Gammaℝ observation.coordinate ≠ 0 :=
    observation.gammaReal_ne_zero_of_nontrivial nontrivial
  change burnolCompletedMellinEvaluator
      (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)
      (evenFaceFourier burnolUnscaledCommonGapRadius
        ⟨burnolAnalyticComplementDivisionAdditiveState observation nontrivial
            (generatedRiemannXiZeroOrder owner observation.coordinate),
          burnolAnalyticComplementDivisionAdditiveState_mem_evenBurnolClosedFace
            observation nontrivial rightHalf
              (generatedRiemannXiZeroOrder owner observation.coordinate)
              (le_refl _)⟩) =
    (Gammaℝ (1 - observation.coordinate) / Gammaℝ observation.coordinate) *
      (1 / 2 : ℂ) *
        burnolAnalyticComplementIteratedResolventFinitePart owner observation
          ((1 / 2 : ℂ) - observation.coordinate / 2)
  calc
    _ = ((1 / 2 : ℂ) * Gammaℝ (1 - observation.coordinate) *
          burnolAnalyticComplementIteratedResolventFinitePart owner observation
            ((1 / 2 : ℂ) - observation.coordinate / 2)) /
        Gammaℝ observation.coordinate := by
      apply (eq_div_iff gammaNe).2
      calc
        _ = Gammaℝ observation.coordinate *
            burnolCompletedMellinEvaluator
              (burnolDivisionZeroCompletedMellinCoordinate
                observation rightHalf)
              (evenFaceFourier burnolUnscaledCommonGapRadius
                ⟨burnolAnalyticComplementDivisionAdditiveState
                    observation nontrivial
                    (generatedRiemannXiZeroOrder owner observation.coordinate),
                  burnolAnalyticComplementDivisionAdditiveState_mem_evenBurnolClosedFace
                    observation nontrivial rightHalf
                      (generatedRiemannXiZeroOrder owner observation.coordinate)
                      (le_refl _)⟩) := by ring
        _ = _ := identity
    _ = _ := by field_simp [gammaNe]

/-- The actual public exact-order Fourier read is nonzero, now as a
consequence of the generated state law rather than a supplied pairing. -/
theorem burnolAnalyticComplementExactOrderPhysicalFourierRead_ne_zero_generated
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolCompletedMellinEvaluator
        (burnolAnalyticComplementCompletedMellinCoordinate
          observation rightHalf)
        (burnolAnalyticComplementExactOrderPhysicalFourierState
          observation nontrivial) ≠ 0 := by
  rw [burnolAnalyticComplementExactOrderPhysicalFourierRead_eq_expected
    observation nontrivial rightHalf]
  exact burnolAnalyticComplementExpectedPhysicalFourierRead_ne_zero
    observation nontrivial

/-- Independent consumer: the selected completed-Mellin functional itself
is nonzero because it reads the source-generated exact-order Fourier state
nontrivially. -/
theorem burnolAnalyticComplementCompletedMellinEvaluator_ne_zero_generated
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolCompletedMellinEvaluator
        (burnolAnalyticComplementCompletedMellinCoordinate
          observation rightHalf) ≠ 0 := by
  intro functionalZero
  have readZero := congrArg
    (fun functional : BurnolPaAmbientCarrier →L[ℂ] ℂ =>
      functional
        (burnolAnalyticComplementExactOrderPhysicalFourierState
          observation nontrivial)) functionalZero
  simp only [zero_apply] at readZero
  exact (burnolAnalyticComplementExactOrderPhysicalFourierRead_ne_zero_generated
    observation nontrivial rightHalf) readZero

/-- Source-owned exact-order package.  All state equality and nonvanishing
claims are outputs of the division law. -/
theorem burnolAnalyticComplementDivisionExactOrder_directConsumer
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    (burnolAnalyticComplementExactOrderPhysicalState
        observation nontrivial : BurnolL2) =
        burnolAnalyticComplementExactOrderAdditiveState observation nontrivial ∧
      burnolCompletedMellinEvaluator
          (burnolAnalyticComplementCompletedMellinCoordinate
            observation rightHalf)
          (burnolAnalyticComplementExactOrderPhysicalFourierState
            observation nontrivial) =
        burnolAnalyticComplementExpectedPhysicalFourierRead owner observation ∧
      burnolCompletedMellinEvaluator
          (burnolAnalyticComplementCompletedMellinCoordinate
            observation rightHalf)
          (burnolAnalyticComplementExactOrderPhysicalFourierState
            observation nontrivial) ≠ 0 ∧
      burnolCompletedMellinEvaluator
          (burnolAnalyticComplementCompletedMellinCoordinate
            observation rightHalf) ≠ 0 := by
  exact ⟨
    burnolAnalyticComplementExactOrderPhysicalState_coe_eq_raw
      observation nontrivial rightHalf,
    burnolAnalyticComplementExactOrderPhysicalFourierRead_eq_expected
      observation nontrivial rightHalf,
    burnolAnalyticComplementExactOrderPhysicalFourierRead_ne_zero_generated
      observation nontrivial rightHalf,
    burnolAnalyticComplementCompletedMellinEvaluator_ne_zero_generated
      observation nontrivial rightHalf⟩

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
