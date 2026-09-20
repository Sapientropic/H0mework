import H0mework.Physics.AlphaSources.P665

/-!
# Proposition 666: Yukawa leave-one-out pressure on the unified root

P665 strengthens the central root with the alpha_s producer-pressure law.

This file adds the matching Yukawa pressure law.  The current finite layer
already forces the nine Yukawa depths and the CKM/Jarlskog depth sum.  P522
separately states the honest validation contract for a real frozen GUT-scale
Yukawa table: eight non-target slots must lock the shared sigma and thereby
predict the held-out slot.

This file welds those two facts into one root-level receipt.  It does not
provide the real frozen Yukawa observations.  It proves that the central root
now carries both sides of the obligation:

* finite SU7 / primitive-card input surfaces force the depth table;
* any future frozen table with an eight-slot sigma lock has unique held-out
  prediction.

Boundary: the remaining debt is still the physical frozen GUT-scale table and
its nine leave-one-out certificates.  The validation target itself is no
longer informal.
-/

noncomputable section

namespace SaturationMonoid

universe u

namespace GrandUnification

open StandardModelConstraint
open StandardModelConstraint.InformationMatterProjection

/-- The central root strengthened by Yukawa leave-one-out pressure.

This is a producer-pressure receipt, not a new low-energy fit: the finite depth
surface and the leave-one-out validation contract are forced to live together.
-/
structure YukawaLeaveOneOutPressureUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  alpha_pressure_root :
    AlphaStrongProducerPressureUnifiedRootCertificate E
  finite_yukawa_closure :
    YukawaFiniteDepthProducerDebtClosureCertificate
  full_beta_vector_input_surface :
    FullBetaVectorInputThreeNailSurfaceCertificate
  one_axis_yukawa_depth :
    OneAxisYukawaDepthProducerCertificate
      canonicalOneAxisPrimitiveSourceProducer
  finite_depths :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  finite_ckm_depth_sum :
    ckmJarlskogFourProductDepthSum
        primitiveCardYukawaProducerInputCandidate.depthTable =
      (ckmCPDepthSum : Int)
  input_surface_no_free :
    NoContinuousFreeFullBetaVectorInputThreeNailParameters
      FullBetaVectorInputThreeNailProducerSurface
  input_surface_forces_depths :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        C.2.massOrder = [50, 346, 372, 489, 583, 682, 880, 908, 982]
  input_surface_forces_ckm :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        ckmJarlskogFourProductDepthSum C.2 = (ckmCPDepthSum : Int)
  locked_candidate_predicts :
    ∀ {T : FrozenGUTScaleYukawaTable} {target : YukawaParameter},
      EightSlotSigmaLock target T.observed T.amplitude T.exponent ->
        ∀ C : YukawaLeaveOneOutCandidate T target,
          T.observed target = T.predictionAt C.sigma target
  locked_target_prediction_unique :
    ∀ {T : FrozenGUTScaleYukawaTable} {target : YukawaParameter},
      EightSlotSigmaLock target T.observed T.amplitude T.exponent ->
        ∀ C₁ C₂ : YukawaLeaveOneOutCandidate T target,
          T.predictionAt C₁.sigma target =
            T.predictionAt C₂.sigma target
  linear_anchor_predicts :
    ∀ {T : FrozenGUTScaleYukawaTable}
      {target anchor : YukawaParameter},
      anchor ≠ target ->
        T.exponent anchor = 1 ->
          T.amplitude anchor ≠ 0 ->
            ∀ C : YukawaLeaveOneOutCandidate T target,
              T.observed target = T.predictionAt C.sigma target

/-- THEOREM 1: the Yukawa leave-one-out pressure root is inhabited. -/
def yukawaLeaveOneOutPressureUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    YukawaLeaveOneOutPressureUnifiedRootCertificate E where
  alpha_pressure_root :=
    alphaStrongProducerPressureUnifiedRootCertificate (E := E)
  finite_yukawa_closure := yukawaFiniteDepthProducerDebtClosureCertificate
  full_beta_vector_input_surface := fullBetaVectorInputThreeNailSurfaceCertificate
  one_axis_yukawa_depth := canonicalOneAxisYukawaDepthProducerCertificate
  finite_depths := refinedCentralRoot_yukawa_depths (E := E)
  finite_ckm_depth_sum :=
    oneAxisPrimitiveSource_forces_typedJarlskogDepthSum
      canonicalOneAxisPrimitiveSourceProducer
  input_surface_no_free := fullBetaVectorInputThreeNailSurfaceCertificate.no_free
  input_surface_forces_depths :=
    fullBetaVectorInputThreeNailSurfaceCertificate.yukawa_mass_order
  input_surface_forces_ckm :=
    fullBetaVectorInputThreeNailSurfaceCertificate.ckm_jarlskog_sum
  locked_candidate_predicts := by
    intro T target lock C
    exact C.predicts_target lock
  locked_target_prediction_unique := by
    intro T target lock C₁ C₂
    exact
      YukawaLeaveOneOutCandidate.target_prediction_unique lock C₁ C₂
  linear_anchor_predicts := by
    intro T target anchor hanchor hexp hamp C
    exact leaveOneOut_predicts_target_of_linear_anchor hanchor hexp hamp C

/-! ## Focused projections -/

/-- THEOREM 2: the strengthened root exposes the finite Yukawa depth list. -/
theorem yukawaPressure_finite_depths
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] :=
  (yukawaLeaveOneOutPressureUnifiedRootCertificate
    (E := E)).finite_depths

/-- THEOREM 3: every accepted full beta-vector input surface forces the same
Yukawa depth list. -/
theorem yukawaPressure_input_surface_forces_depths
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    C.2.massOrder = [50, 346, 372, 489, 583, 682, 880, 908, 982] :=
  (yukawaLeaveOneOutPressureUnifiedRootCertificate
    (E := E)).input_surface_forces_depths C hC

/-- THEOREM 4: every accepted full beta-vector input surface forces the
CKM/Jarlskog depth sum. -/
theorem yukawaPressure_input_surface_forces_ckm
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    ckmJarlskogFourProductDepthSum C.2 = (ckmCPDepthSum : Int) :=
  (yukawaLeaveOneOutPressureUnifiedRootCertificate
    (E := E)).input_surface_forces_ckm C hC

/-- THEOREM 5: under an eight-slot sigma lock, a leave-one-out candidate
predicts the held-out Yukawa slot exactly. -/
theorem yukawaPressure_locked_candidate_predicts
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {T : FrozenGUTScaleYukawaTable} {target : YukawaParameter}
    (lock : EightSlotSigmaLock target T.observed T.amplitude T.exponent)
    (C : YukawaLeaveOneOutCandidate T target) :
    T.observed target = T.predictionAt C.sigma target :=
  (yukawaLeaveOneOutPressureUnifiedRootCertificate
    (E := E)).locked_candidate_predicts lock C

/-- THEOREM 6: under an eight-slot sigma lock, the held-out prediction is
unique across all leave-one-out sigma candidates. -/
theorem yukawaPressure_locked_prediction_unique
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {T : FrozenGUTScaleYukawaTable} {target : YukawaParameter}
    (lock : EightSlotSigmaLock target T.observed T.amplitude T.exponent)
    (C₁ C₂ : YukawaLeaveOneOutCandidate T target) :
    T.predictionAt C₁.sigma target =
      T.predictionAt C₂.sigma target :=
  (yukawaLeaveOneOutPressureUnifiedRootCertificate
    (E := E)).locked_target_prediction_unique lock C₁ C₂

/-- THEOREM 7: a nonzero linear anchor among the eight non-target slots is a
sufficient certificate for held-out prediction. -/
theorem yukawaPressure_linear_anchor_predicts
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {T : FrozenGUTScaleYukawaTable}
    {target anchor : YukawaParameter}
    (hanchor : anchor ≠ target)
    (hexp : T.exponent anchor = 1)
    (hamp : T.amplitude anchor ≠ 0)
    (C : YukawaLeaveOneOutCandidate T target) :
    T.observed target = T.predictionAt C.sigma target :=
  (yukawaLeaveOneOutPressureUnifiedRootCertificate
    (E := E)).linear_anchor_predicts hanchor hexp hamp C

end GrandUnification
end SaturationMonoid
