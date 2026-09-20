import H0mework.Physics.YukawaSources.P533
import H0mework.Physics.YukawaSources.P666
import H0mework.Physics.RepresentationSources.P778

/-!
# Proposition 780: Yukawa leave-one-out producer source normal form

P774 proves that the finite Yukawa/CKM depth table is forced by the carrier
coefficient stencil.  P778 ties that numerical spine back to the SU(7)
representation/matter/Higgs carrier.  P522/P525/P533 prove the honest
leave-one-out harness: an eight-slot sigma lock forces the held-out Yukawa
slot, and an all-target lock gives a complete nine-slot run.

P666 keeps that harness alive at the producer-pressure root, but its facts are
still spread across the root.  This file packages the whole obligation as one
source-normal-form certificate: the same producer that forces the nine integer
depths also carries the all-target leave-one-out validation contract.
-/

noncomputable section

namespace SaturationMonoid

universe u

namespace GrandUnification

open StandardModelConstraint

/-! ## Focused leave-one-out normal-form projections -/

/-- THEOREM 1: the pressure root and the carrier source normal forms force the
same nine depths and CKM/Jarlskog depth sum. -/
theorem yukawaLeaveOneOutNormalForm_depthsAndCKM
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
        [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
      selectedYukawaDepthTableCandidate.massOrder =
        [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
        ckmJarlskogFourProductDepthSum
            selectedYukawaDepthTableCandidate =
          (ckmCPDepthSum : Int) := by
  exact
    ⟨yukawaPressure_finite_depths (E := E),
      StandardModelConstraint.su7RepresentationMatterHiggsNormalForm_numericalSpine.2.1,
      by
        calc
          ckmJarlskogFourProductDepthSum
              selectedYukawaDepthTableCandidate =
              ckmJarlskogDepthFromMatrix := by
            exact StandardModelConstraint.ckmJarlskogDepthFromMatrix_eq_selectedTable.symm
          _ = (ckmCPDepthSum : Int) := by
            exact StandardModelConstraint.ckmJarlskogDepthFromMatrix_eq_386⟩

/-- THEOREM 2: any accepted full beta-vector input surface inherits the same
Yukawa depth list and CKM/Jarlskog sum. -/
theorem yukawaLeaveOneOutNormalForm_inputSurfaceForces
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    C.2.massOrder = [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
      ckmJarlskogFourProductDepthSum C.2 = (ckmCPDepthSum : Int) := by
  exact
    ⟨yukawaPressure_input_surface_forces_depths (E := E) C hC,
      yukawaPressure_input_surface_forces_ckm (E := E) C hC⟩

/-- THEOREM 3: an all-target sigma lock predicts every held-out Yukawa slot
and makes every same-target prediction unique. -/
theorem yukawaLeaveOneOutNormalForm_allTargetLock
    {T : FrozenGUTScaleYukawaTable}
    (L : AllTargetYukawaLeaveOneOutLock T) :
    (∀ target : YukawaParameter,
      ∀ C : YukawaLeaveOneOutCandidate T target,
        T.observed target = T.predictionAt C.sigma target) ∧
      (∀ target : YukawaParameter,
        ∀ C₁ C₂ : YukawaLeaveOneOutCandidate T target,
          T.predictionAt C₁.sigma target =
            T.predictionAt C₂.sigma target) := by
  exact
    ⟨fun target C => L.predicts_every_target target C,
      fun target C₁ C₂ =>
        YukawaLeaveOneOutCandidate.target_prediction_unique
          (L.lock_at target) C₁ C₂⟩

/-- DEFINITION/THEOREM 4a: an all-target lock plus a complete run gives the
canonical run certificate. -/
def yukawaLeaveOneOutNormalForm_runCertificate_of_lock_and_run :
    ∀ {T : FrozenGUTScaleYukawaTable},
      AllTargetYukawaLeaveOneOutLock T ->
        AllTargetYukawaLeaveOneOutRun T ->
          AllTargetYukawaLeaveOneOutRunCertificate T :=
  fun {_T} L R =>
    allTargetYukawaLeaveOneOutRunCertificate_of_lock_and_run L R

/-- DEFINITION/THEOREM 4b: a linear-anchor family gives the all-target run
certificate directly. -/
def yukawaLeaveOneOutNormalForm_runCertificate_of_linear_anchor_family :
    ∀ {T : FrozenGUTScaleYukawaTable},
      (∀ target : YukawaParameter,
        ∃ anchor : YukawaParameter,
          anchor ≠ target ∧
            T.exponent anchor = 1 ∧
              T.amplitude anchor ≠ 0) ->
        AllTargetYukawaLeaveOneOutRunCertificate T :=
  fun {_T} hanchor =>
    canonicalAllTargetYukawaLeaveOneOutRunCertificate_of_linear_anchor_family
      hanchor

/-! ## Bundled certificate -/

/-- One source-normal-form certificate for the Yukawa leave-one-out producer
chain.  It keeps the finite SU(7) depth producer, the representation-backed
numerical spine, and the nine-slot leave-one-out validation harness in the
same object. -/
structure YukawaLeaveOneOutSourceNormalFormCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  pressure_root :
    YukawaLeaveOneOutPressureUnifiedRootCertificate E
  yukawa_depth_source_normal_form :
    StandardModelConstraint.YukawaDepthProducerSourceNormalFormCertificate
  su7_representation_matter_higgs :
    StandardModelConstraint.SU7RepresentationMatterHiggsSourceNormalFormCertificate
  all_target_run_shape :
    ∀ {T : FrozenGUTScaleYukawaTable},
      AllTargetYukawaLeaveOneOutLock T ->
        AllTargetYukawaLeaveOneOutRun T ->
          AllTargetYukawaLeaveOneOutRunCertificate T
  linear_anchor_family_run :
    ∀ {T : FrozenGUTScaleYukawaTable},
      (∀ target : YukawaParameter,
        ∃ anchor : YukawaParameter,
          anchor ≠ target ∧
            T.exponent anchor = 1 ∧
              T.amplitude anchor ≠ 0) ->
        AllTargetYukawaLeaveOneOutRunCertificate T
  depths_and_ckm :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
        [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
      selectedYukawaDepthTableCandidate.massOrder =
        [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
        ckmJarlskogFourProductDepthSum
            selectedYukawaDepthTableCandidate =
          (ckmCPDepthSum : Int)
  input_surface_forces :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        C.2.massOrder = [50, 346, 372, 489, 583, 682, 880, 908, 982] ∧
          ckmJarlskogFourProductDepthSum C.2 = (ckmCPDepthSum : Int)
  all_target_lock :
    ∀ {T : FrozenGUTScaleYukawaTable},
      AllTargetYukawaLeaveOneOutLock T ->
        (∀ target : YukawaParameter,
          ∀ C : YukawaLeaveOneOutCandidate T target,
            T.observed target = T.predictionAt C.sigma target) ∧
          (∀ target : YukawaParameter,
            ∀ C₁ C₂ : YukawaLeaveOneOutCandidate T target,
              T.predictionAt C₁.sigma target =
                T.predictionAt C₂.sigma target)
  pressure_locked_candidate_predicts :
    ∀ {T : FrozenGUTScaleYukawaTable} {target : YukawaParameter},
      EightSlotSigmaLock target T.observed T.amplitude T.exponent ->
        ∀ C : YukawaLeaveOneOutCandidate T target,
          T.observed target = T.predictionAt C.sigma target
  pressure_locked_prediction_unique :
    ∀ {T : FrozenGUTScaleYukawaTable} {target : YukawaParameter},
      EightSlotSigmaLock target T.observed T.amplitude T.exponent ->
        ∀ C₁ C₂ : YukawaLeaveOneOutCandidate T target,
          T.predictionAt C₁.sigma target =
            T.predictionAt C₂.sigma target
  pressure_linear_anchor_predicts :
    ∀ {T : FrozenGUTScaleYukawaTable}
      {target anchor : YukawaParameter},
      anchor ≠ target ->
        T.exponent anchor = 1 ->
          T.amplitude anchor ≠ 0 ->
            ∀ C : YukawaLeaveOneOutCandidate T target,
              T.observed target = T.predictionAt C.sigma target

/-- DEFINITION/THEOREM 5: Yukawa leave-one-out producer source-normal-form
certificate. -/
def yukawaLeaveOneOutSourceNormalFormCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    YukawaLeaveOneOutSourceNormalFormCertificate E where
  pressure_root :=
    yukawaLeaveOneOutPressureUnifiedRootCertificate (E := E)
  yukawa_depth_source_normal_form :=
    StandardModelConstraint.yukawaDepthProducerSourceNormalFormCertificate
  su7_representation_matter_higgs :=
    StandardModelConstraint.su7RepresentationMatterHiggsSourceNormalFormCertificate
  all_target_run_shape :=
    yukawaLeaveOneOutNormalForm_runCertificate_of_lock_and_run
  linear_anchor_family_run :=
    yukawaLeaveOneOutNormalForm_runCertificate_of_linear_anchor_family
  depths_and_ckm :=
    yukawaLeaveOneOutNormalForm_depthsAndCKM (E := E)
  input_surface_forces :=
    yukawaLeaveOneOutNormalForm_inputSurfaceForces (E := E)
  all_target_lock :=
    fun {_T} L => yukawaLeaveOneOutNormalForm_allTargetLock L
  pressure_locked_candidate_predicts :=
    fun {_T} {_target} lock C =>
      yukawaPressure_locked_candidate_predicts (E := E) lock C
  pressure_locked_prediction_unique :=
    fun {_T} {_target} lock C₁ C₂ =>
      yukawaPressure_locked_prediction_unique (E := E) lock C₁ C₂
  pressure_linear_anchor_predicts :=
    fun {_T} {_target} {_anchor} hanchor hexp hamp C =>
      yukawaPressure_linear_anchor_predicts (E := E) hanchor hexp hamp C

end GrandUnification
end SaturationMonoid
