import H0mework.Physics.AlphaSources.P527

/-!
# Proposition 528: unified grand hard-gate certificate

P524-P527 close four hard gates that were previously flat:

* the root affine / running-sigma / projection spine;
* all-target Yukawa leave-one-out locking;
* rejection of tautological truth-value shadows at the structured producer
  front door;
* the closed four-source alpha_s residual producer surface.

This file bundles those gates as a single Lean object.  It still does not
claim that the missing physical producers have been computed.  It proves that
the current "grand producer" target has one root certificate with the real
obligations exposed.
-/

noncomputable section

namespace SaturationMonoid

open StandardModelConstraint

universe u

/-! ## Unified hard-gate bundle -/

/-- The current hard-gate certificate for the unified formula / Standard Model
projection track.

It intentionally separates:

* algebraic formula spine;
* Yukawa leave-one-out validation contract;
* mathematical prime-shadow non-tautology gate;
* alpha_s four-source residual closure.
-/
structure UnifiedGrandHardGateCertificate where
  root_spine :
    UnifiedFormulaRootSpineCertificate.{u}
  yukawa_all_target_from_lock :
    ∀ {T : FrozenGUTScaleYukawaTable},
      AllTargetYukawaLeaveOneOutLock T ->
        AllTargetYukawaLeaveOneOutPredictionCertificate T
  yukawa_all_target_from_linear_anchor :
    ∀ {T : FrozenGUTScaleYukawaTable},
      (∀ target : YukawaParameter,
        ∃ anchor : YukawaParameter,
          anchor ≠ target ∧
            T.exponent anchor = 1 ∧
              T.amplitude anchor ≠ 0) ->
        AllTargetYukawaLeaveOneOutPredictionCertificate T
  structured_truth_shadow_exclusion :
    StructuredFrontDoorTruthShadowExclusionCertificate.{u}
  alpha_four_source_closure :
    AlphaStrongFourSourceClosureCertificate

/-- DEFINITION/THEOREM 1: the unified grand hard-gate certificate is inhabited by the
current machine-checked gates. -/
def unifiedGrandHardGateCertificate :
    UnifiedGrandHardGateCertificate.{u} where
  root_spine := unifiedFormulaRootSpineCertificate
  yukawa_all_target_from_lock := by
    intro T L
    exact allTargetYukawaLeaveOneOutPredictionCertificate_of_lock L
  yukawa_all_target_from_linear_anchor := by
    intro T hanchor
    exact allTargetYukawaLeaveOneOutPredictionCertificate_of_linear_anchor_family hanchor
  structured_truth_shadow_exclusion :=
    structuredFrontDoorTruthShadowExclusionCertificate
  alpha_four_source_closure :=
    alphaStrongFourSourceClosureCertificate

namespace UnifiedGrandHardGateCertificate

/-- THEOREM 2: the hard-gate bundle rejects the `Prop`-valued truth shadow at
the structured unified producer front door. -/
theorem rejects_truth_value_shadow_front_door
    (G : UnifiedGrandHardGateCertificate.{u})
    {Index A CKMCarrier PhysicalGeometry : Type u} [AddCommGroup A] :
    Not
      (Nonempty
        (UnifiedGrandStructuredProducerFrontDoor
          Index A CKMCarrier PhysicalGeometry
          AffineRelaxation.truthValuePrimeShadowProducer)) :=
  G.structured_truth_shadow_exclusion.truth_shadow_rejected

/-- THEOREM 3: the hard-gate bundle turns any closed four-source alpha_s
receipt into exact displayed-alpha closure. -/
theorem alpha_four_source_closes_displayed
    (G : UnifiedGrandHardGateCertificate.{u})
    (R : AlphaStrongFourSourceClosureReceipt) :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            (∑ s : AlphaStrongResidualSource, R.contribution s)) =
      alphaStrongDisplayed ℚ :=
  G.alpha_four_source_closure.closure_to_displayed_alpha R

/-- THEOREM 4: the hard-gate bundle exposes all-target Yukawa prediction from
an all-target sigma lock. -/
theorem yukawa_predicts_all_targets_from_lock
    (G : UnifiedGrandHardGateCertificate.{u})
    {T : FrozenGUTScaleYukawaTable}
    (L : AllTargetYukawaLeaveOneOutLock T) :
    AllTargetYukawaLeaveOneOutPredictionCertificate T :=
  G.yukawa_all_target_from_lock L

/-- THEOREM 5: the hard-gate bundle keeps the post-collapse RG front door
empty, so running dynamics must be produced before singleton collapse. -/
theorem post_collapse_rg_front_door_empty
    (G : UnifiedGrandHardGateCertificate.{u})
    {Index A CKMCarrier : Type u} [AddCommGroup A] :
    ¬ GrandUnificationProducerNormalForm.PhysicallyFaithfulGrandUnificationFrontDoor
        Index A CKMCarrier :=
  G.root_spine.post_collapse_rg_front_door_empty

end UnifiedGrandHardGateCertificate

end SaturationMonoid
