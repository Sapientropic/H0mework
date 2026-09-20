import H0mework.Physics.AlphaSources.P530

/-!
# Proposition 531: unified grand hard gate v2

P528 bundled the first hard gates.  P529/P530 then tightened the `alpha_s`
surface:

* the explicit four-source receipt is the exact normal form of the residual-gap
  producer;
* partial-source closure is equivalent to omitted-source nullity.

This file closes that bundle gap.  The unified hard gate now exposes one entry
point for the current grand-unification target, with the alpha residual producer
surface no longer split across separate wrappers.
-/

noncomputable section

namespace SaturationMonoid

open StandardModelConstraint

universe u

/-! ## Unified hard gate v2 -/

/-- The current unified hard gate with exact alpha_s producer normal form and
partial-source accounting included. -/
structure UnifiedGrandHardGateV2Certificate where
  base :
    UnifiedGrandHardGateCertificate.{u}
  alpha_exact_normal_form :
    AlphaStrongFourSourceExactNormalFormCertificate
  alpha_partial_source_accounting :
    AlphaStrongPartialSourceAccountingCertificate

/-- THEOREM 1: the unified grand hard gate v2 is inhabited by the current
machine-checked gates. -/
def unifiedGrandHardGateV2Certificate :
    UnifiedGrandHardGateV2Certificate.{u} where
  base := unifiedGrandHardGateCertificate
  alpha_exact_normal_form :=
    alphaStrongFourSourceExactNormalFormCertificate
  alpha_partial_source_accounting :=
    alphaStrongPartialSourceAccountingCertificate

namespace UnifiedGrandHardGateV2Certificate

/-- THEOREM 2: v2 keeps the `Prop`-valued truth shadow outside the structured
producer front door. -/
theorem rejects_truth_value_shadow_front_door
    (G : UnifiedGrandHardGateV2Certificate.{u})
    {Index A CKMCarrier PhysicalGeometry : Type u} [AddCommGroup A] :
    Not
      (Nonempty
        (UnifiedGrandStructuredProducerFrontDoor
          Index A CKMCarrier PhysicalGeometry
          AffineRelaxation.truthValuePrimeShadowProducer)) :=
  G.base.rejects_truth_value_shadow_front_door

/-- DEFINITION/THEOREM 3: v2 exposes exact equivalence between the explicit four-source
receipt and the residual-gap producer. -/
def alpha_receipt_equiv_gapProducer
    (G : UnifiedGrandHardGateV2Certificate.{u}) :
    AlphaStrongFourSourceClosureReceipt ≃ AlphaStrongResidualGapProducer :=
  G.alpha_exact_normal_form.equiv

/-- THEOREM 4: v2 transports any explicit four-source closure receipt to the
displayed strong-coupling anchor. -/
theorem alpha_four_source_closes_displayed
    (G : UnifiedGrandHardGateV2Certificate.{u})
    (R : AlphaStrongFourSourceClosureReceipt) :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            (∑ s : AlphaStrongResidualSource, R.contribution s)) =
      alphaStrongDisplayed ℚ :=
  G.base.alpha_four_source_closes_displayed R

/-- THEOREM 5: v2 exposes the exact partial-source accounting law: a selected
source family closes the alpha residual iff the omitted sources sum to zero. -/
theorem alpha_partial_closure_iff_omitted_null
    (G : UnifiedGrandHardGateV2Certificate.{u})
    (R : AlphaStrongFourSourceClosureReceipt)
    (selected : AlphaStrongResidualSource -> Bool) :
    R.selectedSum selected = alphaStrongTwoLoopSMDisplayedGap ℚ ↔
      R.omittedSum selected = 0 :=
  G.alpha_partial_source_accounting.partial_closure_iff_omitted_null R selected

/-- THEOREM 6: v2 rejects empty alpha-source closure. -/
theorem alpha_empty_selection_never_closes
    (G : UnifiedGrandHardGateV2Certificate.{u})
    (R : AlphaStrongFourSourceClosureReceipt) :
    R.selectedSum (fun _ => false) ≠
      alphaStrongTwoLoopSMDisplayedGap ℚ :=
  G.alpha_partial_source_accounting.empty_selection_never_closes R

/-- THEOREM 7: v2 keeps all-target Yukawa prediction available from an
all-target sigma lock. -/
theorem yukawa_predicts_all_targets_from_lock
    (G : UnifiedGrandHardGateV2Certificate.{u})
    {T : FrozenGUTScaleYukawaTable}
    (L : AllTargetYukawaLeaveOneOutLock T) :
    AllTargetYukawaLeaveOneOutPredictionCertificate T :=
  G.base.yukawa_predicts_all_targets_from_lock L

/-- THEOREM 8: v2 also exposes the reusable linear-anchor sufficient condition
for all-target Yukawa leave-one-out prediction. -/
theorem yukawa_predicts_all_targets_from_linear_anchor
    (G : UnifiedGrandHardGateV2Certificate.{u})
    {T : FrozenGUTScaleYukawaTable}
    (hanchor :
      ∀ target : YukawaParameter,
        ∃ anchor : YukawaParameter,
          anchor ≠ target ∧
            T.exponent anchor = 1 ∧
              T.amplitude anchor ≠ 0) :
    AllTargetYukawaLeaveOneOutPredictionCertificate T :=
  G.base.yukawa_all_target_from_linear_anchor hanchor

/-- THEOREM 9: v2 keeps the post-collapse RG front door empty. -/
theorem post_collapse_rg_front_door_empty
    (G : UnifiedGrandHardGateV2Certificate.{u})
    {Index A CKMCarrier : Type u} [AddCommGroup A] :
    ¬ GrandUnificationProducerNormalForm.PhysicallyFaithfulGrandUnificationFrontDoor
        Index A CKMCarrier :=
  G.base.post_collapse_rg_front_door_empty

end UnifiedGrandHardGateV2Certificate

end SaturationMonoid
