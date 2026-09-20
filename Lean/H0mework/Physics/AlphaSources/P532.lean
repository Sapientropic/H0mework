import H0mework.Realization.Relations.P531

/-!
# Proposition 532: producer-facing alpha_s source accounting

P530 proves exact partial-source accounting for the explicit four-source
closure receipt.  P529 proves that this receipt is the exact normal form of the
original `AlphaStrongResidualGapProducer`.

This file pushes the accounting law back through that equivalence.  From here
on, the accounting rule is stated directly on the residual producer:

* selected and omitted physical source families recombine to the displayed
  alpha-level gap;
* a selected subfamily can itself be a residual-gap producer iff the omitted
  source contribution is exactly zero;
* therefore an `alpha_s` residual producer cannot silently omit SU(7) breaking,
  thresholds, three-loop RG, or Higgs/extra-representation effects.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open scoped BigOperators

namespace AlphaStrongResidualGapProducer

/-! ## Producer-facing selected and omitted source sums -/

/-- Selected source contribution, stated on the residual producer itself. -/
def selectedContribution
    (P : AlphaStrongResidualGapProducer)
    (selected : AlphaStrongResidualSource -> Bool) :
    AlphaStrongResidualSource -> ℚ :=
  P.toFourSourceClosureReceipt.selectedContribution selected

/-- Omitted source contribution, stated on the residual producer itself. -/
def omittedContribution
    (P : AlphaStrongResidualGapProducer)
    (selected : AlphaStrongResidualSource -> Bool) :
    AlphaStrongResidualSource -> ℚ :=
  P.toFourSourceClosureReceipt.omittedContribution selected

/-- Sum of selected source families for the residual producer. -/
def selectedSum
    (P : AlphaStrongResidualGapProducer)
    (selected : AlphaStrongResidualSource -> Bool) : ℚ :=
  P.toFourSourceClosureReceipt.selectedSum selected

/-- Sum of omitted source families for the residual producer. -/
def omittedSum
    (P : AlphaStrongResidualGapProducer)
    (selected : AlphaStrongResidualSource -> Bool) : ℚ :=
  P.toFourSourceClosureReceipt.omittedSum selected

/-- THEOREM 1: selected and omitted producer contributions recombine
pointwise to the original source contribution. -/
theorem selectedContribution_add_omittedContribution
    (P : AlphaStrongResidualGapProducer)
    (selected : AlphaStrongResidualSource -> Bool)
    (s : AlphaStrongResidualSource) :
    P.selectedContribution selected s +
        P.omittedContribution selected s =
      P.contribution s := by
  have h :=
    P.toFourSourceClosureReceipt.selectedContribution_add_omittedContribution
      selected s
  cases s <;>
    simpa [selectedContribution, omittedContribution,
      AlphaStrongResidualGapProducer.toFourSourceClosureReceipt,
      AlphaStrongFourSourceClosureReceipt.contribution] using h

/-- THEOREM 2: selected and omitted producer sums recombine to the displayed
alpha-level residual gap. -/
theorem selectedSum_add_omittedSum_eq_gap
    (P : AlphaStrongResidualGapProducer)
    (selected : AlphaStrongResidualSource -> Bool) :
    P.selectedSum selected + P.omittedSum selected =
      alphaStrongTwoLoopSMDisplayedGap ℚ :=
  P.toFourSourceClosureReceipt.selectedSum_add_omittedSum_eq_gap selected

/-- THEOREM 3: if the selected producer source families already close the
alpha-level residual, the omitted source sum is exactly zero. -/
theorem omittedSum_eq_zero_of_selectedSum_eq_gap
    (P : AlphaStrongResidualGapProducer)
    (selected : AlphaStrongResidualSource -> Bool)
    (hselected :
      P.selectedSum selected = alphaStrongTwoLoopSMDisplayedGap ℚ) :
    P.omittedSum selected = 0 :=
  P.toFourSourceClosureReceipt.omittedSum_eq_zero_of_selectedSum_eq_gap
    selected hselected

/-- THEOREM 4: if the omitted producer source families sum to zero, the
selected source families close the alpha-level residual. -/
theorem selectedSum_eq_gap_of_omittedSum_eq_zero
    (P : AlphaStrongResidualGapProducer)
    (selected : AlphaStrongResidualSource -> Bool)
    (homitted : P.omittedSum selected = 0) :
    P.selectedSum selected = alphaStrongTwoLoopSMDisplayedGap ℚ :=
  P.toFourSourceClosureReceipt.selectedSum_eq_gap_of_omittedSum_eq_zero
    selected homitted

/-- THEOREM 5: exact partial-source accounting on the producer itself.  A
selected source family closes the residual iff the omitted source families are
null. -/
theorem selectedSum_eq_gap_iff_omittedSum_eq_zero
    (P : AlphaStrongResidualGapProducer)
    (selected : AlphaStrongResidualSource -> Bool) :
    P.selectedSum selected = alphaStrongTwoLoopSMDisplayedGap ℚ ↔
      P.omittedSum selected = 0 :=
  ⟨P.omittedSum_eq_zero_of_selectedSum_eq_gap selected,
    P.selectedSum_eq_gap_of_omittedSum_eq_zero selected⟩

/-- THEOREM 6: the empty selected source family cannot close the producer-level
alpha residual. -/
theorem selectedSum_empty_ne_gap
    (P : AlphaStrongResidualGapProducer) :
    P.selectedSum (fun _ => false) ≠
      alphaStrongTwoLoopSMDisplayedGap ℚ :=
  P.toFourSourceClosureReceipt.selectedSum_empty_ne_gap

/-! ## Selected-source producer front door -/

/-- The residual producer made from only the selected source families, when
those selected families really close the alpha-level gap. -/
def selectedSubproducer
    (P : AlphaStrongResidualGapProducer)
    (selected : AlphaStrongResidualSource -> Bool)
    (hselected :
      P.selectedSum selected = alphaStrongTwoLoopSMDisplayedGap ℚ) :
    AlphaStrongResidualGapProducer where
  contribution := P.selectedContribution selected
  total_gap := by
    rw [← alphaStrongResidualSource_univ_sum (P.selectedContribution selected)]
    simpa [selectedSum, selectedContribution,
      AlphaStrongFourSourceClosureReceipt.selectedSum] using hselected

/-- THEOREM 7: a selected source family can be promoted to a producer exactly
when the omitted source sum is zero. -/
theorem exists_selectedSubproducer_iff_omittedSum_eq_zero
    (P : AlphaStrongResidualGapProducer)
    (selected : AlphaStrongResidualSource -> Bool) :
    (∃ Q : AlphaStrongResidualGapProducer,
        ∀ s : AlphaStrongResidualSource,
          Q.contribution s = P.selectedContribution selected s) ↔
      P.omittedSum selected = 0 := by
  constructor
  · intro h
    rcases h with ⟨Q, hQ⟩
    have hQsum :
        (∑ s : AlphaStrongResidualSource, Q.contribution s) =
          alphaStrongTwoLoopSMDisplayedGap ℚ := by
      rw [alphaStrongResidualSource_univ_sum]
      simpa using Q.total_gap
    have hselected_explicit :
        (∑ s : AlphaStrongResidualSource, P.selectedContribution selected s) =
          alphaStrongTwoLoopSMDisplayedGap ℚ := by
      calc
        (∑ s : AlphaStrongResidualSource, P.selectedContribution selected s) =
            ∑ s : AlphaStrongResidualSource, Q.contribution s := by
          apply Finset.sum_congr rfl
          intro s _hs
          exact (hQ s).symm
        _ = alphaStrongTwoLoopSMDisplayedGap ℚ := hQsum
    have hselected :
        P.selectedSum selected = alphaStrongTwoLoopSMDisplayedGap ℚ := by
      simpa [selectedSum, selectedContribution,
        AlphaStrongFourSourceClosureReceipt.selectedSum]
        using hselected_explicit
    exact P.omittedSum_eq_zero_of_selectedSum_eq_gap selected hselected
  · intro homitted
    refine ⟨P.selectedSubproducer selected
        (P.selectedSum_eq_gap_of_omittedSum_eq_zero selected homitted), ?_⟩
    intro s
    rfl

/-- THEOREM 8: a selected source family that closes the alpha-level gap also
closes the displayed strong-coupling anchor after inverse-coordinate transport. -/
theorem selectedSum_closes_displayedAlpha_of_selectedSum_eq_gap
    (P : AlphaStrongResidualGapProducer)
    (selected : AlphaStrongResidualSource -> Bool)
    (hselected :
      P.selectedSum selected = alphaStrongTwoLoopSMDisplayedGap ℚ) :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            (P.selectedSum selected)) =
      alphaStrongDisplayed ℚ := by
  rw [hselected]
  rw [← alphaStrongResidualInverseCorrection_eq_inverseGapImage]
  exact alphaStrongResidualInverseCorrection_closes_displayedAlpha

end AlphaStrongResidualGapProducer

/-! ## Bundled producer-facing accounting certificate -/

/-- Producer-facing accounting certificate for the `alpha_s` residual. -/
structure AlphaStrongResidualProducerAccountingCertificate where
  selected_plus_omitted :
    ∀ (P : AlphaStrongResidualGapProducer)
      (selected : AlphaStrongResidualSource -> Bool),
      P.selectedSum selected + P.omittedSum selected =
        alphaStrongTwoLoopSMDisplayedGap ℚ
  partial_closure_iff_omitted_null :
    ∀ (P : AlphaStrongResidualGapProducer)
      (selected : AlphaStrongResidualSource -> Bool),
      P.selectedSum selected = alphaStrongTwoLoopSMDisplayedGap ℚ ↔
        P.omittedSum selected = 0
  selected_producer_iff_omitted_null :
    ∀ (P : AlphaStrongResidualGapProducer)
      (selected : AlphaStrongResidualSource -> Bool),
      (∃ Q : AlphaStrongResidualGapProducer,
          ∀ s : AlphaStrongResidualSource,
            Q.contribution s = P.selectedContribution selected s) ↔
        P.omittedSum selected = 0
  selected_gap_closes_displayed :
    ∀ (P : AlphaStrongResidualGapProducer)
      (selected : AlphaStrongResidualSource -> Bool),
      P.selectedSum selected = alphaStrongTwoLoopSMDisplayedGap ℚ →
        (1 : ℚ) /
            (alphaStrongTwoLoopSMOutputInverse ℚ +
              inverseCorrectionFromAlphaGap
                (alphaStrongTwoLoopSMOutput ℚ)
                (P.selectedSum selected)) =
          alphaStrongDisplayed ℚ
  empty_selection_never_closes :
    ∀ P : AlphaStrongResidualGapProducer,
      P.selectedSum (fun _ => false) ≠
        alphaStrongTwoLoopSMDisplayedGap ℚ

/-- THEOREM 9: exact source accounting is available directly on the residual
producer, not only on its explicit receipt normal form. -/
theorem alphaStrongResidualProducerAccountingCertificate :
    AlphaStrongResidualProducerAccountingCertificate where
  selected_plus_omitted := fun P selected =>
    P.selectedSum_add_omittedSum_eq_gap selected
  partial_closure_iff_omitted_null := fun P selected =>
    P.selectedSum_eq_gap_iff_omittedSum_eq_zero selected
  selected_producer_iff_omitted_null := fun P selected =>
    P.exists_selectedSubproducer_iff_omittedSum_eq_zero selected
  selected_gap_closes_displayed := fun P selected hselected =>
    P.selectedSum_closes_displayedAlpha_of_selectedSum_eq_gap selected hselected
  empty_selection_never_closes := fun P =>
    P.selectedSum_empty_ne_gap

end StandardModelConstraint

open StandardModelConstraint

universe u

/-! ## Unified hard gate v3 -/

/-- The current unified hard gate with producer-facing alpha_s accounting.

Compared with v2, this gate exposes the residual producer itself as the
accounting surface.  The explicit four-source receipt remains the exact normal
form, but a caller no longer has to leave the producer interface to ask which
source families were selected or omitted. -/
structure UnifiedGrandHardGateV3Certificate where
  base :
    UnifiedGrandHardGateV2Certificate.{u}
  alpha_residual_producer_accounting :
    AlphaStrongResidualProducerAccountingCertificate

/-- THEOREM 10: the unified grand hard gate v3 is inhabited by the current
machine-checked gates. -/
noncomputable def unifiedGrandHardGateV3Certificate :
    UnifiedGrandHardGateV3Certificate.{u} where
  base := unifiedGrandHardGateV2Certificate
  alpha_residual_producer_accounting :=
    alphaStrongResidualProducerAccountingCertificate

namespace UnifiedGrandHardGateV3Certificate

/-- THEOREM 11: v3 keeps the exact producer/receipt equivalence from v2. -/
def alpha_receipt_equiv_gapProducer
    (G : UnifiedGrandHardGateV3Certificate.{u}) :
    AlphaStrongFourSourceClosureReceipt ≃ AlphaStrongResidualGapProducer :=
  G.base.alpha_receipt_equiv_gapProducer

/-- THEOREM 12: v3 states partial-source closure directly on the residual
producer. -/
theorem alpha_residual_partial_closure_iff_omitted_null
    (G : UnifiedGrandHardGateV3Certificate.{u})
    (P : AlphaStrongResidualGapProducer)
    (selected : AlphaStrongResidualSource -> Bool) :
    P.selectedSum selected = alphaStrongTwoLoopSMDisplayedGap ℚ ↔
      P.omittedSum selected = 0 :=
  G.alpha_residual_producer_accounting.partial_closure_iff_omitted_null
    P selected

/-- THEOREM 13: v3 promotes a selected source family to a residual producer
exactly when all omitted source families are null. -/
theorem alpha_residual_selected_producer_iff_omitted_null
    (G : UnifiedGrandHardGateV3Certificate.{u})
    (P : AlphaStrongResidualGapProducer)
    (selected : AlphaStrongResidualSource -> Bool) :
    (∃ Q : AlphaStrongResidualGapProducer,
        ∀ s : AlphaStrongResidualSource,
          Q.contribution s = P.selectedContribution selected s) ↔
      P.omittedSum selected = 0 :=
  G.alpha_residual_producer_accounting.selected_producer_iff_omitted_null
    P selected

/-- THEOREM 14: v3 rejects the empty source selection directly on the residual
producer. -/
theorem alpha_residual_empty_selection_never_closes
    (G : UnifiedGrandHardGateV3Certificate.{u})
    (P : AlphaStrongResidualGapProducer) :
    P.selectedSum (fun _ => false) ≠
      alphaStrongTwoLoopSMDisplayedGap ℚ :=
  G.alpha_residual_producer_accounting.empty_selection_never_closes P

/-- THEOREM 15: v3 transports any producer-level selected source closure to
the displayed strong-coupling anchor. -/
theorem alpha_residual_selected_gap_closes_displayed
    (G : UnifiedGrandHardGateV3Certificate.{u})
    (P : AlphaStrongResidualGapProducer)
    (selected : AlphaStrongResidualSource -> Bool)
    (hselected :
      P.selectedSum selected = alphaStrongTwoLoopSMDisplayedGap ℚ) :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            (P.selectedSum selected)) =
      alphaStrongDisplayed ℚ :=
  G.alpha_residual_producer_accounting.selected_gap_closes_displayed
    P selected hselected

end UnifiedGrandHardGateV3Certificate

end SaturationMonoid
