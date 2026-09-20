import H0mework.Physics.BranchSources.P639

/-!
# Proposition 640: scalar gaps cannot recover the active source label

P639 proves that a scalar total-gap-only selector cannot choose the finite
`SU(7)` branch.  This file lowers that no-go to the actual source label.

The canonical `SU(7)`-only receipt and the threshold-only receipt have the
same scalar total gap, but their active-source supports are different:

* canonical receipt: active source is `su7Breaking`;
* threshold-only receipt: active source is `threshold`.

Therefore the missing physical producer must recover source identity, not just
the scalar alpha residual.  Equivalently: the next useful `alpha_s` producer
input is a source / representation selector, not a decimal correction.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Active-source labels of the two closed receipts -/

/-- THEOREM 1: the canonical receipt has active support exactly at
`su7Breaking`. -/
theorem alphaStrongCanonicalFourSourceReceipt_activeSupport_iff
    (s : AlphaStrongResidualSource) :
    AlphaStrongResidualActiveSourceSupport
        alphaStrongCanonicalFourSourceReceipt.contribution s ↔
      s = .su7Breaking := by
  cases s
  · norm_num [AlphaStrongResidualActiveSourceSupport,
      alphaStrongCanonicalFourSourceReceipt,
      AlphaStrongFourSourceClosureReceipt.contribution,
      alphaStrongTwoLoopSMDisplayedGap,
      alphaStrongDisplayed,
      alphaStrongTwoLoopSMOutput]
  · simp [AlphaStrongResidualActiveSourceSupport,
      alphaStrongCanonicalFourSourceReceipt,
      AlphaStrongFourSourceClosureReceipt.contribution]
  · simp [AlphaStrongResidualActiveSourceSupport,
      alphaStrongCanonicalFourSourceReceipt,
      AlphaStrongFourSourceClosureReceipt.contribution]
  · simp [AlphaStrongResidualActiveSourceSupport,
      alphaStrongCanonicalFourSourceReceipt,
      AlphaStrongFourSourceClosureReceipt.contribution]

/-- THEOREM 2: the threshold-only receipt has active support exactly at
`threshold`. -/
theorem alphaStrongThresholdOnlyFourSourceReceipt_activeSupport_iff
    (s : AlphaStrongResidualSource) :
    AlphaStrongResidualActiveSourceSupport
        alphaStrongThresholdOnlyFourSourceReceipt.contribution s ↔
      s = .threshold := by
  cases s
  · simp [AlphaStrongResidualActiveSourceSupport,
      alphaStrongThresholdOnlyFourSourceReceipt,
      AlphaStrongFourSourceClosureReceipt.contribution]
  · norm_num [AlphaStrongResidualActiveSourceSupport,
      alphaStrongThresholdOnlyFourSourceReceipt,
      AlphaStrongFourSourceClosureReceipt.contribution,
      alphaStrongTwoLoopSMDisplayedGap,
      alphaStrongDisplayed,
      alphaStrongTwoLoopSMOutput]
  · simp [AlphaStrongResidualActiveSourceSupport,
      alphaStrongThresholdOnlyFourSourceReceipt,
      AlphaStrongFourSourceClosureReceipt.contribution]
  · simp [AlphaStrongResidualActiveSourceSupport,
      alphaStrongThresholdOnlyFourSourceReceipt,
      AlphaStrongFourSourceClosureReceipt.contribution]

/-- The source labels required by the two witness receipts are genuinely
different. -/
theorem alphaStrong_canonical_threshold_activeSourceLabels_ne :
    AlphaStrongResidualSource.su7Breaking ≠
      AlphaStrongResidualSource.threshold := by
  intro h
  cases h

/-! ## Total-gap-only active-source recovery is impossible -/

/-- A selector is correct on the two branch witnesses when it returns the
unique active source for each witness. -/
def AlphaStrongActiveSourceLabelCorrectOnBranchWitnesses
    (selector :
      AlphaStrongFourSourceClosureReceipt -> AlphaStrongResidualSource) :
    Prop :=
  selector alphaStrongCanonicalFourSourceReceipt =
      AlphaStrongResidualSource.su7Breaking ∧
    selector alphaStrongThresholdOnlyFourSourceReceipt =
      AlphaStrongResidualSource.threshold

/-- THEOREM 3: no total-gap-only selector can recover the active-source labels
of both branch witnesses. -/
theorem alphaStrong_no_totalGapOnly_activeSourceLabelSelector
    (selector :
      AlphaStrongFourSourceClosureReceipt -> AlphaStrongResidualSource)
    (hgap : AlphaStrongFourSourceTotalGapOnly selector)
    (hcorrect :
      AlphaStrongActiveSourceLabelCorrectOnBranchWitnesses selector) :
    False := by
  have hsame :
      selector alphaStrongCanonicalFourSourceReceipt =
        selector alphaStrongThresholdOnlyFourSourceReceipt :=
    alphaStrongFourSourceTotalGapOnly_constant selector hgap
      alphaStrongCanonicalFourSourceReceipt
      alphaStrongThresholdOnlyFourSourceReceipt
  rcases hcorrect with ⟨hcanonical, hthreshold⟩
  rw [hcanonical, hthreshold] at hsame
  exact alphaStrong_canonical_threshold_activeSourceLabels_ne hsame

/-! ## A minimal source-sensitive witness selector -/

/-- A minimal source-label selector that uses finite-source branch membership.

It is not a physical threshold calculation.  It is the smallest source-sensitive
selector witnessing the correct input shape for the future producer. -/
def alphaStrongFiniteSourceActiveSourceSelector
    (R : AlphaStrongFourSourceClosureReceipt) : AlphaStrongResidualSource :=
  by
    classical
    exact
      if AlphaStrongResidualProducerFiniteSourceSurface R.toGapProducer then
        AlphaStrongResidualSource.su7Breaking
      else
        AlphaStrongResidualSource.threshold

/-- THEOREM 4: the minimal source-sensitive selector returns `su7Breaking` on
the canonical receipt. -/
theorem alphaStrongFiniteSourceActiveSourceSelector_canonical :
    alphaStrongFiniteSourceActiveSourceSelector
        alphaStrongCanonicalFourSourceReceipt =
      AlphaStrongResidualSource.su7Breaking := by
  classical
  unfold alphaStrongFiniteSourceActiveSourceSelector
  rw [if_pos alphaStrongCanonicalFourSourceReceipt_sourceSurface]

/-- THEOREM 5: the minimal source-sensitive selector returns `threshold` on
the threshold-only receipt. -/
theorem alphaStrongFiniteSourceActiveSourceSelector_threshold :
    alphaStrongFiniteSourceActiveSourceSelector
        alphaStrongThresholdOnlyFourSourceReceipt =
      AlphaStrongResidualSource.threshold := by
  classical
  unfold alphaStrongFiniteSourceActiveSourceSelector
  rw [if_neg alphaStrongThresholdOnlyFourSourceReceipt_not_sourceSurface]

/-- THEOREM 6: the minimal source-sensitive selector is correct on both branch
witnesses. -/
theorem alphaStrongFiniteSourceActiveSourceSelector_correctOnBranchWitnesses :
    AlphaStrongActiveSourceLabelCorrectOnBranchWitnesses
      alphaStrongFiniteSourceActiveSourceSelector := by
  constructor
  · exact alphaStrongFiniteSourceActiveSourceSelector_canonical
  · exact alphaStrongFiniteSourceActiveSourceSelector_threshold

/-- THEOREM 7: recovering the active-source label is not total-gap-only. -/
theorem alphaStrongFiniteSourceActiveSourceSelector_not_totalGapOnly :
    ¬ AlphaStrongFourSourceTotalGapOnly
        alphaStrongFiniteSourceActiveSourceSelector := by
  intro hgap
  exact
    alphaStrong_no_totalGapOnly_activeSourceLabelSelector
      alphaStrongFiniteSourceActiveSourceSelector
      hgap
      alphaStrongFiniteSourceActiveSourceSelector_correctOnBranchWitnesses

/-! ## Receipt -/

/-- Compact certificate that active-source identity is source-sensitive data,
not scalar-gap data. -/
structure AlphaStrongActiveSourceLabelNoScalarRecoveryCertificate where
  canonical_active_support :
    ∀ s : AlphaStrongResidualSource,
      AlphaStrongResidualActiveSourceSupport
          alphaStrongCanonicalFourSourceReceipt.contribution s ↔
        s = .su7Breaking
  threshold_active_support :
    ∀ s : AlphaStrongResidualSource,
      AlphaStrongResidualActiveSourceSupport
          alphaStrongThresholdOnlyFourSourceReceipt.contribution s ↔
        s = .threshold
  labels_different :
    AlphaStrongResidualSource.su7Breaking ≠
      AlphaStrongResidualSource.threshold
  no_total_gap_only_active_source_selector :
    ∀ selector :
      AlphaStrongFourSourceClosureReceipt -> AlphaStrongResidualSource,
        AlphaStrongFourSourceTotalGapOnly selector ->
        AlphaStrongActiveSourceLabelCorrectOnBranchWitnesses selector ->
          False
  finite_source_selector_correct :
    AlphaStrongActiveSourceLabelCorrectOnBranchWitnesses
      alphaStrongFiniteSourceActiveSourceSelector
  finite_source_selector_not_total_gap_only :
    ¬ AlphaStrongFourSourceTotalGapOnly
        alphaStrongFiniteSourceActiveSourceSelector

/-- THEOREM 8: active-source label no-scalar-recovery certificate. -/
theorem alphaStrongActiveSourceLabelNoScalarRecoveryCertificate :
    AlphaStrongActiveSourceLabelNoScalarRecoveryCertificate where
  canonical_active_support :=
    alphaStrongCanonicalFourSourceReceipt_activeSupport_iff
  threshold_active_support :=
    alphaStrongThresholdOnlyFourSourceReceipt_activeSupport_iff
  labels_different :=
    alphaStrong_canonical_threshold_activeSourceLabels_ne
  no_total_gap_only_active_source_selector := by
    intro selector hgap hcorrect
    exact
      alphaStrong_no_totalGapOnly_activeSourceLabelSelector
        selector hgap hcorrect
  finite_source_selector_correct :=
    alphaStrongFiniteSourceActiveSourceSelector_correctOnBranchWitnesses
  finite_source_selector_not_total_gap_only :=
    alphaStrongFiniteSourceActiveSourceSelector_not_totalGapOnly

end StandardModelConstraint
end SaturationMonoid
