import H0mework.Physics.JointSources.P638

/-!
# Proposition 639: total-gap selectors cannot produce the SU7 branch

P638 shows that two four-source receipts can close the same displayed
`alpha_s` scalar while living on different source branches: the canonical
`SU(7)`-only receipt lies on the finite source surface, while the threshold-only
receipt does not.

This file turns that observation into a producer no-go theorem.  Any selector
that only sees the total alpha-level gap is constant on the closed four-source
receipt carrier, hence it cannot distinguish the canonical `SU(7)` branch from
the threshold-only counter-receipt.  Therefore the missing physical producer
must be source-resolved / representation-resolved; a scalar residual producer
is mathematically too weak.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open scoped BigOperators

/-! ## Total-gap-only selectors collapse the four-source carrier -/

/-- The scalar alpha-level gap seen by a receipt after forgetting the four
source coordinates. -/
def alphaStrongFourSourceTotalGap
    (R : AlphaStrongFourSourceClosureReceipt) : ℚ :=
  ∑ s : AlphaStrongResidualSource, R.contribution s

/-- A map out of four-source receipts is total-gap-only when equal scalar gaps
force equal outputs. -/
def AlphaStrongFourSourceTotalGapOnly
    {β : Type*}
    (f : AlphaStrongFourSourceClosureReceipt -> β) : Prop :=
  ∀ R S : AlphaStrongFourSourceClosureReceipt,
    alphaStrongFourSourceTotalGap R =
        alphaStrongFourSourceTotalGap S ->
      f R = f S

/-- THEOREM 1: every closed four-source receipt has the same scalar total gap.
-/
theorem alphaStrongFourSourceTotalGap_eq_displayedGap
    (R : AlphaStrongFourSourceClosureReceipt) :
    alphaStrongFourSourceTotalGap R =
      alphaStrongTwoLoopSMDisplayedGap ℚ := by
  exact R.univ_sum_eq_gap

/-- THEOREM 2: therefore any total-gap-only map is constant on the entire
closed four-source carrier. -/
theorem alphaStrongFourSourceTotalGapOnly_constant
    {β : Type*}
    (f : AlphaStrongFourSourceClosureReceipt -> β)
    (hgap : AlphaStrongFourSourceTotalGapOnly f)
    (R S : AlphaStrongFourSourceClosureReceipt) :
    f R = f S := by
  apply hgap
  rw [alphaStrongFourSourceTotalGap_eq_displayedGap R,
    alphaStrongFourSourceTotalGap_eq_displayedGap S]

/-- THEOREM 3: the canonical `SU(7)` receipt and the threshold-only receipt
have identical scalar total gap. -/
theorem alphaStrongCanonical_threshold_sameTotalGap :
    alphaStrongFourSourceTotalGap
        alphaStrongCanonicalFourSourceReceipt =
      alphaStrongFourSourceTotalGap
        alphaStrongThresholdOnlyFourSourceReceipt := by
  rw [alphaStrongFourSourceTotalGap_eq_displayedGap
        alphaStrongCanonicalFourSourceReceipt,
    alphaStrongFourSourceTotalGap_eq_displayedGap
        alphaStrongThresholdOnlyFourSourceReceipt]

/-- THEOREM 4: a Bool selector that only sees total gap cannot separate the
canonical finite-source branch from the threshold-only closed receipt. -/
theorem alphaStrong_no_totalGapOnly_bool_selector_separates_sourceBranch
    (selector : AlphaStrongFourSourceClosureReceipt -> Bool)
    (hgap : AlphaStrongFourSourceTotalGapOnly selector)
    (hcanonical :
      selector alphaStrongCanonicalFourSourceReceipt = true)
    (hthreshold :
      selector alphaStrongThresholdOnlyFourSourceReceipt = false) :
    False := by
  have hsame :
      selector alphaStrongCanonicalFourSourceReceipt =
        selector alphaStrongThresholdOnlyFourSourceReceipt :=
    alphaStrongFourSourceTotalGapOnly_constant selector hgap
      alphaStrongCanonicalFourSourceReceipt
      alphaStrongThresholdOnlyFourSourceReceipt
  rw [hcanonical, hthreshold] at hsame
  cases hsame

/-! ## The finite-source branch selector is necessarily source-sensitive -/

/-- The branch selector induced by the finite `SU(7)` source surface. -/
def alphaStrongFiniteSourceSurfaceSelector
    (R : AlphaStrongFourSourceClosureReceipt) : Bool :=
  by
    classical
    exact
      if AlphaStrongResidualProducerFiniteSourceSurface R.toGapProducer then
        true
      else
        false

/-- THEOREM 5: the selector accepts the canonical `SU(7)`-only receipt. -/
theorem alphaStrongFiniteSourceSurfaceSelector_canonical :
    alphaStrongFiniteSourceSurfaceSelector
        alphaStrongCanonicalFourSourceReceipt = true := by
  classical
  unfold alphaStrongFiniteSourceSurfaceSelector
  rw [if_pos alphaStrongCanonicalFourSourceReceipt_sourceSurface]

/-- THEOREM 6: the selector rejects the threshold-only receipt. -/
theorem alphaStrongFiniteSourceSurfaceSelector_threshold :
    alphaStrongFiniteSourceSurfaceSelector
        alphaStrongThresholdOnlyFourSourceReceipt = false := by
  classical
  unfold alphaStrongFiniteSourceSurfaceSelector
  rw [if_neg alphaStrongThresholdOnlyFourSourceReceipt_not_sourceSurface]

/-- THEOREM 7: the finite-source selector is not total-gap-only.  It needs
source coordinates, not merely the scalar residual. -/
theorem alphaStrongFiniteSourceSurfaceSelector_not_totalGapOnly :
    ¬ AlphaStrongFourSourceTotalGapOnly
        alphaStrongFiniteSourceSurfaceSelector := by
  intro hgap
  exact
    alphaStrong_no_totalGapOnly_bool_selector_separates_sourceBranch
      alphaStrongFiniteSourceSurfaceSelector
      hgap
      alphaStrongFiniteSourceSurfaceSelector_canonical
      alphaStrongFiniteSourceSurfaceSelector_threshold

/-! ## Receipt -/

/-- Compact certificate that scalar total-gap closure is too weak for the
`alpha_s` producer branch-selection debt. -/
structure AlphaStrongNoScalarBranchSelectionCertificate where
  canonical_threshold_same_total_gap :
    alphaStrongFourSourceTotalGap
        alphaStrongCanonicalFourSourceReceipt =
      alphaStrongFourSourceTotalGap
        alphaStrongThresholdOnlyFourSourceReceipt
  total_gap_only_constant_bool :
    ∀ selector : AlphaStrongFourSourceClosureReceipt -> Bool,
      AlphaStrongFourSourceTotalGapOnly selector ->
        selector alphaStrongCanonicalFourSourceReceipt =
          selector alphaStrongThresholdOnlyFourSourceReceipt
  no_total_gap_only_branch_selector :
    ∀ selector : AlphaStrongFourSourceClosureReceipt -> Bool,
      AlphaStrongFourSourceTotalGapOnly selector ->
      selector alphaStrongCanonicalFourSourceReceipt = true ->
      selector alphaStrongThresholdOnlyFourSourceReceipt = false ->
        False
  finite_source_selector_accepts_canonical :
    alphaStrongFiniteSourceSurfaceSelector
        alphaStrongCanonicalFourSourceReceipt = true
  finite_source_selector_rejects_threshold :
    alphaStrongFiniteSourceSurfaceSelector
        alphaStrongThresholdOnlyFourSourceReceipt = false
  finite_source_selector_not_total_gap_only :
    ¬ AlphaStrongFourSourceTotalGapOnly
        alphaStrongFiniteSourceSurfaceSelector

/-- THEOREM 8: the no-scalar-branch-selection certificate. -/
theorem alphaStrongNoScalarBranchSelectionCertificate :
    AlphaStrongNoScalarBranchSelectionCertificate where
  canonical_threshold_same_total_gap :=
    alphaStrongCanonical_threshold_sameTotalGap
  total_gap_only_constant_bool := by
    intro selector hgap
    exact
      alphaStrongFourSourceTotalGapOnly_constant selector hgap
        alphaStrongCanonicalFourSourceReceipt
        alphaStrongThresholdOnlyFourSourceReceipt
  no_total_gap_only_branch_selector := by
    intro selector hgap hcanonical hthreshold
    exact
      alphaStrong_no_totalGapOnly_bool_selector_separates_sourceBranch
        selector hgap hcanonical hthreshold
  finite_source_selector_accepts_canonical :=
    alphaStrongFiniteSourceSurfaceSelector_canonical
  finite_source_selector_rejects_threshold :=
    alphaStrongFiniteSourceSurfaceSelector_threshold
  finite_source_selector_not_total_gap_only :=
    alphaStrongFiniteSourceSurfaceSelector_not_totalGapOnly

end StandardModelConstraint
end SaturationMonoid
