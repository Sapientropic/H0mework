import H0mework.Physics.AlphaSources.P643
import H0mework.Physics.MixingSources.P612

/-!
# Proposition 644: CKM depth sum from the typed Jarlskog four-product

P582 reads the four CKM/Jarlskog depth deltas from the named up/down Yukawa
depth assignment.  P612 gives the typed four-product normal form.  This file
connects the two presentations on the selected table:

* `V_us` is exactly `n_s - n_u = -226`;
* `V_cb` is exactly `n_b - n_c = -143`;
* `V_ub*` is exactly `n_u - n_b = 562`;
* `V_cs*` is exactly `n_s - n_c = 193`;
* therefore the typed Jarlskog four-product depth sum is `386`.

Boundary: this proves the CKM phase-depth sum from the current finite
up/down depth assignment and Jarlskog product.  It still does not derive the
nine depth integers from continuous SU(7)-breaking / consolidation ordering,
nor does it construct the full CKM matrix.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Typed factors equal the named P582 depth deltas -/

/-- THEOREM 1: the typed `V_us` factor is the named `n_s - n_u` delta. -/
theorem selectedCKMJarlskogFactor_V_us_eq_namedDelta :
    CKMJarlskogFactor.depthContribution
        selectedYukawaDepthTableCandidate .V_us =
      ckmDepthDelta_us_fromYukawaDepths := by
  rfl

/-- THEOREM 2: the typed `V_cb` factor is the named `n_b - n_c` delta. -/
theorem selectedCKMJarlskogFactor_V_cb_eq_namedDelta :
    CKMJarlskogFactor.depthContribution
        selectedYukawaDepthTableCandidate .V_cb =
      ckmDepthDelta_cb_fromYukawaDepths := by
  rfl

/-- THEOREM 3: the typed conjugated `V_ub*` factor is the named
`n_u - n_b` delta. -/
theorem selectedCKMJarlskogFactor_V_ub_conj_eq_namedDelta :
    CKMJarlskogFactor.depthContribution
        selectedYukawaDepthTableCandidate .V_ub_conj =
      ckmDepthDelta_ub_conj_fromYukawaDepths := by
  rfl

/-- THEOREM 4: the typed conjugated `V_cs*` factor is the named
`n_s - n_c` delta. -/
theorem selectedCKMJarlskogFactor_V_cs_conj_eq_namedDelta :
    CKMJarlskogFactor.depthContribution
        selectedYukawaDepthTableCandidate .V_cs_conj =
      ckmDepthDelta_cs_conj_fromYukawaDepths := by
  rfl

/-! ## Numeric values and four-product sum -/

/-- THEOREM 5: the selected `V_us` depth contribution is `-226`. -/
theorem selectedCKMJarlskogFactor_V_us_eq_neg226 :
    CKMJarlskogFactor.depthContribution
        selectedYukawaDepthTableCandidate .V_us =
      (-226 : Int) := by
  rw [selectedCKMJarlskogFactor_V_us_eq_namedDelta,
    ckmDepthDelta_us_fromYukawaDepths_eq]
  rfl

/-- THEOREM 6: the selected `V_cb` depth contribution is `-143`. -/
theorem selectedCKMJarlskogFactor_V_cb_eq_neg143 :
    CKMJarlskogFactor.depthContribution
        selectedYukawaDepthTableCandidate .V_cb =
      (-143 : Int) := by
  rw [selectedCKMJarlskogFactor_V_cb_eq_namedDelta,
    ckmDepthDelta_cb_fromYukawaDepths_eq]
  rfl

/-- THEOREM 7: the selected `V_ub*` depth contribution is `562`. -/
theorem selectedCKMJarlskogFactor_V_ub_conj_eq_562 :
    CKMJarlskogFactor.depthContribution
        selectedYukawaDepthTableCandidate .V_ub_conj =
      (562 : Int) := by
  rw [selectedCKMJarlskogFactor_V_ub_conj_eq_namedDelta,
    ckmDepthDelta_ub_conj_fromYukawaDepths_eq]
  rfl

/-- THEOREM 8: the selected `V_cs*` depth contribution is `193`. -/
theorem selectedCKMJarlskogFactor_V_cs_conj_eq_193 :
    CKMJarlskogFactor.depthContribution
        selectedYukawaDepthTableCandidate .V_cs_conj =
      (193 : Int) := by
  rw [selectedCKMJarlskogFactor_V_cs_conj_eq_namedDelta,
    ckmDepthDelta_cs_conj_fromYukawaDepths_eq]
  rfl

/-- THEOREM 9: the typed selected four-product is exactly the named P582
four-delta sum. -/
theorem selectedCKMJarlskogFourProductDepthSum_eq_namedDepthSum :
    ckmJarlskogFourProductDepthSum selectedYukawaDepthTableCandidate =
      ckmDepthSum_fromYukawaDepths := by
  rfl

/-- THEOREM 10: the typed selected four-product depth sum is `386`. -/
theorem selectedCKMJarlskogFourProductDepthSum_eq_386 :
    ckmJarlskogFourProductDepthSum selectedYukawaDepthTableCandidate =
      (ckmCPDepthSum : Int) := by
  rw [selectedCKMJarlskogFourProductDepthSum_eq_namedDepthSum]
  exact ckmDepthSum_fromYukawaDepths_eq_386

/-- THEOREM 11: expanded arithmetic form of the typed four-product:
`-226 + -143 + 562 + 193 = 386`. -/
theorem selectedCKMJarlskogFourProduct_expanded_eq_386 :
    (-226 : Int) + (-143 : Int) + (562 : Int) + (193 : Int) =
      (ckmCPDepthSum : Int) := by
  exact ckmCPDepthDeltas_sum_eq_depthSum

/-! ## Receipt -/

/-- Compact receipt: CKM depth sum `386` is produced by the selected
up/down depth assignment through the typed Jarlskog four-product. -/
structure CKMJarlskogTypedDepthProducerReceipt where
  v_us :
    CKMJarlskogFactor.depthContribution
        selectedYukawaDepthTableCandidate .V_us =
      ckmDepthDelta_us_fromYukawaDepths
  v_cb :
    CKMJarlskogFactor.depthContribution
        selectedYukawaDepthTableCandidate .V_cb =
      ckmDepthDelta_cb_fromYukawaDepths
  v_ub_conj :
    CKMJarlskogFactor.depthContribution
        selectedYukawaDepthTableCandidate .V_ub_conj =
      ckmDepthDelta_ub_conj_fromYukawaDepths
  v_cs_conj :
    CKMJarlskogFactor.depthContribution
        selectedYukawaDepthTableCandidate .V_cs_conj =
      ckmDepthDelta_cs_conj_fromYukawaDepths
  numeric_factors :
    CKMJarlskogFactor.depthContribution
          selectedYukawaDepthTableCandidate .V_us = (-226 : Int) ∧
      CKMJarlskogFactor.depthContribution
          selectedYukawaDepthTableCandidate .V_cb = (-143 : Int) ∧
        CKMJarlskogFactor.depthContribution
            selectedYukawaDepthTableCandidate .V_ub_conj = (562 : Int) ∧
          CKMJarlskogFactor.depthContribution
              selectedYukawaDepthTableCandidate .V_cs_conj = (193 : Int)
  typed_sum :
    ckmJarlskogFourProductDepthSum selectedYukawaDepthTableCandidate =
      ckmDepthSum_fromYukawaDepths
  depth_sum :
    ckmJarlskogFourProductDepthSum selectedYukawaDepthTableCandidate =
      (ckmCPDepthSum : Int)
  expanded_sum :
    (-226 : Int) + (-143 : Int) + (562 : Int) + (193 : Int) =
      (ckmCPDepthSum : Int)

/-- THEOREM 12: typed CKM/Jarlskog depth producer receipt. -/
theorem ckmJarlskogTypedDepthProducerReceipt :
    CKMJarlskogTypedDepthProducerReceipt where
  v_us := selectedCKMJarlskogFactor_V_us_eq_namedDelta
  v_cb := selectedCKMJarlskogFactor_V_cb_eq_namedDelta
  v_ub_conj := selectedCKMJarlskogFactor_V_ub_conj_eq_namedDelta
  v_cs_conj := selectedCKMJarlskogFactor_V_cs_conj_eq_namedDelta
  numeric_factors := by
    exact
      ⟨selectedCKMJarlskogFactor_V_us_eq_neg226,
        selectedCKMJarlskogFactor_V_cb_eq_neg143,
        selectedCKMJarlskogFactor_V_ub_conj_eq_562,
        selectedCKMJarlskogFactor_V_cs_conj_eq_193⟩
  typed_sum := selectedCKMJarlskogFourProductDepthSum_eq_namedDepthSum
  depth_sum := selectedCKMJarlskogFourProductDepthSum_eq_386
  expanded_sum := selectedCKMJarlskogFourProduct_expanded_eq_386

end StandardModelConstraint
end SaturationMonoid
