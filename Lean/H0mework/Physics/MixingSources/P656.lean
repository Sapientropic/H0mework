import Mathlib.Tactic
import H0mework.Physics.AlphaSources.P655

/-!
# Proposition 656: CKM/Jarlskog depth sum from the primitive-card closed stencil

P654 compresses the Yukawa nail to one closed primitive-card stencil:

`evalAt (primitiveCardYukawaDepthStencilCoefficientVector P) x y`.

P644/P649 prove that the typed CKM/Jarlskog four-product reads the selected
Yukawa table as

`V_us = n_s - n_u`, `V_cb = n_b - n_c`,
`V_ub* = n_u - n_b`, and `V_cs* = n_s - n_c`,

with depth sum `386`.

This file welds those two statements directly: turn the P654 closed stencil
itself into a `YukawaDepthTableCandidate`, then prove the typed Jarlskog
factors and their normal form from that table.  This removes one presentation
layer from the CKM nail: the phase-depth sum is read from the same closed
primitive-card stencil that produces the nine Yukawa depths.

Boundary: this remains the phase-depth producer.  It does not construct the
full CKM matrix or derive the primitive-card source equations from smooth
SU(7)-breaking / consolidation dynamics.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

open InformationMatterProjection

/-! ## Closed-stencil table -/

/-- The P654 closed primitive-card formula repackaged as a Yukawa depth table.
-/
def yukawaPrimitiveCardClosedDepthTableCandidate
    (P : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot) :
    YukawaDepthTableCandidate where
  depth := yukawaPrimitiveCardEndpointClosedDepthFormulaOf P f

/-- THEOREM 1: primitive-card source equations plus endpoint preservation force
the closed-stencil table to be the selected Yukawa depth table. -/
theorem yukawaPrimitiveCardClosedDepthTableCandidate_eq_selected
    (P : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot)
    (hP : YukawaPrimitiveCardSourceEquations P)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f) :
    yukawaPrimitiveCardClosedDepthTableCandidate P f =
      selectedYukawaDepthTableCandidate := by
  ext y
  exact yukawaPrimitiveCardEndpointClosedDepthFormulaOf_eq_selectedDepthZ
    P f hP hf y

/-! ## Typed CKM/Jarlskog factors from the closed-stencil table -/

/-- THEOREM 2: the closed-stencil table forces `V_us = -226`. -/
theorem closedStencilCKMJarlskogFactor_V_us_eq_neg226
    (P : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot)
    (hP : YukawaPrimitiveCardSourceEquations P)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f) :
    CKMJarlskogFactor.depthContribution
        (yukawaPrimitiveCardClosedDepthTableCandidate P f) .V_us =
      (-226 : Int) := by
  rw [yukawaPrimitiveCardClosedDepthTableCandidate_eq_selected P f hP hf]
  exact selectedCKMJarlskogFactor_V_us_eq_neg226

/-- THEOREM 3: the closed-stencil table forces `V_cb = -143`. -/
theorem closedStencilCKMJarlskogFactor_V_cb_eq_neg143
    (P : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot)
    (hP : YukawaPrimitiveCardSourceEquations P)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f) :
    CKMJarlskogFactor.depthContribution
        (yukawaPrimitiveCardClosedDepthTableCandidate P f) .V_cb =
      (-143 : Int) := by
  rw [yukawaPrimitiveCardClosedDepthTableCandidate_eq_selected P f hP hf]
  exact selectedCKMJarlskogFactor_V_cb_eq_neg143

/-- THEOREM 4: the closed-stencil table forces `V_ub* = 562`. -/
theorem closedStencilCKMJarlskogFactor_V_ub_conj_eq_562
    (P : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot)
    (hP : YukawaPrimitiveCardSourceEquations P)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f) :
    CKMJarlskogFactor.depthContribution
        (yukawaPrimitiveCardClosedDepthTableCandidate P f) .V_ub_conj =
      (562 : Int) := by
  rw [yukawaPrimitiveCardClosedDepthTableCandidate_eq_selected P f hP hf]
  exact selectedCKMJarlskogFactor_V_ub_conj_eq_562

/-- THEOREM 5: the closed-stencil table forces `V_cs* = 193`. -/
theorem closedStencilCKMJarlskogFactor_V_cs_conj_eq_193
    (P : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot)
    (hP : YukawaPrimitiveCardSourceEquations P)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f) :
    CKMJarlskogFactor.depthContribution
        (yukawaPrimitiveCardClosedDepthTableCandidate P f) .V_cs_conj =
      (193 : Int) := by
  rw [yukawaPrimitiveCardClosedDepthTableCandidate_eq_selected P f hP hf]
  exact selectedCKMJarlskogFactor_V_cs_conj_eq_193

/-! ## Normal form and depth sum -/

/-- THEOREM 6: the closed-stencil table has strange/charm gap `193`. -/
theorem closedStencilCharmStrangeGap_eq_193
    (P : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot)
    (hP : YukawaPrimitiveCardSourceEquations P)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f) :
    charmStrangeDepthGap
        (yukawaPrimitiveCardClosedDepthTableCandidate P f) =
      (193 : Int) := by
  rw [yukawaPrimitiveCardClosedDepthTableCandidate_eq_selected P f hP hf]
  exact selectedYukawaDepthTableCandidate_charmStrangeGap_eq_193

/-- THEOREM 7: the closed-stencil Jarlskog four-product has the structural
normal form `2*(n_s-n_c)`. -/
theorem closedStencilCKMJarlskogFourProduct_normalForm
    (P : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot) :
    ckmJarlskogFourProductDepthSum
        (yukawaPrimitiveCardClosedDepthTableCandidate P f) =
      2 *
        charmStrangeDepthGap
          (yukawaPrimitiveCardClosedDepthTableCandidate P f) := by
  exact ckmJarlskogFourProductDepthSum_normalForm
    (yukawaPrimitiveCardClosedDepthTableCandidate P f)

/-- THEOREM 8: the closed-stencil table forces CKM/Jarlskog depth sum `386`.
-/
theorem closedStencilCKMJarlskogFourProductDepthSum_eq_386
    (P : YukawaCoefficientPrimitiveCardPacket)
    (f : YukawaInteractionSector -> InformationSlot)
    (hP : YukawaPrimitiveCardSourceEquations P)
    (hf : YukawaSectorEndpointSignaturePreservingSchedule f) :
    ckmJarlskogFourProductDepthSum
        (yukawaPrimitiveCardClosedDepthTableCandidate P f) =
      (ckmCPDepthSum : Int) := by
  rw [yukawaPrimitiveCardClosedDepthTableCandidate_eq_selected P f hP hf]
  exact selectedCKMJarlskogFourProductDepthSum_eq_386

/-! ## Certificate -/

/-- Compact certificate: the CKM/Jarlskog phase-depth nail is read directly
from the P654 primitive-card closed stencil table. -/
structure CKMJarlskogClosedStencilProducerCertificate where
  closed_stencil :
    YukawaPrimitiveCardClosedStencilProducerCertificate
  finite_jarlskog :
    CKMFiniteJarlskogProducerDebtClosureCertificate
  table_forced :
    ∀ (P : YukawaCoefficientPrimitiveCardPacket)
      (f : YukawaInteractionSector -> InformationSlot),
        YukawaPrimitiveCardSourceEquations P ->
          YukawaSectorEndpointSignaturePreservingSchedule f ->
            yukawaPrimitiveCardClosedDepthTableCandidate P f =
              selectedYukawaDepthTableCandidate
  factors_forced :
    ∀ (P : YukawaCoefficientPrimitiveCardPacket)
      (f : YukawaInteractionSector -> InformationSlot),
        YukawaPrimitiveCardSourceEquations P ->
          YukawaSectorEndpointSignaturePreservingSchedule f ->
            CKMJarlskogFactor.depthContribution
                (yukawaPrimitiveCardClosedDepthTableCandidate P f)
                .V_us = (-226 : Int) ∧
              CKMJarlskogFactor.depthContribution
                  (yukawaPrimitiveCardClosedDepthTableCandidate P f)
                  .V_cb = (-143 : Int) ∧
                CKMJarlskogFactor.depthContribution
                    (yukawaPrimitiveCardClosedDepthTableCandidate P f)
                    .V_ub_conj = (562 : Int) ∧
                  CKMJarlskogFactor.depthContribution
                      (yukawaPrimitiveCardClosedDepthTableCandidate P f)
                      .V_cs_conj = (193 : Int)
  normal_form :
    ∀ (P : YukawaCoefficientPrimitiveCardPacket)
      (f : YukawaInteractionSector -> InformationSlot),
        ckmJarlskogFourProductDepthSum
            (yukawaPrimitiveCardClosedDepthTableCandidate P f) =
          2 *
            charmStrangeDepthGap
              (yukawaPrimitiveCardClosedDepthTableCandidate P f)
  depth_sum :
    ∀ (P : YukawaCoefficientPrimitiveCardPacket)
      (f : YukawaInteractionSector -> InformationSlot),
        YukawaPrimitiveCardSourceEquations P ->
          YukawaSectorEndpointSignaturePreservingSchedule f ->
            ckmJarlskogFourProductDepthSum
                (yukawaPrimitiveCardClosedDepthTableCandidate P f) =
              (ckmCPDepthSum : Int)

/-- THEOREM 9: closed-stencil CKM/Jarlskog producer certificate. -/
theorem ckmJarlskogClosedStencilProducerCertificate :
    CKMJarlskogClosedStencilProducerCertificate where
  closed_stencil := yukawaPrimitiveCardClosedStencilProducerCertificate
  finite_jarlskog := ckmFiniteJarlskogProducerDebtClosureCertificate
  table_forced := yukawaPrimitiveCardClosedDepthTableCandidate_eq_selected
  factors_forced := by
    intro P f hP hf
    exact
      ⟨closedStencilCKMJarlskogFactor_V_us_eq_neg226 P f hP hf,
        closedStencilCKMJarlskogFactor_V_cb_eq_neg143 P f hP hf,
        closedStencilCKMJarlskogFactor_V_ub_conj_eq_562 P f hP hf,
        closedStencilCKMJarlskogFactor_V_cs_conj_eq_193 P f hP hf⟩
  normal_form := closedStencilCKMJarlskogFourProduct_normalForm
  depth_sum := closedStencilCKMJarlskogFourProductDepthSum_eq_386

end StandardModelConstraint
end SaturationMonoid
