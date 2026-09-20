import H0mework.Physics.AlphaSources.P677

/-!
# Proposition 678: full-beta-vector source-law unified root

P677 welded the explicit even support-code source object to the alpha_s
active-source normal form.  This file makes the physical side equally
source-law shaped.

The key move is small but load-bearing: the full Standard-Model incidence
beta-vector color projection plus the 4D Poincare pairing slots is itself a
P632 `OneAxisFiniteSourceLaw`.  Therefore the same source law, not a loose
collection of numeric receipts, forces:

* the exact alpha_s inverse residual `-89000/128511`;
* the nine Yukawa depths `[50,346,372,489,583,682,880,908,982]`;
* the CKM/Jarlskog depth sum `386`.

We also prove that every accepted input-level full-beta-vector product surface
induces the same one-axis source-law receipt.  The grand root then contains
the current mathematics source object, the alpha_s active-source singleton, and
the full-beta-vector physical source-law receipt in one certificate.

Boundary: this still does not derive the universal one-loop QFT weights,
smooth SU(7) breaking, threshold / three-loop RG, Higgs-extra spectra, the
final Euler/RH adapter range, Goldbach, or RH.  It closes the current finite
source-law root: the proved finite physical nails now descend from the same
source law as the input-level no-free product surface.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Full beta-vector axis as a one-axis source law -/

/-- The full Standard-Model beta-vector axis used by the three-nail finite
producer: color beta-vector projection plus the 4D Poincare slot count. -/
def fullBetaVectorPoincareOneAxis : ℚ :=
  standardModelIncidenceBetaVector.color +
    (AffineRelaxation.GeometryConnection.poincarePairingSlotCount 4 : ℚ)

/-- THEOREM 1: the full beta-vector/Poincare axis is exactly a P632
`OneAxisFiniteSourceLaw`. -/
theorem fullBetaVectorPoincareOneAxis_sourceLaw :
    OneAxisFiniteSourceLaw fullBetaVectorPoincareOneAxis := by
  unfold fullBetaVectorPoincareOneAxis OneAxisFiniteSourceLaw
  rw [qcdBlockInput_betaCoeff_eq_fullBetaVector_color]

/-- THEOREM 2: the full beta-vector source-law axis has value `10`. -/
theorem fullBetaVectorPoincareOneAxis_eq_ten :
    fullBetaVectorPoincareOneAxis = (10 : ℚ) :=
  oneAxisFiniteSourceLaw_eq_ten
    fullBetaVectorPoincareOneAxis_sourceLaw

/-- THEOREM 3: the full beta-vector source law has the reusable P632 receipt.
-/
theorem fullBetaVectorPoincareOneAxisReceipt :
    OneAxisFiniteSourceLawReceipt fullBetaVectorPoincareOneAxis :=
  oneAxisFiniteSourceLawReceipt
    fullBetaVectorPoincareOneAxis_sourceLaw

/-- THEOREM 4: the full beta-vector source-law receipt forces the exact
alpha_s inverse residual. -/
theorem fullBetaVectorPoincareOneAxis_alphaInverseResidual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (oneAxisAlphaStrongGap fullBetaVectorPoincareOneAxis) =
      -((89000 : ℚ) / 128511) :=
  fullBetaVectorPoincareOneAxisReceipt.alpha_inverse_residual

/-- THEOREM 5: the full beta-vector source-law receipt forces the documented
Yukawa mass-order depth list. -/
theorem fullBetaVectorPoincareOneAxis_yukawaMassOrder :
    rationalGridMassOrder
        (gridOfStencil
          (oneAxisYukawaRationalStencil fullBetaVectorPoincareOneAxis)) =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] :=
  fullBetaVectorPoincareOneAxisReceipt.yukawa_mass_order

/-- THEOREM 6: the full beta-vector source-law receipt forces the CKM/Jarlskog
depth sum `386` on the one-axis CKM gap. -/
theorem fullBetaVectorPoincareOneAxis_ckmDepthSum :
    2 * oneAxisCKMSectorGap fullBetaVectorPoincareOneAxis = (386 : ℚ) :=
  fullBetaVectorPoincareOneAxisReceipt.ckm_depth_sum

/-! ## Input-level product surface to source-law receipt -/

/-- THEOREM 7: every accepted input-level full-beta-vector product surface
induces the same P632 one-axis source law through its trace-input axis. -/
theorem fullBetaVectorInputThreeNailProducerSurface_to_oneAxisSourceLaw
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    OneAxisFiniteSourceLaw (incidenceBetaInputOneAxis C.1.betaInput) := by
  rw [fullBetaVectorInputThreeNailProducerSurface_inputAxis_eq_canonical C hC]
  exact
    oneAxisPrimitiveSourceProducer_sourceLaw
      canonicalOneAxisPrimitiveSourceProducer

/-- THEOREM 8: every accepted input-level full-beta-vector product surface
inherits the P632 receipt. -/
theorem fullBetaVectorInputThreeNailProducerSurface_to_oneAxisReceipt
    (C : FullBetaVectorInputThreeNailCandidate)
    (hC : FullBetaVectorInputThreeNailProducerSurface C) :
    OneAxisFiniteSourceLawReceipt (incidenceBetaInputOneAxis C.1.betaInput) :=
  oneAxisFiniteSourceLawReceipt
    (fullBetaVectorInputThreeNailProducerSurface_to_oneAxisSourceLaw C hC)

/-! ## Source-law physical certificate -/

/-- P678 physical certificate: the full beta-vector input surface and the P632
one-axis source law are now explicitly welded. -/
structure FullBetaVectorSourceLawPhysicalCertificate where
  input_surface :
    FullBetaVectorInputThreeNailSurfaceCertificate
  canonical_axis_source_law :
    OneAxisFiniteSourceLaw fullBetaVectorPoincareOneAxis
  canonical_axis_receipt :
    OneAxisFiniteSourceLawReceipt fullBetaVectorPoincareOneAxis
  canonical_axis_eq_ten :
    fullBetaVectorPoincareOneAxis = (10 : ℚ)
  input_surface_no_free :
    NoContinuousFreeFullBetaVectorInputThreeNailParameters
      FullBetaVectorInputThreeNailProducerSurface
  input_surface_to_source_law :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        OneAxisFiniteSourceLaw (incidenceBetaInputOneAxis C.1.betaInput)
  input_surface_to_source_receipt :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        OneAxisFiniteSourceLawReceipt
          (incidenceBetaInputOneAxis C.1.betaInput)
  alpha_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (oneAxisAlphaStrongGap fullBetaVectorPoincareOneAxis) =
      -((89000 : ℚ) / 128511)
  yukawa_mass_order :
    rationalGridMassOrder
        (gridOfStencil
          (oneAxisYukawaRationalStencil fullBetaVectorPoincareOneAxis)) =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  ckm_depth_sum :
    2 * oneAxisCKMSectorGap fullBetaVectorPoincareOneAxis = (386 : ℚ)
  input_surface_alpha_inverse_residual :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            C.1.producedGap =
          -((89000 : ℚ) / 128511)
  input_surface_yukawa_mass_order :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        C.2.massOrder = [50, 346, 372, 489, 583, 682, 880, 908, 982]
  input_surface_ckm_depth_sum :
    ∀ C : FullBetaVectorInputThreeNailCandidate,
      FullBetaVectorInputThreeNailProducerSurface C ->
        ckmJarlskogFourProductDepthSum C.2 = (ckmCPDepthSum : Int)

/-- DEFINITION 1: canonical full-beta-vector source-law physical certificate. -/
def fullBetaVectorSourceLawPhysicalCertificate :
    FullBetaVectorSourceLawPhysicalCertificate where
  input_surface := fullBetaVectorInputThreeNailSurfaceCertificate
  canonical_axis_source_law :=
    fullBetaVectorPoincareOneAxis_sourceLaw
  canonical_axis_receipt :=
    fullBetaVectorPoincareOneAxisReceipt
  canonical_axis_eq_ten :=
    fullBetaVectorPoincareOneAxis_eq_ten
  input_surface_no_free :=
    fullBetaVectorInputThreeNailSurfaceCertificate.no_free
  input_surface_to_source_law :=
    fullBetaVectorInputThreeNailProducerSurface_to_oneAxisSourceLaw
  input_surface_to_source_receipt :=
    fullBetaVectorInputThreeNailProducerSurface_to_oneAxisReceipt
  alpha_inverse_residual :=
    fullBetaVectorPoincareOneAxis_alphaInverseResidual
  yukawa_mass_order :=
    fullBetaVectorPoincareOneAxis_yukawaMassOrder
  ckm_depth_sum :=
    fullBetaVectorPoincareOneAxis_ckmDepthSum
  input_surface_alpha_inverse_residual :=
    fullBetaVectorInputThreeNailSurfaceCertificate.alpha_inverse_residual
  input_surface_yukawa_mass_order :=
    fullBetaVectorInputThreeNailSurfaceCertificate.yukawa_mass_order
  input_surface_ckm_depth_sum :=
    fullBetaVectorInputThreeNailSurfaceCertificate.ckm_jarlskog_sum

end StandardModelConstraint

namespace GrandUnification

open AffineRelaxation
open StandardModelConstraint

universe u

/-! ## Grand root -/

/-- P678 grand root: the mathematics support-code source, the alpha_s
active-source singleton, and the full-beta-vector physical source law sit in
one machine-checked object. -/
structure SourceLawInformationMathMatterEnergyUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p677_root :
    AlphaStrongActiveSourceUnifiedRootCertificate E
  physical_source_law :
    FullBetaVectorSourceLawPhysicalCertificate
  even_support_code_source :
    EvenSupportCodeSourceCertificate
  source_producer_iff_goldbach :
    ∀ S : EvenSupportCodeSource,
      Nonempty S.PullbackProducer ↔ EvenGoldbachStatement
  alpha_active_source_iff_su7 :
    ∀ (P : AlphaStrongResidualGapProducer)
      (_hP : AlphaStrongResidualProducerFiniteSourceSurface P)
      (s : AlphaStrongResidualSource),
        AlphaStrongActiveResidualSource P s ↔ s = .su7Breaking
  physical_input_surface_no_free :
    NoContinuousFreeFullBetaVectorInputThreeNailParameters
      FullBetaVectorInputThreeNailProducerSurface
  physical_source_law_axis :
    OneAxisFiniteSourceLaw fullBetaVectorPoincareOneAxis
  physical_source_law_receipt :
    OneAxisFiniteSourceLawReceipt fullBetaVectorPoincareOneAxis
  physical_alpha_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (oneAxisAlphaStrongGap fullBetaVectorPoincareOneAxis) =
      -((89000 : ℚ) / 128511)
  physical_yukawa_mass_order :
    rationalGridMassOrder
        (gridOfStencil
          (oneAxisYukawaRationalStencil fullBetaVectorPoincareOneAxis)) =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  physical_ckm_depth_sum :
    2 * oneAxisCKMSectorGap fullBetaVectorPoincareOneAxis = (386 : ℚ)

/-- THEOREM 10: the source-law unified root is inhabited. -/
def sourceLawInformationMathMatterEnergyUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    SourceLawInformationMathMatterEnergyUnifiedRootCertificate E where
  p677_root := alphaStrongActiveSourceUnifiedRootCertificate (E := E)
  physical_source_law := fullBetaVectorSourceLawPhysicalCertificate
  even_support_code_source := evenSupportCodeSourceCertificate
  source_producer_iff_goldbach :=
    evenSupportCodeSource_pullbackProducer_iff_goldbach
  alpha_active_source_iff_su7 :=
    alphaStrong_sourceSurface_activeSource_iff_su7Breaking
  physical_input_surface_no_free :=
    fullBetaVectorSourceLawPhysicalCertificate.input_surface_no_free
  physical_source_law_axis :=
    fullBetaVectorSourceLawPhysicalCertificate.canonical_axis_source_law
  physical_source_law_receipt :=
    fullBetaVectorSourceLawPhysicalCertificate.canonical_axis_receipt
  physical_alpha_inverse_residual :=
    fullBetaVectorSourceLawPhysicalCertificate.alpha_inverse_residual
  physical_yukawa_mass_order :=
    fullBetaVectorSourceLawPhysicalCertificate.yukawa_mass_order
  physical_ckm_depth_sum :=
    fullBetaVectorSourceLawPhysicalCertificate.ckm_depth_sum

end GrandUnification
end SaturationMonoid
