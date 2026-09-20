import H0mework.Physics.AlphaSources.P642

/-!
# Proposition 643: finite geometry has exactly one four-source alpha_s receipt

P641/P642 connect the positive finite-geometry selector to the upstream
block-incidence/QCD/Poincare producer.  This file removes the last branch
freedom on the closed four-source carrier:

`AlphaStrongResidualProducerFiniteGeometrySurface R.toGapProducer`

holds for a closed four-source receipt `R` if and only if `R` is the canonical
SU(7)-only receipt.

Consequences:

* finite geometry does not merely separate the canonical and threshold-only
  examples; it accepts exactly one closed four-source receipt;
* the finite-geometry active-source selector returns `su7Breaking` exactly on
  that canonical receipt;
* the current physical finite-geometry producer's explicit four-source receipt
  is definitionally forced to be the canonical receipt.

Boundary: this is still the finite block-incidence / geometry receipt.  It
proves uniqueness of the accepted closed receipt, not the smooth threshold
spectrum or three-loop RG calculation upstream of that receipt.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Canonical receipt as the unique finite-geometry receipt -/

/-- THEOREM 1: the canonical four-source receipt is exactly the canonical
finite SU7 residual-gap producer after conversion. -/
theorem alphaStrongCanonicalFourSourceReceipt_toGapProducer_eq :
    alphaStrongCanonicalFourSourceReceipt.toGapProducer =
      alphaStrongSU7BreakingResidualGapProducer := by
  exact
    eq_alphaStrongSU7BreakingResidualGapProducer_of_sourceSurface
      alphaStrongCanonicalFourSourceReceipt.toGapProducer
      alphaStrongCanonicalFourSourceReceipt_sourceSurface

/-- THEOREM 2: converting the canonical producer back to the explicit
four-source carrier gives the canonical receipt. -/
theorem alphaStrongSU7BreakingResidualGapProducer_toFourSource_eq_canonical :
    alphaStrongSU7BreakingResidualGapProducer.toFourSourceClosureReceipt =
      alphaStrongCanonicalFourSourceReceipt := by
  calc
    alphaStrongSU7BreakingResidualGapProducer.toFourSourceClosureReceipt =
        alphaStrongCanonicalFourSourceReceipt.toGapProducer.toFourSourceClosureReceipt := by
      rw [alphaStrongCanonicalFourSourceReceipt_toGapProducer_eq]
    _ = alphaStrongCanonicalFourSourceReceipt := by
      exact alphaStrongCanonicalFourSourceReceipt.toGapProducer_toFourSourceClosureReceipt

/-- THEOREM 3: any closed four-source receipt on the finite-geometry surface
is the canonical SU7-only receipt. -/
theorem alphaStrongFiniteGeometrySurface_receipt_eq_canonical
    (R : AlphaStrongFourSourceClosureReceipt)
    (hR :
      AlphaStrongResidualProducerFiniteGeometrySurface R.toGapProducer) :
    R = alphaStrongCanonicalFourSourceReceipt := by
  have hsource :
      AlphaStrongResidualProducerFiniteSourceSurface R.toGapProducer :=
    (alphaStrongResidualProducerFiniteSourceSurface_iff_finiteGeometrySurface
      R.toGapProducer).mpr hR
  have hproducer :
      R.toGapProducer = alphaStrongSU7BreakingResidualGapProducer :=
    eq_alphaStrongSU7BreakingResidualGapProducer_of_sourceSurface
      R.toGapProducer hsource
  have hreceipt :
      R.toGapProducer.toFourSourceClosureReceipt =
        alphaStrongSU7BreakingResidualGapProducer.toFourSourceClosureReceipt :=
    congrArg AlphaStrongResidualGapProducer.toFourSourceClosureReceipt hproducer
  rw [R.toGapProducer_toFourSourceClosureReceipt,
    alphaStrongSU7BreakingResidualGapProducer_toFourSource_eq_canonical]
    at hreceipt
  exact hreceipt

/-- THEOREM 4: finite-geometry surface membership for closed four-source
receipts is equivalent to being the canonical receipt. -/
theorem alphaStrongFiniteGeometrySurface_iff_receipt_eq_canonical
    (R : AlphaStrongFourSourceClosureReceipt) :
    AlphaStrongResidualProducerFiniteGeometrySurface R.toGapProducer ↔
      R = alphaStrongCanonicalFourSourceReceipt := by
  constructor
  · intro hR
    exact alphaStrongFiniteGeometrySurface_receipt_eq_canonical R hR
  · intro hR
    subst hR
    exact alphaStrongCanonicalFourSourceReceipt_finiteGeometrySurface

/-! ## Selector exactness on the full four-source carrier -/

/-- THEOREM 5: the finite-geometry active-source selector returns
`su7Breaking` exactly on the canonical receipt. -/
theorem alphaStrongFiniteGeometryActiveSourceSelector_su7_iff_canonical
    (R : AlphaStrongFourSourceClosureReceipt) :
    alphaStrongFiniteGeometryActiveSourceSelector R =
        AlphaStrongResidualSource.su7Breaking ↔
      R = alphaStrongCanonicalFourSourceReceipt := by
  classical
  constructor
  · intro hsel
    by_cases hgeo :
      AlphaStrongResidualProducerFiniteGeometrySurface R.toGapProducer
    · exact alphaStrongFiniteGeometrySurface_receipt_eq_canonical R hgeo
    · unfold alphaStrongFiniteGeometryActiveSourceSelector at hsel
      rw [if_neg hgeo] at hsel
      cases hsel
  · intro hR
    subst hR
    exact alphaStrongFiniteGeometryActiveSourceSelector_canonical

/-- THEOREM 6: noncanonical closed receipts are sent to the fallback
`threshold` label by the finite-geometry selector. -/
theorem alphaStrongFiniteGeometryActiveSourceSelector_threshold_iff_not_canonical
    (R : AlphaStrongFourSourceClosureReceipt) :
    alphaStrongFiniteGeometryActiveSourceSelector R =
        AlphaStrongResidualSource.threshold ↔
      R ≠ alphaStrongCanonicalFourSourceReceipt := by
  classical
  constructor
  · intro hsel hcanonical
    subst hcanonical
    rw [alphaStrongFiniteGeometryActiveSourceSelector_canonical] at hsel
    cases hsel
  · intro hcanonical
    unfold alphaStrongFiniteGeometryActiveSourceSelector
    rw [if_neg]
    intro hgeo
    exact hcanonical
      (alphaStrongFiniteGeometrySurface_receipt_eq_canonical R hgeo)

/-! ## Physical finite producer receipt is canonical -/

/-- THEOREM 7: the current physical finite-geometry producer's explicit
four-source receipt is the canonical SU7-only receipt. -/
theorem alphaStrongPhysicalFiniteGeometryProducer_toFourSourceReceipt_eq_canonical
    (C : FourDPoincareCertificate.{0})
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    (alphaStrongPhysicalFiniteGeometryProducer C e).toFourSourceClosureReceipt =
      alphaStrongCanonicalFourSourceReceipt := by
  apply alphaStrongFiniteGeometrySurface_receipt_eq_canonical
  simpa [AlphaStrongResidualGapProducer.toFourSourceClosureReceipt_toGapProducer]
    using alphaStrongPhysicalFiniteGeometryProducer_finiteGeometrySurface C e

/-- THEOREM 8: therefore the block-incidence physical producer's four-source
receipt is canonical as well. -/
theorem alphaStrongBlockIncidencePhysicalProducer_toFourSourceReceipt_eq_canonical
    (C : FourDPoincareCertificate.{0})
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    (alphaStrongPhysicalFiniteGeometryProducer C e).toFourSourceClosureReceipt =
      alphaStrongCanonicalFourSourceReceipt :=
  alphaStrongPhysicalFiniteGeometryProducer_toFourSourceReceipt_eq_canonical C e

/-! ## Receipt -/

/-- Compact receipt: finite geometry is an exact canonicalization map on the
closed four-source alpha_s carrier. -/
structure AlphaStrongFiniteGeometryCanonicalReceiptCertificate where
  canonical_to_gap_producer :
    alphaStrongCanonicalFourSourceReceipt.toGapProducer =
      alphaStrongSU7BreakingResidualGapProducer
  canonical_producer_to_receipt :
    alphaStrongSU7BreakingResidualGapProducer.toFourSourceClosureReceipt =
      alphaStrongCanonicalFourSourceReceipt
  geometry_iff_canonical :
    ∀ R : AlphaStrongFourSourceClosureReceipt,
      AlphaStrongResidualProducerFiniteGeometrySurface R.toGapProducer ↔
        R = alphaStrongCanonicalFourSourceReceipt
  selector_su7_iff_canonical :
    ∀ R : AlphaStrongFourSourceClosureReceipt,
      alphaStrongFiniteGeometryActiveSourceSelector R =
          AlphaStrongResidualSource.su7Breaking ↔
        R = alphaStrongCanonicalFourSourceReceipt
  selector_threshold_iff_not_canonical :
    ∀ R : AlphaStrongFourSourceClosureReceipt,
      alphaStrongFiniteGeometryActiveSourceSelector R =
          AlphaStrongResidualSource.threshold ↔
        R ≠ alphaStrongCanonicalFourSourceReceipt
  physical_producer_receipt_canonical :
    ∀ (C : FourDPoincareCertificate.{0})
      (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier),
        (alphaStrongPhysicalFiniteGeometryProducer C e).toFourSourceClosureReceipt =
          alphaStrongCanonicalFourSourceReceipt

/-- THEOREM 9: finite-geometry canonical receipt certificate. -/
theorem alphaStrongFiniteGeometryCanonicalReceiptCertificate :
    AlphaStrongFiniteGeometryCanonicalReceiptCertificate where
  canonical_to_gap_producer :=
    alphaStrongCanonicalFourSourceReceipt_toGapProducer_eq
  canonical_producer_to_receipt :=
    alphaStrongSU7BreakingResidualGapProducer_toFourSource_eq_canonical
  geometry_iff_canonical :=
    alphaStrongFiniteGeometrySurface_iff_receipt_eq_canonical
  selector_su7_iff_canonical :=
    alphaStrongFiniteGeometryActiveSourceSelector_su7_iff_canonical
  selector_threshold_iff_not_canonical :=
    alphaStrongFiniteGeometryActiveSourceSelector_threshold_iff_not_canonical
  physical_producer_receipt_canonical := by
    intro C e
    exact
      alphaStrongPhysicalFiniteGeometryProducer_toFourSourceReceipt_eq_canonical
        C e

end StandardModelConstraint
end SaturationMonoid
