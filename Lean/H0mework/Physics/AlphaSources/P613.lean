import H0mework.Physics.AlphaSources.P611

/-!
# Proposition 613: geometry-witness selector for the alpha_s active source

P609-P611 show that the accepted finite `alpha_s` source law has a unique,
minimal active source, namely `SU(7)` breaking.  This file lowers the selector
one more step.  The active source is characterized by a finite-geometry witness:

* an embedded unified-gauge complement numerator;
* a 4D Poincare-resolution denominator;
* the P602 receipt proving that these two carriers feed the alpha-gap surface.

At the current finite layer, Lean proves that such a witness exists for exactly
one residual source, `su7Breaking`.  Therefore the finite source law is
equivalent to the geometry-witness law: sources with this witness carry the
finite gap, and sources without it carry zero.

Boundary: this is still not the smooth threshold / three-loop / Higgs-spectrum
dynamics.  It turns the remaining producer debt into a sharper obligation:
produce the finite-geometry witness from physical dynamics, rather than merely
name `su7Breaking` as the active coordinate.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Geometry witness for the active residual source -/

/-- A finite-geometry witness for an `alpha_s` residual source.

The witness carries the current P602 geometry: an embedded unified-gauge
complement inside the structural electromagnetic carrier, together with a 4D
Poincare-resolution denominator and its producer receipt.  The equality field
records that this finite geometry activates the `SU(7)`-breaking roadmap
source. -/
def AlphaStrongFiniteGeometryWitness
    (s : AlphaStrongResidualSource) : Prop :=
  ∃ _h : s = .su7Breaking,
    ∃ (C : FourDPoincareCertificate.{0})
      (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier),
      Nonempty (AlphaStrongPoincareResolutionProducerReceipt C e)

/-- THEOREM 1: the current-formal P602 geometry gives a witness for the
`SU(7)`-breaking source. -/
theorem alphaStrongSU7Breaking_hasFiniteGeometryWitness :
    AlphaStrongFiniteGeometryWitness
      AlphaStrongResidualSource.su7Breaking := by
  exact
    ⟨rfl,
      currentFormalFourDPoincareCertificate,
      unifiedGaugeIntoAlphaEMStructural,
      ⟨alphaStrongPoincareResolutionProducerReceipt
        currentFormalFourDPoincareCertificate
        unifiedGaugeIntoAlphaEMStructural⟩⟩

/-- THEOREM 2: an `alpha_s` residual source has the finite-geometry witness iff
it is the `SU(7)`-breaking source. -/
theorem alphaStrongFiniteGeometryWitness_iff_su7
    (s : AlphaStrongResidualSource) :
    AlphaStrongFiniteGeometryWitness s ↔ s = .su7Breaking := by
  constructor
  · intro h
    rcases h with ⟨hs, _C, _e, _receipt⟩
    exact hs
  · intro hs
    subst hs
    exact alphaStrongSU7Breaking_hasFiniteGeometryWitness

/-- THEOREM 3: threshold effects do not carry this finite SU(7)-breaking
geometry witness. -/
theorem alphaStrongThreshold_noFiniteGeometryWitness :
    ¬ AlphaStrongFiniteGeometryWitness
      AlphaStrongResidualSource.threshold := by
  intro h
  have h_eq :=
    (alphaStrongFiniteGeometryWitness_iff_su7
      AlphaStrongResidualSource.threshold).mp h
  cases h_eq

/-- THEOREM 4: three-loop RG effects do not carry this finite SU(7)-breaking
geometry witness. -/
theorem alphaStrongThreeLoopRG_noFiniteGeometryWitness :
    ¬ AlphaStrongFiniteGeometryWitness
      AlphaStrongResidualSource.threeLoopRG := by
  intro h
  have h_eq :=
    (alphaStrongFiniteGeometryWitness_iff_su7
      AlphaStrongResidualSource.threeLoopRG).mp h
  cases h_eq

/-- THEOREM 5: Higgs / extra-representation effects do not carry this finite
SU(7)-breaking geometry witness. -/
theorem alphaStrongHiggsExtra_noFiniteGeometryWitness :
    ¬ AlphaStrongFiniteGeometryWitness
      AlphaStrongResidualSource.higgsExtraRepresentation := by
  intro h
  have h_eq :=
    (alphaStrongFiniteGeometryWitness_iff_su7
      AlphaStrongResidualSource.higgsExtraRepresentation).mp h
  cases h_eq

/-! ## Geometry-witness source law -/

/-- Geometry-witness presentation of the finite source law.

Sources carrying the finite P602 geometry witness get the P581 alpha gap;
sources without that witness get zero. -/
def AlphaStrongFiniteGeometrySourceLaw
    (c : AlphaStrongResidualSource -> ℚ) : Prop :=
  ∀ s : AlphaStrongResidualSource,
    (AlphaStrongFiniteGeometryWitness s ->
        c s = alphaStrongSU7BreakingAlphaGap ℚ) ∧
      (¬ AlphaStrongFiniteGeometryWitness s ->
        c s = 0)

/-- THEOREM 6: the finite SU(7)-breaking contribution law is equivalent to the
geometry-witness source law. -/
theorem alphaStrongSU7FiniteContributionLaw_iff_finiteGeometrySourceLaw
    (c : AlphaStrongResidualSource -> ℚ) :
    AlphaStrongSU7FiniteContributionLaw c ↔
      AlphaStrongFiniteGeometrySourceLaw c := by
  constructor
  · intro hc s
    rcases hc with ⟨hc_su7, hc_threshold, hc_three, hc_higgs⟩
    cases s
    · exact
        ⟨fun _ => hc_su7,
          fun hnone => False.elim
            (hnone alphaStrongSU7Breaking_hasFiniteGeometryWitness)⟩
    · exact
        ⟨fun h => False.elim
            (alphaStrongThreshold_noFiniteGeometryWitness h),
          fun _ => hc_threshold⟩
    · exact
        ⟨fun h => False.elim
            (alphaStrongThreeLoopRG_noFiniteGeometryWitness h),
          fun _ => hc_three⟩
    · exact
        ⟨fun h => False.elim
            (alphaStrongHiggsExtra_noFiniteGeometryWitness h),
          fun _ => hc_higgs⟩
  · intro hgeo
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact
        (hgeo AlphaStrongResidualSource.su7Breaking).1
          alphaStrongSU7Breaking_hasFiniteGeometryWitness
    · exact
        (hgeo AlphaStrongResidualSource.threshold).2
          alphaStrongThreshold_noFiniteGeometryWitness
    · exact
        (hgeo AlphaStrongResidualSource.threeLoopRG).2
          alphaStrongThreeLoopRG_noFiniteGeometryWitness
    · exact
        (hgeo AlphaStrongResidualSource.higgsExtraRepresentation).2
          alphaStrongHiggsExtra_noFiniteGeometryWitness

/-- Producer surface stated by the finite-geometry witness selector. -/
def AlphaStrongResidualProducerFiniteGeometrySurface
    (P : AlphaStrongResidualGapProducer) : Prop :=
  AlphaStrongFiniteGeometrySourceLaw P.contribution

/-- THEOREM 7: the existing finite source surface and the finite-geometry
surface are equivalent. -/
theorem alphaStrongResidualProducerFiniteSourceSurface_iff_finiteGeometrySurface
    (P : AlphaStrongResidualGapProducer) :
    AlphaStrongResidualProducerFiniteSourceSurface P ↔
      AlphaStrongResidualProducerFiniteGeometrySurface P := by
  exact alphaStrongSU7FiniteContributionLaw_iff_finiteGeometrySourceLaw
    P.contribution

/-- THEOREM 8: any producer on the finite-geometry surface has the exact alpha
gap `89/10000`. -/
theorem alphaStrongResidualProducer_finiteGeometrySurface_gap
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteGeometrySurface P) :
    P.producedGap = (89 : ℚ) / 10000 :=
  alphaStrongResidualProducer_sourceSurface_gap P
    ((alphaStrongResidualProducerFiniteSourceSurface_iff_finiteGeometrySurface
      P).mpr hP)

/-- THEOREM 9: any producer on the finite-geometry surface transports to the
exact inverse residual `-89000/128511`. -/
theorem alphaStrongResidualProducer_finiteGeometrySurface_inverseCorrection
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteGeometrySurface P) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        P.producedGap =
      -((89000 : ℚ) / 128511) :=
  alphaStrongResidualProducer_sourceSurface_inverseCorrection P
    ((alphaStrongResidualProducerFiniteSourceSurface_iff_finiteGeometrySurface
      P).mpr hP)

/-! ## Bundled receipt -/

/-- Compact receipt: the active alpha_s source is selected by the finite
geometry witness rather than by a bare source-name assignment. -/
structure AlphaStrongFiniteGeometrySelectorReceipt where
  witness_iff_su7 :
    ∀ s : AlphaStrongResidualSource,
      AlphaStrongFiniteGeometryWitness s ↔ s = .su7Breaking
  law_iff_geometry :
    ∀ c : AlphaStrongResidualSource -> ℚ,
      AlphaStrongSU7FiniteContributionLaw c ↔
        AlphaStrongFiniteGeometrySourceLaw c
  producer_surface_iff_geometry :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ↔
        AlphaStrongResidualProducerFiniteGeometrySurface P
  geometry_gap :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteGeometrySurface P ->
        P.producedGap = (89 : ℚ) / 10000
  geometry_inverse_residual :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteGeometrySurface P ->
        inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            P.producedGap =
          -((89000 : ℚ) / 128511)

/-- THEOREM 10: finite-geometry selector receipt for the current alpha_s
residual producer. -/
theorem alphaStrongFiniteGeometrySelectorReceipt :
    AlphaStrongFiniteGeometrySelectorReceipt where
  witness_iff_su7 := alphaStrongFiniteGeometryWitness_iff_su7
  law_iff_geometry :=
    alphaStrongSU7FiniteContributionLaw_iff_finiteGeometrySourceLaw
  producer_surface_iff_geometry :=
    alphaStrongResidualProducerFiniteSourceSurface_iff_finiteGeometrySurface
  geometry_gap := alphaStrongResidualProducer_finiteGeometrySurface_gap
  geometry_inverse_residual :=
    alphaStrongResidualProducer_finiteGeometrySurface_inverseCorrection

end StandardModelConstraint
end SaturationMonoid
