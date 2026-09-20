import H0mework.Physics.YukawaSources.P606

/-!
# Proposition 607: singleton source surface for the alpha_s residual producer

P597 proved that the finite SU(7)-breaking contribution law is a singleton on
contribution functions.  P602 then fed that law from an embedded-complement
numerator and a 4D Poincare-resolution denominator.  P605/P606 bundled the
current main producer nails and removed packet-level freedom from the
Yukawa/CKM side.

This file performs the analogous tightening on the `alpha_s` side: the whole
`AlphaStrongResidualGapProducer` object is unique on the finite source surface,
not merely its contribution function.  Hence any residual producer whose four
sources satisfy the finite SU(7)-breaking law collapses to the canonical
P581/P597 producer and carries the same alpha gap, inverse residual, and
displayed strong-coupling closure.

Boundary: this still does not compute threshold / three-loop / Higgs-spectrum
dynamics.  It proves that the current finite `alpha_s` source surface has no
producer-object freedom once the finite SU(7)-breaking law is accepted.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## The residual-producer source surface -/

/-- Source surface for an `alpha_s` residual producer: its four-source
contribution function satisfies the finite SU(7)-breaking source law. -/
def AlphaStrongResidualProducerFiniteSourceSurface
    (P : AlphaStrongResidualGapProducer) : Prop :=
  AlphaStrongSU7FiniteContributionLaw P.contribution

/-- THEOREM 1: the canonical finite SU(7)-breaking residual producer lies on
the finite source surface. -/
theorem alphaStrongSU7BreakingResidualGapProducer_sourceSurface :
    AlphaStrongResidualProducerFiniteSourceSurface
      alphaStrongSU7BreakingResidualGapProducer :=
  alphaStrongSU7BreakingResidualGapProducer_contributionLaw

/-- THEOREM 2: the finite source surface is a singleton on full residual
producer objects. -/
theorem eq_alphaStrongSU7BreakingResidualGapProducer_of_sourceSurface
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P) :
    P = alphaStrongSU7BreakingResidualGapProducer := by
  cases P with
  | mk contribution total_gap =>
    unfold AlphaStrongResidualProducerFiniteSourceSurface at hP
    have hContribution :
        contribution =
          alphaStrongSU7BreakingResidualGapProducer.contribution :=
      alphaStrongSU7FiniteContributionLaw_unique
        contribution
        alphaStrongSU7BreakingResidualGapProducer.contribution
        hP
        alphaStrongSU7BreakingResidualGapProducer_contributionLaw
    subst contribution
    rfl

/-! ## Transporting singleton uniqueness to alpha_s output -/

/-- THEOREM 3: any source-surface residual producer has the exact alpha gap
`89/10000`. -/
theorem alphaStrongResidualProducer_sourceSurface_gap
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P) :
    P.producedGap = (89 : ℚ) / 10000 := by
  rw [eq_alphaStrongSU7BreakingResidualGapProducer_of_sourceSurface P hP]
  exact alphaStrongSU7BreakingResidualGapProducer_gap

/-- THEOREM 4: any source-surface residual producer transports to the exact
inverse residual `-89000/128511`. -/
theorem alphaStrongResidualProducer_sourceSurface_inverseCorrection
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        P.producedGap =
      -((89000 : ℚ) / 128511) := by
  rw [eq_alphaStrongSU7BreakingResidualGapProducer_of_sourceSurface P hP]
  rw [alphaStrongSU7BreakingResidualGapProducer_inverseCorrection]
  exact alphaStrongResidualInverseCorrectionNeeded_eq ℚ

/-- THEOREM 5: any source-surface residual producer closes the displayed
strong-coupling alpha value. -/
theorem alphaStrongResidualProducer_sourceSurface_closes_displayedAlpha
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P) :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            P.producedGap) =
      alphaStrongDisplayed ℚ := by
  rw [eq_alphaStrongSU7BreakingResidualGapProducer_of_sourceSurface P hP]
  exact alphaStrongSU7BreakingResidualGapProducer_closes_displayedAlpha

/-! ## Receipt and strengthened main-nails surface -/

/-- Compact receipt for the singleton finite source surface on alpha_s
residual producers. -/
structure AlphaStrongResidualProducerSourceSurfaceReceipt where
  canonical_source :
    AlphaStrongResidualProducerFiniteSourceSurface
      alphaStrongSU7BreakingResidualGapProducer
  source_surface_singleton :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ->
        P = alphaStrongSU7BreakingResidualGapProducer
  alpha_gap :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ->
        P.producedGap = (89 : ℚ) / 10000
  inverse_residual :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ->
        inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            P.producedGap =
          -((89000 : ℚ) / 128511)
  closes_displayed_alpha :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ->
        (1 : ℚ) /
            (alphaStrongTwoLoopSMOutputInverse ℚ +
              inverseCorrectionFromAlphaGap
                (alphaStrongTwoLoopSMOutput ℚ)
                P.producedGap) =
          alphaStrongDisplayed ℚ

/-- THEOREM 6: receipt for the alpha_s residual-producer singleton source
surface. -/
theorem alphaStrongResidualProducerSourceSurfaceReceipt :
    AlphaStrongResidualProducerSourceSurfaceReceipt where
  canonical_source :=
    alphaStrongSU7BreakingResidualGapProducer_sourceSurface
  source_surface_singleton :=
    eq_alphaStrongSU7BreakingResidualGapProducer_of_sourceSurface
  alpha_gap :=
    alphaStrongResidualProducer_sourceSurface_gap
  inverse_residual :=
    alphaStrongResidualProducer_sourceSurface_inverseCorrection
  closes_displayed_alpha :=
    alphaStrongResidualProducer_sourceSurface_closes_displayedAlpha

/-- P606 strengthened again: both the alpha_s residual producer and the
Yukawa primitive-card packet have singleton source surfaces. -/
structure MainProducerNailsFullSourceSurfaceCertificate
    (C : FourDPoincareCertificate)
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) where
  main_source_surface :
    MainProducerNailsSourceSurfaceCertificate C e
  alpha_residual_source_surface :
    AlphaStrongResidualProducerSourceSurfaceReceipt

/-- THEOREM 7: any P606 main-nails input also carries the alpha_s residual
producer singleton source surface. -/
noncomputable def mainProducerNailsFullSourceSurfaceCertificate
    (C : FourDPoincareCertificate)
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    MainProducerNailsFullSourceSurfaceCertificate C e where
  main_source_surface := mainProducerNailsSourceSurfaceCertificate C e
  alpha_residual_source_surface :=
    alphaStrongResidualProducerSourceSurfaceReceipt

/-- THEOREM 8: canonical current-formal P605/P606/P607 combined certificate. -/
noncomputable def canonicalCurrentFormalMainProducerNailsFullSourceSurfaceCertificate :
    MainProducerNailsFullSourceSurfaceCertificate
      currentFormalFourDPoincareCertificate
      unifiedGaugeIntoAlphaEMStructural :=
  mainProducerNailsFullSourceSurfaceCertificate
    currentFormalFourDPoincareCertificate
    unifiedGaugeIntoAlphaEMStructural

end StandardModelConstraint
end SaturationMonoid
