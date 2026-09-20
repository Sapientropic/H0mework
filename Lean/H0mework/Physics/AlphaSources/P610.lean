import H0mework.Physics.AlphaSources.P609

/-!
# Proposition 610: active-source factorization for the alpha_s residual law

P609 rewrites the finite `alpha_s` source law as a canonical support statement:
`SU(7)` breaking is the unique nonzero / positive source, and the pointwise
component normal form is fixed.

This file removes one more presentation layer.  The accepted four-source
contribution function is exactly the zero-extension of a singleton active
source.  In other words, the current finite residual producer factors through a
one-point active-source carrier; the four-source surface is just its extension
back to the named roadmap source coordinates.

Boundary: this still does not derive why the physical dynamics selects the
singleton active source.  It proves that, once selected, the current finite law
has no extra four-source algebra hidden in its presentation.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Singleton active-source carrier -/

/-- The canonical active source carrier for the current finite alpha_s line:
there is one active coordinate, represented by `PUnit`. -/
abbrev AlphaStrongResidualActiveSourceCarrier :=
  Unit

/-- Embed the singleton active-source carrier into the four roadmap residual
source coordinates. -/
def alphaStrongResidualActiveSourceEmbedding :
    AlphaStrongResidualActiveSourceCarrier -> AlphaStrongResidualSource :=
  fun _ => .su7Breaking

/-- Restrict a four-source contribution function to its active singleton
coordinate. -/
def alphaStrongRestrictToActiveSource
    (c : AlphaStrongResidualSource -> ℚ) :
    AlphaStrongResidualActiveSourceCarrier -> ℚ :=
  fun _ => c .su7Breaking

/-- Extend a singleton active-source contribution back to the four roadmap
source coordinates by zero outside `su7Breaking`. -/
def alphaStrongExtendFromActiveSource
  (a : AlphaStrongResidualActiveSourceCarrier -> ℚ) :
    AlphaStrongResidualSource -> ℚ
  | .su7Breaking => a Unit.unit
  | .threshold => 0
  | .threeLoopRG => 0
  | .higgsExtraRepresentation => 0

/-- The canonical singleton active-source contribution: it carries precisely
the P581/P609 alpha gap. -/
def canonicalAlphaStrongActiveSourceContribution :
    AlphaStrongResidualActiveSourceCarrier -> ℚ :=
  fun _ => (89 : ℚ) / 10000

/-- The canonical four-source contribution is the zero-extension of the
singleton active-source contribution. -/
def canonicalAlphaStrongActiveSourceExtension :
    AlphaStrongResidualSource -> ℚ :=
  alphaStrongExtendFromActiveSource
    canonicalAlphaStrongActiveSourceContribution

/-! ## Factorization theorems -/

/-- THEOREM 1: the canonical singleton extension is exactly P609's pointwise
component normal form. -/
theorem canonicalAlphaStrongActiveSourceExtension_componentNormalForm :
    AlphaStrongSU7ComponentNormalForm
      canonicalAlphaStrongActiveSourceExtension := by
  intro s
  cases s <;>
    simp [canonicalAlphaStrongActiveSourceExtension,
      alphaStrongExtendFromActiveSource,
      canonicalAlphaStrongActiveSourceContribution]

/-- THEOREM 2: the finite contribution law is equivalent to equality with the
canonical singleton active-source extension. -/
theorem alphaStrongSU7FiniteContributionLaw_iff_eq_activeSourceExtension
    (c : AlphaStrongResidualSource -> ℚ) :
    AlphaStrongSU7FiniteContributionLaw c ↔
      c = canonicalAlphaStrongActiveSourceExtension := by
  rw [alphaStrongSU7FiniteContributionLaw_iff_componentNormalForm]
  constructor
  · intro hnormal
    funext s
    rw [hnormal s]
    cases s <;>
      simp [canonicalAlphaStrongActiveSourceExtension,
        alphaStrongExtendFromActiveSource,
        canonicalAlphaStrongActiveSourceContribution]
  · intro hc
    rw [hc]
    exact canonicalAlphaStrongActiveSourceExtension_componentNormalForm

/-- THEOREM 3: any finite-law contribution function factors through the
singleton active-source carrier by restriction and zero-extension. -/
theorem alphaStrongSU7FiniteContributionLaw_extend_restrict_eq
    (c : AlphaStrongResidualSource -> ℚ)
    (hc : AlphaStrongSU7FiniteContributionLaw c) :
    alphaStrongExtendFromActiveSource
        (alphaStrongRestrictToActiveSource c) =
      c := by
  funext s
  rcases hc with ⟨hc_su7, hc_threshold, hc_three, hc_higgs⟩
  cases s <;>
    simp [alphaStrongExtendFromActiveSource,
      alphaStrongRestrictToActiveSource, hc_su7, hc_threshold, hc_three,
      hc_higgs]

/-- THEOREM 4: on the finite law, the singleton active-source coordinate is the
finite alpha gap. -/
theorem alphaStrongSU7FiniteContributionLaw_activeSourceValue
    (c : AlphaStrongResidualSource -> ℚ)
    (hc : AlphaStrongSU7FiniteContributionLaw c)
    (u : AlphaStrongResidualActiveSourceCarrier) :
    alphaStrongRestrictToActiveSource c u = (89 : ℚ) / 10000 := by
  rcases hc with ⟨hc_su7, _, _, _⟩
  rw [alphaStrongRestrictToActiveSource, hc_su7,
    alphaStrongSU7BreakingAlphaGap_eq_89_div_10000]

/-- THEOREM 5: the canonical P581/P597 producer contribution is the canonical
singleton active-source extension. -/
theorem alphaStrongSU7BreakingResidualGapProducer_contribution_eq_activeSourceExtension :
    alphaStrongSU7BreakingResidualGapProducer.contribution =
      canonicalAlphaStrongActiveSourceExtension := by
  exact
    (alphaStrongSU7FiniteContributionLaw_iff_eq_activeSourceExtension
      alphaStrongSU7BreakingResidualGapProducer.contribution).mp
        alphaStrongSU7BreakingResidualGapProducer_contributionLaw

/-- THEOREM 6: finite-source-surface residual producers are exactly those whose
contribution function is the canonical singleton active-source extension. -/
theorem alphaStrongResidualProducerFiniteSourceSurface_iff_contribution_eq_activeSourceExtension
    (P : AlphaStrongResidualGapProducer) :
    AlphaStrongResidualProducerFiniteSourceSurface P ↔
      P.contribution = canonicalAlphaStrongActiveSourceExtension :=
  alphaStrongSU7FiniteContributionLaw_iff_eq_activeSourceExtension
    P.contribution

/-- THEOREM 7: any P608 combined source-surface object has alpha residual
contribution equal to the canonical singleton active-source extension. -/
theorem mainProducerObjectSourceSurface_alphaContribution_eq_activeSourceExtension
    (M : MainProducerObjectCandidate)
    (hM : MainProducerObjectSourceSurface M) :
    M.alphaResidual.contribution =
      canonicalAlphaStrongActiveSourceExtension :=
  (alphaStrongResidualProducerFiniteSourceSurface_iff_contribution_eq_activeSourceExtension
    M.alphaResidual).mp hM.1

/-! ## Receipt -/

/-- Compact receipt: the current finite alpha_s law is the zero-extension of a
singleton active source. -/
structure AlphaStrongActiveSourceFactorizationReceipt where
  component_normal_form :
    AlphaStrongSU7ComponentNormalForm
      canonicalAlphaStrongActiveSourceExtension
  law_iff_extension :
    ∀ c : AlphaStrongResidualSource -> ℚ,
      AlphaStrongSU7FiniteContributionLaw c ↔
        c = canonicalAlphaStrongActiveSourceExtension
  extend_restrict :
    ∀ c : AlphaStrongResidualSource -> ℚ,
      AlphaStrongSU7FiniteContributionLaw c ->
        alphaStrongExtendFromActiveSource
            (alphaStrongRestrictToActiveSource c) =
          c
  active_value :
    ∀ c : AlphaStrongResidualSource -> ℚ,
      AlphaStrongSU7FiniteContributionLaw c ->
        ∀ u : AlphaStrongResidualActiveSourceCarrier,
          alphaStrongRestrictToActiveSource c u = (89 : ℚ) / 10000
  canonical_producer :
    alphaStrongSU7BreakingResidualGapProducer.contribution =
      canonicalAlphaStrongActiveSourceExtension
  producer_surface :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ↔
        P.contribution = canonicalAlphaStrongActiveSourceExtension
  combined_surface :
    ∀ M : MainProducerObjectCandidate,
      MainProducerObjectSourceSurface M ->
        M.alphaResidual.contribution =
          canonicalAlphaStrongActiveSourceExtension

/-- THEOREM 8: active-source factorization receipt for the finite alpha_s
producer law. -/
theorem alphaStrongActiveSourceFactorizationReceipt :
    AlphaStrongActiveSourceFactorizationReceipt where
  component_normal_form :=
    canonicalAlphaStrongActiveSourceExtension_componentNormalForm
  law_iff_extension :=
    alphaStrongSU7FiniteContributionLaw_iff_eq_activeSourceExtension
  extend_restrict :=
    alphaStrongSU7FiniteContributionLaw_extend_restrict_eq
  active_value :=
    alphaStrongSU7FiniteContributionLaw_activeSourceValue
  canonical_producer :=
    alphaStrongSU7BreakingResidualGapProducer_contribution_eq_activeSourceExtension
  producer_surface :=
    alphaStrongResidualProducerFiniteSourceSurface_iff_contribution_eq_activeSourceExtension
  combined_surface :=
    mainProducerObjectSourceSurface_alphaContribution_eq_activeSourceExtension

end StandardModelConstraint
end SaturationMonoid
