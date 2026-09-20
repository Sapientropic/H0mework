import H0mework.Physics.SourceForms.P608

/-!
# Proposition 609: canonical active source for the alpha_s residual producer

P607/P608 prove that the current finite `alpha_s` residual-producer surface is
a singleton.  This file sharpens the same surface in support language: the
finite contribution law is equivalent to saying that the `SU(7)`-breaking
source is the unique nonzero residual source and that it carries the P581
finite alpha gap.

This is still not a threshold / three-loop / Higgs-spectrum calculation.  It
does remove another presentation choice: the current finite law is no longer
only a four-field assignment; it is exactly the canonical active-source support
law for the residual producer.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Active-source support -/

/-- Nonzero source support for an alpha_s residual contribution function. -/
def AlphaStrongResidualActiveSourceSupport
    (c : AlphaStrongResidualSource -> ℚ)
    (s : AlphaStrongResidualSource) : Prop :=
  c s ≠ 0

/-- Positive source support for an alpha_s residual contribution function. -/
def AlphaStrongResidualPositiveSourceSupport
    (c : AlphaStrongResidualSource -> ℚ)
    (s : AlphaStrongResidualSource) : Prop :=
  0 < c s

/-- The active-source presentation of the finite SU(7)-breaking law: the SU(7)
source carries the finite alpha gap, and it is the only nonzero source. -/
def AlphaStrongSU7ActiveSourceSupportLaw
    (c : AlphaStrongResidualSource -> ℚ) : Prop :=
  c .su7Breaking = alphaStrongSU7BreakingAlphaGap ℚ ∧
    ∀ s : AlphaStrongResidualSource,
      AlphaStrongResidualActiveSourceSupport c s ↔
        s = .su7Breaking

/-- Pointwise component normal form for the finite SU(7)-breaking law. -/
def AlphaStrongSU7ComponentNormalForm
    (c : AlphaStrongResidualSource -> ℚ) : Prop :=
  ∀ s : AlphaStrongResidualSource,
    c s =
      match s with
      | .su7Breaking => (89 : ℚ) / 10000
      | .threshold => 0
      | .threeLoopRG => 0
      | .higgsExtraRepresentation => 0

/-! ## Equivalence with the finite contribution law -/

/-- THEOREM 1: under the finite contribution law, the nonzero source support is
exactly the singleton `{su7Breaking}`. -/
theorem alphaStrongSU7FiniteContributionLaw_activeSupport_iff
    (c : AlphaStrongResidualSource -> ℚ)
    (hc : AlphaStrongSU7FiniteContributionLaw c)
    (s : AlphaStrongResidualSource) :
    AlphaStrongResidualActiveSourceSupport c s ↔
      s = .su7Breaking := by
  rcases hc with ⟨hc_su7, hc_threshold, hc_three, hc_higgs⟩
  cases s <;>
    simp [AlphaStrongResidualActiveSourceSupport, hc_su7, hc_threshold,
      hc_three, hc_higgs, alphaStrongSU7BreakingAlphaGap_eq_89_div_10000]

/-- THEOREM 2: under the finite contribution law, the positive source support
is also exactly the singleton `{su7Breaking}`. -/
theorem alphaStrongSU7FiniteContributionLaw_positiveSupport_iff
    (c : AlphaStrongResidualSource -> ℚ)
    (hc : AlphaStrongSU7FiniteContributionLaw c)
    (s : AlphaStrongResidualSource) :
    AlphaStrongResidualPositiveSourceSupport c s ↔
      s = .su7Breaking := by
  rcases hc with ⟨hc_su7, hc_threshold, hc_three, hc_higgs⟩
  cases s <;>
    simp [AlphaStrongResidualPositiveSourceSupport, hc_su7, hc_threshold,
      hc_three, hc_higgs, alphaStrongSU7BreakingAlphaGap_eq_89_div_10000]

/-- THEOREM 3: the active-source support law is equivalent to the finite
SU(7)-breaking contribution law. -/
theorem alphaStrongSU7FiniteContributionLaw_iff_activeSourceSupportLaw
    (c : AlphaStrongResidualSource -> ℚ) :
    AlphaStrongSU7FiniteContributionLaw c ↔
      AlphaStrongSU7ActiveSourceSupportLaw c := by
  constructor
  · intro hc
    rcases hc with ⟨hc_su7, hc_threshold, hc_three, hc_higgs⟩
    constructor
    · exact hc_su7
    · intro s
      cases s <;>
        simp [AlphaStrongResidualActiveSourceSupport, hc_su7, hc_threshold,
          hc_three, hc_higgs, alphaStrongSU7BreakingAlphaGap_eq_89_div_10000]
  · intro hsupport
    rcases hsupport with ⟨hsu7, hnonzero⟩
    refine ⟨hsu7, ?_, ?_, ?_⟩
    · by_contra hthreshold
      have heq :
          AlphaStrongResidualSource.threshold =
            AlphaStrongResidualSource.su7Breaking :=
        (hnonzero AlphaStrongResidualSource.threshold).mp hthreshold
      cases heq
    · by_contra hthree
      have heq :
          AlphaStrongResidualSource.threeLoopRG =
            AlphaStrongResidualSource.su7Breaking :=
        (hnonzero AlphaStrongResidualSource.threeLoopRG).mp hthree
      cases heq
    · by_contra hhiggs
      have heq :
          AlphaStrongResidualSource.higgsExtraRepresentation =
            AlphaStrongResidualSource.su7Breaking :=
        (hnonzero AlphaStrongResidualSource.higgsExtraRepresentation).mp
          hhiggs
      cases heq

/-- THEOREM 4: the finite contribution law is equivalent to a pointwise
component normal form. -/
theorem alphaStrongSU7FiniteContributionLaw_iff_componentNormalForm
    (c : AlphaStrongResidualSource -> ℚ) :
    AlphaStrongSU7FiniteContributionLaw c ↔
      AlphaStrongSU7ComponentNormalForm c := by
  constructor
  · intro hc
    rcases hc with ⟨hc_su7, hc_threshold, hc_three, hc_higgs⟩
    intro s
    cases s <;>
      simp [hc_su7, hc_threshold, hc_three, hc_higgs,
        alphaStrongSU7BreakingAlphaGap_eq_89_div_10000]
  · intro hnormal
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hnormal AlphaStrongResidualSource.su7Breaking]
      rw [alphaStrongSU7BreakingAlphaGap_eq_89_div_10000]
    · exact hnormal AlphaStrongResidualSource.threshold
    · exact hnormal AlphaStrongResidualSource.threeLoopRG
    · exact hnormal AlphaStrongResidualSource.higgsExtraRepresentation

/-! ## Producer-level support theorem -/

/-- Source surface for a producer expressed by canonical active-source support.
-/
def AlphaStrongResidualProducerActiveSourceSurface
    (P : AlphaStrongResidualGapProducer) : Prop :=
  AlphaStrongSU7ActiveSourceSupportLaw P.contribution

/-- THEOREM 4: the finite producer source surface and the active-source source
surface are definitionally equivalent. -/
theorem alphaStrongResidualProducerFiniteSourceSurface_iff_activeSourceSurface
    (P : AlphaStrongResidualGapProducer) :
    AlphaStrongResidualProducerFiniteSourceSurface P ↔
      AlphaStrongResidualProducerActiveSourceSurface P := by
  exact alphaStrongSU7FiniteContributionLaw_iff_activeSourceSupportLaw
    P.contribution

/-- THEOREM 5: the finite producer source surface is equivalent to the
pointwise component normal form. -/
theorem alphaStrongResidualProducerFiniteSourceSurface_iff_componentNormalForm
    (P : AlphaStrongResidualGapProducer) :
    AlphaStrongResidualProducerFiniteSourceSurface P ↔
      AlphaStrongSU7ComponentNormalForm P.contribution := by
  exact alphaStrongSU7FiniteContributionLaw_iff_componentNormalForm
    P.contribution

/-- THEOREM 6: any finite-source-surface residual producer has exactly one
nonzero source: `su7Breaking`. -/
theorem alphaStrongResidualProducer_sourceSurface_activeSupport_iff
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P)
    (s : AlphaStrongResidualSource) :
    AlphaStrongResidualActiveSourceSupport P.contribution s ↔
      s = .su7Breaking :=
  alphaStrongSU7FiniteContributionLaw_activeSupport_iff P.contribution hP s

/-- THEOREM 7: any finite-source-surface residual producer has exactly one
positive source: `su7Breaking`. -/
theorem alphaStrongResidualProducer_sourceSurface_positiveSupport_iff
    (P : AlphaStrongResidualGapProducer)
    (hP : AlphaStrongResidualProducerFiniteSourceSurface P)
    (s : AlphaStrongResidualSource) :
    AlphaStrongResidualPositiveSourceSupport P.contribution s ↔
      s = .su7Breaking :=
  alphaStrongSU7FiniteContributionLaw_positiveSupport_iff P.contribution hP s

/-- THEOREM 8: on the combined P608 source surface, the alpha residual source
support is still exactly `{su7Breaking}`. -/
theorem mainProducerObjectSourceSurface_alphaActiveSupport_iff
    (M : MainProducerObjectCandidate)
    (hM : MainProducerObjectSourceSurface M)
    (s : AlphaStrongResidualSource) :
    AlphaStrongResidualActiveSourceSupport M.alphaResidual.contribution s ↔
      s = .su7Breaking :=
  alphaStrongResidualProducer_sourceSurface_activeSupport_iff
    M.alphaResidual hM.1 s

/-! ## Receipt -/

/-- Compact receipt: the current alpha_s residual finite law has a canonical
active-source presentation, and the active source is uniquely `SU(7)` breaking.
-/
structure AlphaStrongCanonicalActiveSourceReceipt where
  law_iff_support :
    ∀ c : AlphaStrongResidualSource -> ℚ,
      AlphaStrongSU7FiniteContributionLaw c ↔
        AlphaStrongSU7ActiveSourceSupportLaw c
  law_iff_component_normal_form :
    ∀ c : AlphaStrongResidualSource -> ℚ,
      AlphaStrongSU7FiniteContributionLaw c ↔
        AlphaStrongSU7ComponentNormalForm c
  producer_surface_iff :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ↔
        AlphaStrongResidualProducerActiveSourceSurface P
  producer_surface_iff_component_normal_form :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ↔
        AlphaStrongSU7ComponentNormalForm P.contribution
  active_support :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ->
        ∀ s : AlphaStrongResidualSource,
          AlphaStrongResidualActiveSourceSupport P.contribution s ↔
            s = .su7Breaking
  positive_support :
    ∀ P : AlphaStrongResidualGapProducer,
      AlphaStrongResidualProducerFiniteSourceSurface P ->
        ∀ s : AlphaStrongResidualSource,
          AlphaStrongResidualPositiveSourceSupport P.contribution s ↔
            s = .su7Breaking
  combined_active_support :
    ∀ M : MainProducerObjectCandidate,
      MainProducerObjectSourceSurface M ->
        ∀ s : AlphaStrongResidualSource,
          AlphaStrongResidualActiveSourceSupport
              M.alphaResidual.contribution s ↔
            s = .su7Breaking

/-- THEOREM 8: canonical active-source receipt for the current alpha_s
residual producer. -/
theorem alphaStrongCanonicalActiveSourceReceipt :
    AlphaStrongCanonicalActiveSourceReceipt where
  law_iff_support :=
    alphaStrongSU7FiniteContributionLaw_iff_activeSourceSupportLaw
  law_iff_component_normal_form :=
    alphaStrongSU7FiniteContributionLaw_iff_componentNormalForm
  producer_surface_iff :=
    alphaStrongResidualProducerFiniteSourceSurface_iff_activeSourceSurface
  producer_surface_iff_component_normal_form :=
    alphaStrongResidualProducerFiniteSourceSurface_iff_componentNormalForm
  active_support :=
    alphaStrongResidualProducer_sourceSurface_activeSupport_iff
  positive_support :=
    alphaStrongResidualProducer_sourceSurface_positiveSupport_iff
  combined_active_support :=
    mainProducerObjectSourceSurface_alphaActiveSupport_iff

end StandardModelConstraint
end SaturationMonoid
