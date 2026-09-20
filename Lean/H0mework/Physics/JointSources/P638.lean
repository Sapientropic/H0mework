import H0mework.Physics.AlphaSources.P637

/-!
# Proposition 638: four-source pre-collapse redistribution fiber

P637 proves that the current finite `alpha_s` output surface selects
`SU(7)` breaking as the unique active source, and that any nontrivial dynamics
compatible with that collapsed output must live in a pre-collapse fiber.

This file replaces P637's minimal Bool witness by the actual four-source
closure coordinate space.  The key distinction is important:

* many four-source receipts can close the alpha-level gap;
* only the finite source law picks the canonical `SU(7)`-breaking branch;
* therefore the future physical producer must explain a branch-selection /
  collapse map, not merely produce a total gap.

Boundary: this still is not the threshold spectrum or three-loop RG
calculation.  It proves that the correct pre-collapse carrier is already
nontrivial at the four-source accounting level, and that total-gap closure
alone is too weak to replace the SU(7)-branch producer.
-/

noncomputable section

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Two explicit closed four-source receipts -/

/-- The canonical finite-law four-source receipt: all alpha-level residual gap
is carried by `SU(7)` breaking. -/
def alphaStrongCanonicalFourSourceReceipt :
    AlphaStrongFourSourceClosureReceipt where
  su7_breaking := alphaStrongTwoLoopSMDisplayedGap ℚ
  threshold := 0
  three_loop_rg := 0
  higgs_extra_representation := 0
  total_gap := by ring

/-- A noncanonical pre-collapse receipt: the same total alpha-level gap is
carried by the threshold coordinate. -/
def alphaStrongThresholdOnlyFourSourceReceipt :
    AlphaStrongFourSourceClosureReceipt where
  su7_breaking := 0
  threshold := alphaStrongTwoLoopSMDisplayedGap ℚ
  three_loop_rg := 0
  higgs_extra_representation := 0
  total_gap := by ring

/-- THEOREM 1: the canonical receipt's producer lies on the finite SU7 source
surface. -/
theorem alphaStrongCanonicalFourSourceReceipt_sourceSurface :
    AlphaStrongResidualProducerFiniteSourceSurface
      alphaStrongCanonicalFourSourceReceipt.toGapProducer := by
  rw [alphaStrongResidualProducerFiniteSourceSurface_iff_componentNormalForm]
  intro s
  cases s <;>
    simp [alphaStrongCanonicalFourSourceReceipt,
      AlphaStrongFourSourceClosureReceipt.toGapProducer,
      AlphaStrongFourSourceClosureReceipt.contribution,
      alphaStrongTwoLoopAlphaGap_eq_89_div_10000]

/-- THEOREM 2: the threshold-only receipt still closes the displayed `alpha_s`
anchor at the four-source accounting level. -/
theorem alphaStrongThresholdOnlyFourSourceReceipt_closes_displayedAlpha :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            (∑ s : AlphaStrongResidualSource,
              alphaStrongThresholdOnlyFourSourceReceipt.contribution s)) =
      alphaStrongDisplayed ℚ :=
  alphaStrongThresholdOnlyFourSourceReceipt.closes_displayedAlpha

/-- THEOREM 3: total-gap closure alone does not force the finite SU7 source
surface; the threshold-only closed receipt is outside that surface. -/
theorem alphaStrongThresholdOnlyFourSourceReceipt_not_sourceSurface :
    ¬ AlphaStrongResidualProducerFiniteSourceSurface
        alphaStrongThresholdOnlyFourSourceReceipt.toGapProducer := by
  intro hsurface
  have hsu7 :=
    alphaStrong_sourceSurface_su7Contribution_eq_gap
      alphaStrongThresholdOnlyFourSourceReceipt.toGapProducer
      hsurface
  norm_num [alphaStrongThresholdOnlyFourSourceReceipt,
    AlphaStrongFourSourceClosureReceipt.toGapProducer,
    AlphaStrongFourSourceClosureReceipt.contribution,
    alphaStrongTwoLoopSMDisplayedGap,
    alphaStrongDisplayed,
    alphaStrongTwoLoopSMOutput] at hsu7

/-- THEOREM 4: the threshold-only receipt is not the canonical receipt. -/
theorem alphaStrongThresholdOnlyFourSourceReceipt_ne_canonical :
    alphaStrongThresholdOnlyFourSourceReceipt ≠
      alphaStrongCanonicalFourSourceReceipt := by
  intro h
  have hsu7 :=
    congrArg AlphaStrongFourSourceClosureReceipt.su7_breaking h
  norm_num [alphaStrongThresholdOnlyFourSourceReceipt,
    alphaStrongCanonicalFourSourceReceipt,
    alphaStrongTwoLoopSMDisplayedGap,
    alphaStrongDisplayed,
    alphaStrongTwoLoopSMOutput] at hsu7

/-! ## A concrete redistribution dynamics on the four-source carrier -/

/-- A simple redistribution step on closed four-source receipts.

When the receipt is on the canonical SU7 value, it moves to the threshold-only
closed receipt; otherwise it returns to the canonical receipt.  Its purpose is
not to model physical RG, but to witness genuine pre-collapse motion in the
actual four-source accounting carrier. -/
def alphaStrongFourSourceRedistributionStep
    (R : AlphaStrongFourSourceClosureReceipt) :
    AlphaStrongFourSourceClosureReceipt :=
  if R.su7_breaking = alphaStrongTwoLoopSMDisplayedGap ℚ then
    alphaStrongThresholdOnlyFourSourceReceipt
  else
    alphaStrongCanonicalFourSourceReceipt

/-- THEOREM 5: the redistribution step is nontrivial on the canonical receipt.
-/
theorem alphaStrongFourSourceRedistributionStep_nontrivial :
    alphaStrongFourSourceRedistributionStep
        alphaStrongCanonicalFourSourceReceipt ≠
      alphaStrongCanonicalFourSourceReceipt := by
  have hstep :
      alphaStrongFourSourceRedistributionStep
          alphaStrongCanonicalFourSourceReceipt =
        alphaStrongThresholdOnlyFourSourceReceipt := by
    simp [alphaStrongFourSourceRedistributionStep,
      alphaStrongCanonicalFourSourceReceipt]
  rw [hstep]
  exact alphaStrongThresholdOnlyFourSourceReceipt_ne_canonical

/-- The four-source closure space, equipped with a nontrivial redistribution
step, collapses to the canonical finite `alpha_s` residual producer. -/
def fourSourceAlphaStrongPreCollapseDynamics :
    PreCollapseAlphaStrongResidualDynamics where
  Pre := AlphaStrongFourSourceClosureReceipt
  step := alphaStrongFourSourceRedistributionStep
  collapse := fun _ => alphaStrongSU7BreakingResidualGapProducer
  collapse_source_surface := fun _ =>
    alphaStrongSU7BreakingResidualGapProducer_sourceSurface
  step_preserves_collapse := fun _ => rfl
  nontrivial_step :=
    ⟨alphaStrongCanonicalFourSourceReceipt,
      alphaStrongFourSourceRedistributionStep_nontrivial⟩

/-- THEOREM 6: the four-source pre-collapse dynamics has non-injective
collapse. -/
theorem fourSourceAlphaStrongPreCollapseDynamics_collapse_not_injective :
    ¬ Function.Injective fourSourceAlphaStrongPreCollapseDynamics.collapse :=
  fourSourceAlphaStrongPreCollapseDynamics
    |>.collapse_not_injective_of_nontrivial_step

/-! ## Receipt -/

/-- Compact certificate for the four-source pre-collapse redistribution
carrier. -/
structure AlphaStrongFourSourcePreCollapseRedistributionCertificate where
  canonical_receipt_source_surface :
    AlphaStrongResidualProducerFiniteSourceSurface
      alphaStrongCanonicalFourSourceReceipt.toGapProducer
  threshold_only_closes_displayed :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            (∑ s : AlphaStrongResidualSource,
              alphaStrongThresholdOnlyFourSourceReceipt.contribution s)) =
      alphaStrongDisplayed ℚ
  threshold_only_not_source_surface :
    ¬ AlphaStrongResidualProducerFiniteSourceSurface
        alphaStrongThresholdOnlyFourSourceReceipt.toGapProducer
  threshold_only_ne_canonical :
    alphaStrongThresholdOnlyFourSourceReceipt ≠
      alphaStrongCanonicalFourSourceReceipt
  redistribution_step_nontrivial :
    alphaStrongFourSourceRedistributionStep
        alphaStrongCanonicalFourSourceReceipt ≠
      alphaStrongCanonicalFourSourceReceipt
  dynamics :
    PreCollapseAlphaStrongResidualDynamics
  dynamics_is_four_source :
    dynamics = fourSourceAlphaStrongPreCollapseDynamics
  dynamics_collapse_not_injective :
    ¬ Function.Injective dynamics.collapse

/-- THEOREM 7: the four-source pre-collapse redistribution certificate. -/
def alphaStrongFourSourcePreCollapseRedistributionCertificate :
    AlphaStrongFourSourcePreCollapseRedistributionCertificate where
  canonical_receipt_source_surface :=
    alphaStrongCanonicalFourSourceReceipt_sourceSurface
  threshold_only_closes_displayed :=
    alphaStrongThresholdOnlyFourSourceReceipt_closes_displayedAlpha
  threshold_only_not_source_surface :=
    alphaStrongThresholdOnlyFourSourceReceipt_not_sourceSurface
  threshold_only_ne_canonical :=
    alphaStrongThresholdOnlyFourSourceReceipt_ne_canonical
  redistribution_step_nontrivial :=
    alphaStrongFourSourceRedistributionStep_nontrivial
  dynamics :=
    fourSourceAlphaStrongPreCollapseDynamics
  dynamics_is_four_source := rfl
  dynamics_collapse_not_injective :=
    fourSourceAlphaStrongPreCollapseDynamics_collapse_not_injective

end StandardModelConstraint
end SaturationMonoid
