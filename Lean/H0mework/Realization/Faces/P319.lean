import H0mework.Realization.Faces.P318

/-!
# Proposition 319: faithful pullback is not optional

P318 proves the positive transport theorem:

* if arithmetic completeness and H1-spectral completeness are both faithful
  pullbacks of one self-dual seven-facet global completeness predicate, then
  the two projected completeness predicates are simultaneous.

This file proves the complementary boundary.  Self-duality at `sigma = 1/2`,
even with a self-dual global predicate, does not by itself synchronize
arithmetic and spectral projections.  A mismatch between the projections forces
at least one faithful-pullback condition to fail.

This is the exact reason P318 is a certificate theorem rather than a proof of
Goldbach, RH, or Goldbach <-> RH.  The remaining work is the faithful-pullback
instantiation for the concrete predicates.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## A weaker self-dual carrier with no projection-faithfulness fields -/

/-- A self-dual seven-facet global predicate together with two projected
predicates, but without the faithful-pullback fields required by P318. -/
structure SevenFacetSelfDualGlobalOnly (σ : ℝ) where
  sigma_half : σ = (1 / 2 : ℝ)
  globalComplete : SevenFacetCarrier σ -> Prop
  arithmeticComplete : ℝ -> Prop
  spectralComplete : H1SpectralProjection σ -> Prop
  global_self_dual :
    ∀ x : SevenFacetCarrier σ,
      globalComplete (SevenFacetCarrier.involution x) ↔ globalComplete x

namespace SevenFacetSelfDualGlobalOnly

/-- A pointwise arithmetic pullback obligation. -/
def ArithmeticPullbackAt {σ : ℝ}
    (D : SevenFacetSelfDualGlobalOnly σ) (x : SevenFacetCarrier σ) : Prop :=
  D.arithmeticComplete x.rate ↔ D.globalComplete x

/-- A pointwise H1-spectral pullback obligation. -/
def SpectralPullbackAt {σ : ℝ}
    (D : SevenFacetSelfDualGlobalOnly σ) (x : SevenFacetCarrier σ) : Prop :=
  D.spectralComplete x.spectral ↔ D.globalComplete x

/-- THEOREM 1: any arithmetic/spectral mismatch at a point proves that the two
projected predicates cannot both be faithful pullbacks of the same global
predicate at that point. -/
theorem projection_mismatch_forces_pullback_failure
    {σ : ℝ} (D : SevenFacetSelfDualGlobalOnly σ)
    (x : SevenFacetCarrier σ)
    (hmismatch :
      Not (D.arithmeticComplete x.rate ↔ D.spectralComplete x.spectral)) :
    Not (ArithmeticPullbackAt D x ∧ SpectralPullbackAt D x) := by
  intro hpull
  have hsync :
      D.arithmeticComplete x.rate ↔ D.spectralComplete x.spectral :=
    hpull.1.trans hpull.2.symm
  exact hmismatch hsync

/-- THEOREM 2: global self-duality plus pointwise faithful pullbacks recovers
the P318 synchronization conclusion at that point. -/
theorem synchronized_of_pullbacks_at
    {σ : ℝ} (D : SevenFacetSelfDualGlobalOnly σ)
    (x : SevenFacetCarrier σ)
    (harith : ArithmeticPullbackAt D x)
    (hspec : SpectralPullbackAt D x) :
    D.arithmeticComplete x.rate ↔ D.spectralComplete x.spectral := by
  exact harith.trans hspec.symm

/-- THEOREM 3: global self-duality plus faithful pullbacks at the complemented
point synchronizes the complemented projections. -/
theorem synchronized_at_complement_of_pullbacks_at_complement
    {σ : ℝ} (D : SevenFacetSelfDualGlobalOnly σ)
    (x : SevenFacetCarrier σ)
    (harith :
      ArithmeticPullbackAt D (SevenFacetCarrier.involution x))
    (hspec :
      SpectralPullbackAt D (SevenFacetCarrier.involution x)) :
    D.arithmeticComplete (SevenFacetCarrier.involution x).rate ↔
      D.spectralComplete (SevenFacetCarrier.involution x).spectral := by
  exact harith.trans hspec.symm

end SevenFacetSelfDualGlobalOnly

/-! ## Concrete counterexample: self-duality alone allows projection mismatch -/

/-- A simple half-sigma seven-facet point. -/
def halfSigmaZeroSevenFacetPoint : SevenFacetCarrier (1 / 2 : ℝ) where
  facets := fun _ => True
  rate := 1 / 2
  phase := fun _ _ => 0
  analytic := 0

/-- A self-dual global predicate whose arithmetic projection is constantly
true and spectral projection is constantly false.  It satisfies the weak
self-dual global-only interface, but cannot satisfy P318's faithful-pullback
interface. -/
def selfDualOnlyProjectionMismatch :
    SevenFacetSelfDualGlobalOnly (1 / 2 : ℝ) where
  sigma_half := rfl
  globalComplete := fun _ => True
  arithmeticComplete := fun _ => True
  spectralComplete := fun _ => False
  global_self_dual := by
    intro x
    simp

/-- THEOREM 4: there exists a self-dual half-sigma global carrier where the
arithmetic projection holds and the H1-spectral projection fails at the same
point. -/
theorem selfDual_global_only_counterexample :
    ∃ (D : SevenFacetSelfDualGlobalOnly (1 / 2 : ℝ))
      (x : SevenFacetCarrier (1 / 2 : ℝ)),
      D.globalComplete x ∧
        D.globalComplete (SevenFacetCarrier.involution x) ∧
        D.arithmeticComplete x.rate ∧
        Not (D.spectralComplete x.spectral) := by
  refine ⟨selfDualOnlyProjectionMismatch,
    halfSigmaZeroSevenFacetPoint, ?_⟩
  simp [selfDualOnlyProjectionMismatch]

/-- THEOREM 5: the counterexample has a genuine projection mismatch, therefore
at least one faithful-pullback obligation fails at the witness point. -/
theorem selfDual_counterexample_forces_pullback_failure :
    Not
      (SevenFacetSelfDualGlobalOnly.ArithmeticPullbackAt
        selfDualOnlyProjectionMismatch halfSigmaZeroSevenFacetPoint ∧
      SevenFacetSelfDualGlobalOnly.SpectralPullbackAt
        selfDualOnlyProjectionMismatch halfSigmaZeroSevenFacetPoint) := by
  apply SevenFacetSelfDualGlobalOnly.projection_mismatch_forces_pullback_failure
  simp [selfDualOnlyProjectionMismatch]

/-- THEOREM 6: the counterexample cannot be upgraded to a P318 bridge while
preserving its global, arithmetic, and spectral predicates. -/
theorem selfDual_counterexample_not_upgradable_to_P318_bridge :
    Not
      (∃ B : SevenFacetSelfDualCompletenessBridge (1 / 2 : ℝ),
        (∀ x : SevenFacetCarrier (1 / 2 : ℝ),
          B.globalComplete x ↔
            selfDualOnlyProjectionMismatch.globalComplete x) ∧
        (∀ r : ℝ,
          B.arithmeticComplete r ↔
            selfDualOnlyProjectionMismatch.arithmeticComplete r) ∧
        (∀ p : H1SpectralProjection (1 / 2 : ℝ),
          B.spectralComplete p ↔
            selfDualOnlyProjectionMismatch.spectralComplete p)) := by
  rintro ⟨B, hglobal, harith, hspec⟩
  let x := halfSigmaZeroSevenFacetPoint
  have hsync :
      B.arithmeticComplete x.rate ↔ B.spectralComplete x.spectral :=
    B.arithmetic_iff_spectral x
  have harith_true : B.arithmeticComplete x.rate := by
    exact (harith x.rate).mpr (by simp [selfDualOnlyProjectionMismatch])
  have hspec_false : Not (B.spectralComplete x.spectral) := by
    intro hs
    have : selfDualOnlyProjectionMismatch.spectralComplete x.spectral :=
      (hspec x.spectral).mp hs
    simp [selfDualOnlyProjectionMismatch] at this
  exact hspec_false (hsync.mp harith_true)

/-! ## Packaged necessity certificate -/

/-- A compact certificate for the P319 boundary: faithful pullback is exactly
the missing condition that prevents self-dual projection mismatch. -/
structure FaithfulPullbackNecessityCertificate where
  mismatch_forces_pullback_failure :
    ∀ {σ : ℝ} (D : SevenFacetSelfDualGlobalOnly σ)
      (x : SevenFacetCarrier σ),
      Not (D.arithmeticComplete x.rate ↔ D.spectralComplete x.spectral) ->
      Not (SevenFacetSelfDualGlobalOnly.ArithmeticPullbackAt D x ∧
        SevenFacetSelfDualGlobalOnly.SpectralPullbackAt D x)
  self_dual_counterexample :
    ∃ (D : SevenFacetSelfDualGlobalOnly (1 / 2 : ℝ))
      (x : SevenFacetCarrier (1 / 2 : ℝ)),
      D.globalComplete x ∧
        D.globalComplete (SevenFacetCarrier.involution x) ∧
        D.arithmeticComplete x.rate ∧
        Not (D.spectralComplete x.spectral)
  counterexample_not_upgradable :
    Not
      (∃ B : SevenFacetSelfDualCompletenessBridge (1 / 2 : ℝ),
        (∀ x : SevenFacetCarrier (1 / 2 : ℝ),
          B.globalComplete x ↔
            selfDualOnlyProjectionMismatch.globalComplete x) ∧
        (∀ r : ℝ,
          B.arithmeticComplete r ↔
            selfDualOnlyProjectionMismatch.arithmeticComplete r) ∧
        (∀ p : H1SpectralProjection (1 / 2 : ℝ),
          B.spectralComplete p ↔
            selfDualOnlyProjectionMismatch.spectralComplete p))

/-- THEOREM 7: the canonical faithful-pullback necessity certificate. -/
theorem faithfulPullbackNecessityCertificate :
    FaithfulPullbackNecessityCertificate where
  mismatch_forces_pullback_failure := by
    intro σ D x hmismatch
    exact
      SevenFacetSelfDualGlobalOnly.projection_mismatch_forces_pullback_failure
        D x hmismatch
  self_dual_counterexample := selfDual_global_only_counterexample
  counterexample_not_upgradable :=
    selfDual_counterexample_not_upgradable_to_P318_bridge

end AffineRelaxation
end SaturationMonoid
