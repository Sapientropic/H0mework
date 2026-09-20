import H0mework.Realization.Faces.P319

/-!
# Proposition 320: concrete projection fidelity, and the remaining cross-bridge

P318 gave the abstract seven-facet projection bridge.  P319 proved that the
faithful-pullback hypotheses are necessary.

This file separates what is already concrete from what remains:

* arithmetic side: P308/P311 already prove that the half-sigma image faithfully
  reflects ordinary Goldbach-shaped additive prime decomposition;
* H1 side: P116/P117/P124 already prove that no H1 obstruction is exactly
  path-additivity, and that selected-ring exactness is residual zero, with
  consolidation scaling by the saturation residual;
* remaining bridge: a concrete Goldbach/H1 theorem must still supply one
  global seven-facet predicate whose faithful pullbacks are exactly those two
  concrete predicates.

Thus the next hard object is not another self-duality slogan.  It is the
`ConcreteGoldbachH1FaithfulPullbackObligation` below.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Concrete arithmetic projection fidelity -/

/-- Goldbach completeness on the half-sigma arithmetic image. -/
def HalfSigmaImageGoldbachComplete (r : HalfSigmaArithmeticImage) : Prop :=
  SigmaGoldbachDecomposition (1 / 2 : ℝ) (SigmaExponentImage.exponent r)

/-- Goldbach completeness on raw rate values, restricted to the half-sigma
sigma-exponent image.  Outside the image it is false. -/
def HalfSigmaRateGoldbachComplete (r : ℝ) : Prop :=
  ∃ x : HalfSigmaArithmeticImage, x.1 = r ∧ HalfSigmaImageGoldbachComplete x

/-- THEOREM 1: image-level half-sigma Goldbach is exactly ordinary additive
prime decomposition of the chosen exponent. -/
theorem halfSigmaImageGoldbachComplete_iff_exponentGoldbach
    (r : HalfSigmaArithmeticImage) :
    HalfSigmaImageGoldbachComplete r ↔
      HasPrimeAdditiveDecomposition (SigmaExponentImage.exponent r) := by
  exact
    sigmaGoldbachDecomposition_iff_goldbach_of_mem_Ioo
      halfSigma_mem_Ioo.1 halfSigma_mem_Ioo.2

/-- THEOREM 2: the raw-rate predicate agrees with the image-level predicate on
image points. -/
theorem halfSigmaRateGoldbachComplete_of_image
    (r : HalfSigmaArithmeticImage) :
    HalfSigmaRateGoldbachComplete r.1 ↔
      HalfSigmaImageGoldbachComplete r := by
  constructor
  · rintro ⟨x, hx, hcomplete⟩
    have hxr : x = r := Subtype.ext hx
    simpa [hxr] using hcomplete
  · intro hcomplete
    exact ⟨r, rfl, hcomplete⟩

/-- THEOREM 3: on named half-sigma exponent points, raw-rate Goldbach is
exactly ordinary additive Goldbach for that exponent. -/
theorem halfSigmaRateGoldbachComplete_iteratedRate_iff
    (n : ℕ) :
    HalfSigmaRateGoldbachComplete (iteratedRate (1 / 2 : ℝ) n) ↔
      HasPrimeAdditiveDecomposition n := by
  let r : HalfSigmaArithmeticImage :=
    SigmaExponentImage.ofNat (1 / 2 : ℝ) n
  have hrate :
      HalfSigmaRateGoldbachComplete r.1 ↔
        HalfSigmaImageGoldbachComplete r :=
    halfSigmaRateGoldbachComplete_of_image r
  have hgold :
      HalfSigmaImageGoldbachComplete r ↔
        HasPrimeAdditiveDecomposition (SigmaExponentImage.exponent r) :=
    halfSigmaImageGoldbachComplete_iff_exponentGoldbach r
  have hexp :
      SigmaExponentImage.exponent r = n :=
    SigmaExponentImage.exponent_ofNat_of_mem_Ioo
      halfSigma_mem_Ioo.1 halfSigma_mem_Ioo.2 n
  change
    HalfSigmaRateGoldbachComplete
        (SigmaExponentImage.ofNat (1 / 2 : ℝ) n).1 ↔
      HasPrimeAdditiveDecomposition n
  simpa [r, hexp] using hrate.trans hgold

/-- THEOREM 4: the half-sigma even global statement is exactly ordinary
Goldbach for even exponents. -/
theorem halfSigmaEvenGoldbach_iff_evenGoldbach :
    SigmaEvenGoldbachStatement (1 / 2 : ℝ) ↔
      EvenGoldbachStatement :=
  sigmaEvenGoldbach_iff_evenGoldbach_of_mem_Ioo
    halfSigma_mem_Ioo.1 halfSigma_mem_Ioo.2

/-! ## Concrete H1-spectral projection fidelity -/

/-- H1-spectral completeness as absence of the consolidated H1 obstruction. -/
def H1SpectralNoObstructionComplete {σ : ℝ}
    (p : H1SpectralProjection σ) : Prop :=
  Not p.consolidatedH1Obstruction

/-- The path-additive/exactness face of the H1-spectral projection. -/
def H1SpectralPathAdditiveComplete {σ : ℝ}
    (p : H1SpectralProjection σ) : Prop :=
  PathAdditive p.consolidatedPhase

/-- Selected-ring exactness for the consolidated three-agent ring. -/
def H1SpectralSelectedRingExact {σ : ℝ}
    (p : H1SpectralProjection σ) : Prop :=
  ThreeAgentRingEdgeExact p.consolidatedPhase

/-- The selected-ring residual-zero predicate for the consolidated ring. -/
def H1SpectralResidualZero {σ : ℝ}
    (p : H1SpectralProjection σ) : Prop :=
  p.consolidatedResidual = 0

/-- THEOREM 5: P116 gives the H1-spectral obstruction criterion after
consolidation. -/
theorem h1SpectralObstruction_iff_not_pathAdditive
    {σ : ℝ} (p : H1SpectralProjection σ) :
    p.consolidatedH1Obstruction ↔
      Not (H1SpectralPathAdditiveComplete p) := by
  exact h1Obstruction_iff_not_pathAdditive p.consolidatedPhase

/-- THEOREM 6: no consolidated H1 obstruction is exactly consolidated
path-additivity. -/
theorem h1SpectralNoObstruction_iff_pathAdditive
    {σ : ℝ} (p : H1SpectralProjection σ) :
    H1SpectralNoObstructionComplete p ↔
      H1SpectralPathAdditiveComplete p := by
  classical
  constructor
  · intro hno
    by_contra hnot
    exact hno ((h1SpectralObstruction_iff_not_pathAdditive p).mpr hnot)
  · intro hpath hobs
    exact ((h1SpectralObstruction_iff_not_pathAdditive p).mp hobs) hpath

/-- THEOREM 7: selected-ring exactness is exactly selected residual zero. -/
theorem h1SpectralSelectedRingExact_iff_residualZero
    {σ : ℝ} (p : H1SpectralProjection σ) :
    H1SpectralSelectedRingExact p ↔ H1SpectralResidualZero p := by
  exact threeAgentRingEdgeExact_iff_residual_zero p.consolidatedPhase

/-- THEOREM 8: at half sigma, consolidated residual is half the original
three-agent ring residual. -/
theorem halfSigma_consolidatedResidual_eq
    (p : H1SpectralProjection (1 / 2 : ℝ)) :
    p.consolidatedResidual =
      (1 / 2 : ℝ) * threeAgentRingResidual p.phase := by
  calc
    p.consolidatedResidual =
        (1 - (1 / 2 : ℝ)) * threeAgentRingResidual p.phase := by
      simpa [H1SpectralProjection.consolidatedResidual,
        H1SpectralProjection.consolidatedPhase]
        using
          (threeAgentRingResidual_consolidationStep
            (1 / 2 : ℝ) p.phase)
    _ = (1 / 2 : ℝ) * threeAgentRingResidual p.phase := by
      ring

/-- THEOREM 9: at half sigma, consolidation preserves the selected residual's
zero/nonzero boundary. -/
theorem halfSigma_consolidatedResidual_zero_iff_original
    (p : H1SpectralProjection (1 / 2 : ℝ)) :
    p.consolidatedResidual = 0 ↔
      threeAgentRingResidual p.phase = 0 := by
  rw [halfSigma_consolidatedResidual_eq p]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hhalf | hres
    · exfalso
      norm_num at hhalf
    · exact hres
  · intro hres
    simp [hres]

/-- THEOREM 10: at half sigma, selected-ring exactness after consolidation is
exactly original selected residual zero. -/
theorem halfSigma_selectedRingExact_iff_originalResidualZero
    (p : H1SpectralProjection (1 / 2 : ℝ)) :
    H1SpectralSelectedRingExact p ↔
      threeAgentRingResidual p.phase = 0 := by
  exact (h1SpectralSelectedRingExact_iff_residualZero p).trans
    (halfSigma_consolidatedResidual_zero_iff_original p)

/-! ## The remaining concrete cross-bridge obligation -/

/-- The concrete obligation left after P308/P311 and P116/P124 have done their
own projection work.

Supplying this structure is exactly the missing faithful-pullback step for the
Goldbach/H1-spectral slogan: one global seven-facet predicate must pull back to
the concrete half-sigma Goldbach predicate on the arithmetic rate projection
and to the concrete no-H1-obstruction predicate on the H1-spectral projection.
-/
structure ConcreteGoldbachH1FaithfulPullbackObligation where
  globalComplete : SevenFacetCarrier (1 / 2 : ℝ) -> Prop
  arithmetic_pullback :
    ∀ x : SevenFacetCarrier (1 / 2 : ℝ),
      HalfSigmaRateGoldbachComplete x.rate ↔ globalComplete x
  spectral_pullback :
    ∀ x : SevenFacetCarrier (1 / 2 : ℝ),
      H1SpectralNoObstructionComplete x.spectral ↔ globalComplete x
  global_self_dual :
    ∀ x : SevenFacetCarrier (1 / 2 : ℝ),
      globalComplete (SevenFacetCarrier.involution x) ↔ globalComplete x

namespace ConcreteGoldbachH1FaithfulPullbackObligation

/-- THEOREM 11: a concrete Goldbach/H1 faithful-pullback obligation is exactly
the missing producer for the P318 bridge specialized to the concrete
predicates. -/
def toSevenFacetSelfDualCompletenessBridge
    (O : ConcreteGoldbachH1FaithfulPullbackObligation) :
    SevenFacetSelfDualCompletenessBridge (1 / 2 : ℝ) where
  sigma_half := rfl
  globalComplete := O.globalComplete
  arithmeticComplete := HalfSigmaRateGoldbachComplete
  spectralComplete := fun p => H1SpectralNoObstructionComplete p
  arithmetic_pullback := O.arithmetic_pullback
  spectral_pullback := O.spectral_pullback
  global_self_dual := O.global_self_dual

/-- THEOREM 12: once the concrete obligation is supplied, the half-sigma
Goldbach projection and the H1 no-obstruction projection are synchronized at
every seven-facet point. -/
theorem goldbach_iff_h1_no_obstruction
    (O : ConcreteGoldbachH1FaithfulPullbackObligation)
    (x : SevenFacetCarrier (1 / 2 : ℝ)) :
    HalfSigmaRateGoldbachComplete x.rate ↔
      H1SpectralNoObstructionComplete x.spectral := by
  exact (O.toSevenFacetSelfDualCompletenessBridge).arithmetic_iff_spectral x

/-- THEOREM 13: any concrete mismatch between the two projections refutes the
existence of a concrete faithful-pullback obligation. -/
theorem no_obligation_of_projection_mismatch
    (x : SevenFacetCarrier (1 / 2 : ℝ))
    (hmismatch :
      Not (HalfSigmaRateGoldbachComplete x.rate ↔
        H1SpectralNoObstructionComplete x.spectral)) :
    Not (Nonempty ConcreteGoldbachH1FaithfulPullbackObligation) := by
  rintro ⟨O⟩
  exact hmismatch (O.goldbach_iff_h1_no_obstruction x)

end ConcreteGoldbachH1FaithfulPullbackObligation

/-! ## Packaged certificate -/

/-- A compact certificate for the concrete projection-fidelity layer. -/
structure ConcreteProjectionFidelityCertificate where
  image_goldbach_iff_exponent_goldbach :
    ∀ r : HalfSigmaArithmeticImage,
      HalfSigmaImageGoldbachComplete r ↔
        HasPrimeAdditiveDecomposition (SigmaExponentImage.exponent r)
  rate_goldbach_on_image :
    ∀ r : HalfSigmaArithmeticImage,
      HalfSigmaRateGoldbachComplete r.1 ↔
        HalfSigmaImageGoldbachComplete r
  rate_goldbach_on_iterated :
    ∀ n : ℕ,
      HalfSigmaRateGoldbachComplete (iteratedRate (1 / 2 : ℝ) n) ↔
        HasPrimeAdditiveDecomposition n
  even_goldbach_iff :
    SigmaEvenGoldbachStatement (1 / 2 : ℝ) ↔ EvenGoldbachStatement
  h1_no_obstruction_iff_path_additive :
    ∀ {σ : ℝ} (p : H1SpectralProjection σ),
      H1SpectralNoObstructionComplete p ↔
        H1SpectralPathAdditiveComplete p
  selected_exact_iff_residual_zero :
    ∀ {σ : ℝ} (p : H1SpectralProjection σ),
      H1SpectralSelectedRingExact p ↔ H1SpectralResidualZero p
  half_sigma_selected_exact_iff_original_residual_zero :
    ∀ p : H1SpectralProjection (1 / 2 : ℝ),
      H1SpectralSelectedRingExact p ↔
        threeAgentRingResidual p.phase = 0

/-- THEOREM 14: the canonical concrete projection-fidelity certificate. -/
theorem concreteProjectionFidelityCertificate :
    ConcreteProjectionFidelityCertificate where
  image_goldbach_iff_exponent_goldbach :=
    halfSigmaImageGoldbachComplete_iff_exponentGoldbach
  rate_goldbach_on_image := halfSigmaRateGoldbachComplete_of_image
  rate_goldbach_on_iterated := halfSigmaRateGoldbachComplete_iteratedRate_iff
  even_goldbach_iff := halfSigmaEvenGoldbach_iff_evenGoldbach
  h1_no_obstruction_iff_path_additive :=
    h1SpectralNoObstruction_iff_pathAdditive
  selected_exact_iff_residual_zero :=
    h1SpectralSelectedRingExact_iff_residualZero
  half_sigma_selected_exact_iff_original_residual_zero :=
    halfSigma_selectedRingExact_iff_originalResidualZero

end AffineRelaxation
end SaturationMonoid
