import H0mework.Realization.Faces.P320

/-!
# Proposition 321: product-carrier obstruction to the concrete Goldbach/H1 bridge

P320 isolated the remaining concrete bridge as
`ConcreteGoldbachH1FaithfulPullbackObligation`: the concrete half-sigma
Goldbach predicate and the concrete H1 no-obstruction predicate must be
faithful pullbacks of one global seven-facet predicate.

This file proves that, on the current unconstrained product carrier from P318,
that obligation cannot exist.  The reason is not philosophical; it is a small
product-independence theorem.  The carrier lets us hold the arithmetic rate
fixed while varying the H1 spectral phase from exact to obstructed.  A faithful
pullback would then force the same rate predicate to be both equivalent to a
true H1 predicate and to a false one.

Thus the next bridge cannot be another slogan or a different name for the same
product carrier.  It must introduce a coupled seven-facet subcarrier / graph of
admissible arithmetic-spectral states, or else supply an additional relation
that prevents this independent variation.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Two H1 spectral points with the same arithmetic rate -/

/-- The exact H1 spectral point: zero phase has no H1 obstruction. -/
def exactH1SpectralProjection :
    H1SpectralProjection (1 / 2 : ℝ) where
  phase := fun _ _ => 0
  analytic := 0

/-- THEOREM 1: the zero phase is H1 no-obstruction complete. -/
theorem exactH1SpectralProjection_noObstruction :
    H1SpectralNoObstructionComplete exactH1SpectralProjection := by
  rw [h1SpectralNoObstruction_iff_pathAdditive]
  intro i j k
  simp [H1SpectralProjection.consolidatedPhase, cohomologyConsolidationStep,
    exactH1SpectralProjection]

/-- A one-edge real phase around the three-agent ring. -/
def unitRingPhase : ThreeCycleTime -> ThreeCycleTime -> ℝ
  | ThreeCycleTime.t0, ThreeCycleTime.t1 => 1
  | _, _ => 0

/-- THEOREM 2: the unit ring phase has nonzero residual. -/
theorem unitRingPhase_residual :
    threeAgentRingResidual unitRingPhase = 1 := by
  simp [threeAgentRingResidual, unitRingPhase]

/-- The obstructed H1 spectral point: after half-sigma consolidation its
residual is still nonzero, so it has a genuine H1 obstruction. -/
def obstructedH1SpectralProjection :
    H1SpectralProjection (1 / 2 : ℝ) where
  phase := unitRingPhase
  analytic := 0

/-- THEOREM 3: the obstructed point has consolidated H1 obstruction. -/
theorem obstructedH1SpectralProjection_obstruction :
    obstructedH1SpectralProjection.consolidatedH1Obstruction := by
  dsimp [H1SpectralProjection.consolidatedH1Obstruction,
    H1SpectralProjection.consolidatedPhase,
    obstructedH1SpectralProjection]
  exact
    cohomologyConsolidationStep_preserves_h1_of_keep_nonzero
      (σ := (1 / 2 : ℝ)) unitRingPhase
      (by norm_num)
      (by
        rw [unitRingPhase_residual]
        norm_num)

/-- THEOREM 4: the obstructed point is not H1 no-obstruction complete. -/
theorem obstructedH1SpectralProjection_not_noObstruction :
    Not (H1SpectralNoObstructionComplete obstructedH1SpectralProjection) := by
  intro hno
  exact hno obstructedH1SpectralProjection_obstruction

/-! ## The product carrier refutes the concrete faithful-pullback obligation -/

/-- THEOREM 5: on the unconstrained P318 product carrier, the concrete
Goldbach/H1 faithful-pullback obligation cannot exist.

This is the precise algebraic reason the bridge must move to a coupled
seven-facet subcarrier.  The product carrier allows the same arithmetic rate to
be paired with both an exact H1 phase and an obstructed H1 phase. -/
theorem concreteGoldbachH1_obligation_impossible_on_productCarrier :
    Not (Nonempty ConcreteGoldbachH1FaithfulPullbackObligation) := by
  rintro ⟨O⟩
  let facets : Fin 7 -> Prop := fun _ => True
  let rate : ℝ := 0
  let xExact : SevenFacetCarrier (1 / 2 : ℝ) :=
    SevenFacetCarrier.spectralEmbed facets rate exactH1SpectralProjection
  let xObstructed : SevenFacetCarrier (1 / 2 : ℝ) :=
    SevenFacetCarrier.spectralEmbed facets rate obstructedH1SpectralProjection
  have hExact :
      HalfSigmaRateGoldbachComplete rate ↔
        H1SpectralNoObstructionComplete exactH1SpectralProjection := by
    simpa [xExact, SevenFacetCarrier.spectralEmbed, SevenFacetCarrier.spectral]
      using O.goldbach_iff_h1_no_obstruction xExact
  have hObstructed :
      HalfSigmaRateGoldbachComplete rate ↔
        H1SpectralNoObstructionComplete obstructedH1SpectralProjection := by
    simpa [xObstructed, SevenFacetCarrier.spectralEmbed,
      SevenFacetCarrier.spectral]
      using O.goldbach_iff_h1_no_obstruction xObstructed
  have hGoldbach : HalfSigmaRateGoldbachComplete rate :=
    hExact.mpr exactH1SpectralProjection_noObstruction
  have hNoObstruction :
      H1SpectralNoObstructionComplete obstructedH1SpectralProjection :=
    hObstructed.mp hGoldbach
  exact obstructedH1SpectralProjection_not_noObstruction hNoObstruction

/-- A compact certificate for the product-carrier impossibility boundary. -/
structure ProductCarrierObligationImpossibilityCertificate where
  exact_no_obstruction :
    H1SpectralNoObstructionComplete exactH1SpectralProjection
  obstructed_has_obstruction :
    obstructedH1SpectralProjection.consolidatedH1Obstruction
  obstructed_not_no_obstruction :
    Not (H1SpectralNoObstructionComplete obstructedH1SpectralProjection)
  obligation_impossible :
    Not (Nonempty ConcreteGoldbachH1FaithfulPullbackObligation)

/-- THEOREM 6: the canonical product-carrier impossibility certificate. -/
theorem productCarrierObligationImpossibilityCertificate :
    ProductCarrierObligationImpossibilityCertificate where
  exact_no_obstruction := exactH1SpectralProjection_noObstruction
  obstructed_has_obstruction := obstructedH1SpectralProjection_obstruction
  obstructed_not_no_obstruction :=
    obstructedH1SpectralProjection_not_noObstruction
  obligation_impossible :=
    concreteGoldbachH1_obligation_impossible_on_productCarrier

end AffineRelaxation
end SaturationMonoid
