import H0mework.Physics.RepresentationSources.P344

/-!
# Proposition 345: the SM representation-action bridge for prime-edge cycles

P343 isolated the exact obstruction gate:

* a prime-edge three-cycle is exact exactly when `p + q = 2n`;
* an SM/facet layer can prove Goldbach only by supplying an allowed-sector
  classifier and then excluding allowed obstructions.

P344 lowered the finite carrier: the three-agent cycle is the color block
inside the explicit `3+2+1+1` Standard-Model carrier.

This file adds the next bridge.  It constructs the concrete block-field action
of the already-proved `diag(C,W,z,z⁻¹)` embedding on fields
`SMBlockFacet -> ℂ`, embeds a prime-edge three-cycle as a color-supported
field, and packages the remaining physics as the smallest honest obligation:
the gauge-invariant/color-singlet predicate must be proved sound and complete
as the P343 allowed sector, while confinement must exclude allowed obstructed
cycles.

The final theorem is deliberately conditional:

`classifier + no allowed obstructed color-cycle -> Goldbach`.

So the proposed Standard-Model route has a precise proof target, but no hidden
"QCD proves Goldbach" shortcut is smuggled in.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace StandardModelConstraint

open GaugeProjection
open GaugeProjection.ConcreteBlockDiagonal
open SaturationMonoid.AffineRelaxation

/-! ## Concrete block-field action -/

/-- A complex field over the seven Standard-Model block facets. -/
abbrev SMBlockField := SMBlockFacet -> ℂ

/-- Transport a block-facet field to P286's nested block-index carrier. -/
def smBlockFieldToIndex (v : SMBlockField) : SMBlockIndex -> ℂ :=
  fun i => v (smBlockIndexToFacet i)

/-- Transport a P286 block-index field back to the explicit block-facet
carrier. -/
def smBlockFieldFromIndex (v : SMBlockIndex -> ℂ) : SMBlockField :=
  fun x => v (smBlockFacetToIndex x)

@[simp]
theorem smBlockFieldFromIndex_toIndex (v : SMBlockField) :
    smBlockFieldFromIndex (smBlockFieldToIndex v) = v := by
  ext x
  simp [smBlockFieldFromIndex, smBlockFieldToIndex]

@[simp]
theorem smBlockFieldToIndex_fromIndex (v : SMBlockIndex -> ℂ) :
    smBlockFieldToIndex (smBlockFieldFromIndex v) = v := by
  ext i
  simp [smBlockFieldFromIndex, smBlockFieldToIndex]

/-- The concrete Standard-Model block action on the seven-facet field carrier,
transported from the P286 block matrix `diag(C,W,z,z⁻¹)`. -/
def smGaugeBlockAction (g : StandardModelGaugeGroup)
    (v : SMBlockField) : SMBlockField :=
  smBlockFieldFromIndex
    (Matrix.mulVec (rawBlockDiagonal g) (smBlockFieldToIndex v))

/-- THEOREM 1: the identity gauge element acts trivially on block fields. -/
theorem smGaugeBlockAction_one (v : SMBlockField) :
    smGaugeBlockAction 1 v = v := by
  ext x
  simp [smGaugeBlockAction]

/-- THEOREM 2: the concrete block action composes as a left action. -/
theorem smGaugeBlockAction_mul
    (g h : StandardModelGaugeGroup) (v : SMBlockField) :
    smGaugeBlockAction (g * h) v =
      smGaugeBlockAction g (smGaugeBlockAction h v) := by
  ext x
  simp [smGaugeBlockAction, rawBlockDiagonal_mul, Matrix.mulVec_mulVec]

/-- THEOREM 3: the pure color factor acts on the color block by the fundamental
`SU(3)` matrix. -/
theorem smGaugeBlockAction_colorInclusion_color
    (c : SU3Gauge) (v : SMBlockField) (i : Fin 3) :
    smGaugeBlockAction (standardModelColorInclusion c) v
        (SMBlockFacet.color i) =
      Matrix.mulVec (c : Matrix (Fin 3) (Fin 3) ℂ)
        (fun j : Fin 3 => v (SMBlockFacet.color j)) i := by
  simp [smGaugeBlockAction, smBlockFieldFromIndex, smBlockFieldToIndex,
    smBlockFacetToIndex, smBlockIndexToFacet, standardModelColorInclusion,
    rawBlockDiagonal, Matrix.mulVec, dotProduct]

/-- THEOREM 4: the pure color factor leaves weak components untouched. -/
theorem smGaugeBlockAction_colorInclusion_weak
    (c : SU3Gauge) (v : SMBlockField) (i : Fin 2) :
    smGaugeBlockAction (standardModelColorInclusion c) v
        (SMBlockFacet.weak i) =
      v (SMBlockFacet.weak i) := by
  fin_cases i <;>
    simp [smGaugeBlockAction, smBlockFieldFromIndex, smBlockFieldToIndex,
      smBlockFacetToIndex, smBlockIndexToFacet, standardModelColorInclusion,
      rawBlockDiagonal, weakHyperchargeBlock, hyperchargePairBlock,
      scalarOneBlock, Matrix.mulVec, dotProduct]

/-- THEOREM 5: the pure color factor leaves the hypercharge component
untouched. -/
theorem smGaugeBlockAction_colorInclusion_hypercharge
    (c : SU3Gauge) (v : SMBlockField) :
    smGaugeBlockAction (standardModelColorInclusion c) v
        SMBlockFacet.hypercharge =
      v SMBlockFacet.hypercharge := by
  simp [smGaugeBlockAction, smBlockFieldFromIndex, smBlockFieldToIndex,
    smBlockFacetToIndex, smBlockIndexToFacet, standardModelColorInclusion,
    rawBlockDiagonal, weakHyperchargeBlock, hyperchargePairBlock,
    scalarOneBlock, Matrix.mulVec, dotProduct]

/-- THEOREM 6: the pure color factor leaves the anti-hypercharge component
untouched. -/
theorem smGaugeBlockAction_colorInclusion_antiHypercharge
    (c : SU3Gauge) (v : SMBlockField) :
    smGaugeBlockAction (standardModelColorInclusion c) v
        SMBlockFacet.antiHypercharge =
      v SMBlockFacet.antiHypercharge := by
  simp [smGaugeBlockAction, smBlockFieldFromIndex, smBlockFieldToIndex,
    smBlockFacetToIndex, smBlockIndexToFacet, standardModelColorInclusion,
    rawBlockDiagonal, weakHyperchargeBlock, hyperchargePairBlock,
    scalarOneBlock, Matrix.mulVec, dotProduct]

/-! ## Prime-edge cycles as color-supported fields -/

/-- The three selected prime-edge phases embedded as a color-supported field:

* color `0` stores `p`;
* color `1` stores `q`;
* color `2` stores `-2n`;
* weak/hypercharge coordinates are zero.

This is the concrete carrier on which a future color-singlet / confinement law
must act. -/
def primeEdgeColorField (n : ℕ) (p q : PrimeExponent) : SMBlockField
  | SMBlockFacet.color i =>
      if i = (0 : Fin 3) then (p.1 : ℂ)
      else if i = (1 : Fin 3) then (q.1 : ℂ)
      else -((2 * n : ℕ) : ℂ)
  | SMBlockFacet.weak _ => 0
  | SMBlockFacet.hypercharge => 0
  | SMBlockFacet.antiHypercharge => 0

/-- THEOREM 7: the embedded prime-edge field is supported only on color
facets. -/
theorem primeEdgeColorField_vanishes_off_color
    (n : ℕ) (p q : PrimeExponent)
    {x : SMBlockFacet} (hx : ¬ IsColorFacet x) :
    primeEdgeColorField n p q x = 0 := by
  cases x <;> simp [primeEdgeColorField, IsColorFacet] at hx ⊢

/-- Color-singlet / gauge-invariant status for a block field under the color
factor.  This is a mathematical predicate on the concrete representation
action, not an arbitrary P343 `allowed` predicate. -/
def ColorSingletBlockField (v : SMBlockField) : Prop :=
  ∀ c : SU3Gauge, smGaugeBlockAction (standardModelColorInclusion c) v = v

/-- The gauge-invariant predicate for a prime-edge color cycle.  Future
representation/QCD work must prove the exact laws this predicate satisfies. -/
def PrimeEdgeColorSinglet
    (n : ℕ) (p q : PrimeExponent) : Prop :=
  ColorSingletBlockField (primeEdgeColorField n p q)

/-- The P343 sector whose allowed predicate is no longer arbitrary: it is
derived from the concrete color-singlet predicate on the SM block action. -/
def colorSingletPrimeEdgeSector : SMAllowedPrimeEdgeSector :=
  concreteSMAllowedPrimeEdgeSector PrimeEdgeColorSinglet

/-- The remaining exact physics/representation obligation for the color-singlet
route.  It is intentionally separated from the already-proved finite carrier
and action facts above.

`sound`: a color-singlet obstructed prime-edge cycle is a genuine witness that
the even number has no prime decomposition.

`complete`: if an even number has no prime decomposition, the color-singlet
sector exposes that failure as an obstructed prime-edge cycle.
-/
structure ColorSingletGoldbachObstructionLaw : Prop where
  sound :
    ∀ {n : ℕ} {p q : PrimeExponent},
      2 ≤ n -> PrimeEdgeColorSinglet n p q ->
        PrimeEdgeThreeCycleObstructed n p q ->
          ¬ HasPrimeAdditiveDecomposition (2 * n)
  complete :
    ∀ {n : ℕ}, 2 ≤ n ->
      ¬ HasPrimeAdditiveDecomposition (2 * n) ->
        ∃ p q : PrimeExponent,
          PrimeEdgeColorSinglet n p q ∧
            PrimeEdgeThreeCycleObstructed n p q

/-- THEOREM 8: the color-singlet Goldbach law is exactly the missing P343
classifier for the color-singlet-derived SM allowed sector. -/
theorem colorSingletLaw_to_smGoldbachClassifier
    (L : ColorSingletGoldbachObstructionLaw) :
    SMGoldbachObstructionClassifier colorSingletPrimeEdgeSector where
  obstruction_sound := by
    intro n p q hn hallowed hobs
    exact L.sound hn hallowed hobs
  obstruction_complete := by
    intro n hn hbad
    exact L.complete hn hbad

/-- A confinement-style no-obstruction claim for the concrete color-singlet
sector.  This is the place where QCD/confinement must eventually land. -/
def ColorConfinementExcludesPrimeEdgeObstructions : Prop :=
  ¬ SMAllowedObstructedPrimeEdgeCycle colorSingletPrimeEdgeSector

/-- THEOREM 9: once the color-singlet classifier and confinement-style
exclusion are proved, ordinary Goldbach follows. -/
theorem colorConfinement_plus_classifier_implies_evenGoldbach
    (L : ColorSingletGoldbachObstructionLaw)
    (Hconf : ColorConfinementExcludesPrimeEdgeObstructions) :
    EvenGoldbachStatement :=
  (no_smAllowedObstructedPrimeEdgeCycle_iff_evenGoldbach
    (colorSingletLaw_to_smGoldbachClassifier L)).mp Hconf

/-- THEOREM 10: conversely, if ordinary Goldbach failed, then any proved
color-singlet classifier would force a concrete SM-allowed obstructed color
cycle.  This is the exact falsification target for the proposed SM route. -/
theorem not_goldbach_forces_colorSinglet_obstruction
    (L : ColorSingletGoldbachObstructionLaw)
    (hbad : ¬ EvenGoldbachStatement) :
    SMAllowedObstructedPrimeEdgeCycle colorSingletPrimeEdgeSector :=
  (smAllowedObstructedPrimeEdgeCycle_iff_not_evenGoldbach
    (colorSingletLaw_to_smGoldbachClassifier L)).mpr hbad

/-- THEOREM 11: a color-singlet allowed obstruction still carries the concrete
three-agent H¹ obstruction from P343. -/
theorem colorSingletAllowedObstruction_h1
    (h : SMAllowedObstructedPrimeEdgeCycle colorSingletPrimeEdgeSector) :
    ∃ n : ℕ, ∃ p q : PrimeExponent,
      2 ≤ n ∧ PrimeEdgeColorSinglet n p q ∧
        CechAdditiveCover.H1Obstruction
          (identityPairZeroTripleCover ThreeCycleTime Int)
          (primeEdgeThreeCycleCochain n p q) :=
  smAllowedObstructedPrimeEdgeCycle_h1 h

/-- A compact certificate for the concrete SM representation-action bridge and
the remaining color-singlet/confinement proof target. -/
structure P345SMRepresentationGoldbachBridgeCertificate : Prop where
  action_one :
    ∀ v : SMBlockField, smGaugeBlockAction 1 v = v
  action_mul :
    ∀ (g h : StandardModelGaugeGroup) (v : SMBlockField),
      smGaugeBlockAction (g * h) v =
        smGaugeBlockAction g (smGaugeBlockAction h v)
  color_factor_on_color :
    ∀ (c : SU3Gauge) (v : SMBlockField) (i : Fin 3),
      smGaugeBlockAction (standardModelColorInclusion c) v
          (SMBlockFacet.color i) =
        Matrix.mulVec (c : Matrix (Fin 3) (Fin 3) ℂ)
          (fun j : Fin 3 => v (SMBlockFacet.color j)) i
  color_factor_leaves_weak :
    ∀ (c : SU3Gauge) (v : SMBlockField) (i : Fin 2),
      smGaugeBlockAction (standardModelColorInclusion c) v
          (SMBlockFacet.weak i) =
        v (SMBlockFacet.weak i)
  color_field_off_color_zero :
    ∀ (n : ℕ) (p q : PrimeExponent)
      {x : SMBlockFacet}, ¬ IsColorFacet x ->
        primeEdgeColorField n p q x = 0
  color_singlet_law_to_classifier :
    ColorSingletGoldbachObstructionLaw ->
      SMGoldbachObstructionClassifier colorSingletPrimeEdgeSector
  confinement_plus_classifier_implies_goldbach :
    ColorSingletGoldbachObstructionLaw ->
      ColorConfinementExcludesPrimeEdgeObstructions ->
        EvenGoldbachStatement
  not_goldbach_forces_color_singlet_obstruction :
    ColorSingletGoldbachObstructionLaw ->
      ¬ EvenGoldbachStatement ->
        SMAllowedObstructedPrimeEdgeCycle colorSingletPrimeEdgeSector
  color_singlet_allowed_obstruction_h1 :
    SMAllowedObstructedPrimeEdgeCycle colorSingletPrimeEdgeSector ->
      ∃ n : ℕ, ∃ p q : PrimeExponent,
        2 ≤ n ∧ PrimeEdgeColorSinglet n p q ∧
          CechAdditiveCover.H1Obstruction
            (identityPairZeroTripleCover ThreeCycleTime Int)
            (primeEdgeThreeCycleCochain n p q)

/-- THEOREM 12: the representation-action bridge is machine-checked; the only
unproved scientific input is explicitly named as
`ColorSingletGoldbachObstructionLaw` plus confinement-style exclusion. -/
theorem p345SMRepresentationGoldbachBridgeCertificate :
    P345SMRepresentationGoldbachBridgeCertificate where
  action_one := smGaugeBlockAction_one
  action_mul := smGaugeBlockAction_mul
  color_factor_on_color := smGaugeBlockAction_colorInclusion_color
  color_factor_leaves_weak := smGaugeBlockAction_colorInclusion_weak
  color_field_off_color_zero := by
    intro n p q x hx
    exact primeEdgeColorField_vanishes_off_color n p q hx
  color_singlet_law_to_classifier := colorSingletLaw_to_smGoldbachClassifier
  confinement_plus_classifier_implies_goldbach :=
    colorConfinement_plus_classifier_implies_evenGoldbach
  not_goldbach_forces_color_singlet_obstruction :=
    not_goldbach_forces_colorSinglet_obstruction
  color_singlet_allowed_obstruction_h1 :=
    colorSingletAllowedObstruction_h1

end StandardModelConstraint
end SaturationMonoid
