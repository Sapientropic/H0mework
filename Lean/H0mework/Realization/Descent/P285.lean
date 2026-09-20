import H0mework.Realization.Descent.P284

/-!
# Proposition 285: good-cover local Poincare producers

P284 proves the one-chart analytic bridge: a closed `1`-form on an open convex
domain has a primitive, and that primitive gives an exact local Čech slice.

This file lifts that result one level up the geometry track.  Given an open
cover whose chart domains are exactly open convex domains carrying closed
`1`-forms, choose the Poincare primitive on each chart.  The resulting
additive overlap transitions are continuous on overlaps, and every basepoint
Čech slice is exact, path-additive, and non-obstructed.

Boundary: this is a good-cover producer for the exact additive slice.  It is
not the full global Čech-de Rham theorem, not manifold de Rham cohomology, not
Poincare duality, and not a gauge-field or curvature construction.
-/

namespace SaturationMonoid
namespace AffineRelaxation
namespace GeometryConnection

noncomputable section

variable {Index E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-! ## Convex good-cover closed `1`-form data -/

/-- A good-cover analytic producer for the exact Čech/de Rham slice.

Each chart of the topological cover is required to be the domain of a closed
`1`-form in the sense used by Mathlib's local Poincare lemma.
-/
structure ConvexClosedOneFormGoodCoverData
    (Index E F : Type*) [TopologicalSpace E]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  cover : TopologicalPrincipalCover E Index
  chart : Index -> ConvexClosedOneFormData E F
  chart_domain_eq_cover : ∀ i, (chart i).domain = cover.U i

namespace ConvexClosedOneFormGoodCoverData

/-- The Poincare primitive selected on chart `i`. -/
def primitive
    (D : ConvexClosedOneFormGoodCoverData Index E F) (i : Index) :
    ConvexClosedOneFormData.PrimitiveCertificate (D.chart i) :=
  Classical.choice (D.chart i).exists_primitive_certificate

/-- The chartwise local potential selected by the Poincare lemma. -/
def potential
    (D : ConvexClosedOneFormGoodCoverData Index E F) :
    Index -> E -> F :=
  fun i => (D.primitive i).potential

/-- THEOREM 1: the selected local potential differentiates to the given closed
`1`-form on its chart. -/
theorem potential_hasFDerivAt
    (D : ConvexClosedOneFormGoodCoverData Index E F)
    (i : Index) (x : E) (hx : x ∈ D.cover.U i) :
    HasFDerivAt (D.potential i) ((D.chart i).omega x) x := by
  exact
    (D.primitive i).derivative_eq_one_form x
      (by simpa [D.chart_domain_eq_cover i] using hx)

/-- THEOREM 2: each selected local potential is continuous on its chart. -/
theorem potential_continuousOn
    (D : ConvexClosedOneFormGoodCoverData Index E F)
    (i : Index) :
    ContinuousOn (D.potential i) (D.cover.U i) := by
  simpa [potential, D.chart_domain_eq_cover i] using
    (D.primitive i).continuousOn

/-- THEOREM 3: chartwise Poincare primitives induce additive transitions that
are continuous on chart overlaps. -/
theorem additiveTransition_continuousOn
    (D : ConvexClosedOneFormGoodCoverData Index E F) :
    ContinuousOnAdditiveTransitions D.cover
      (topologicalAdditiveExactTransition D.potential) := by
  intro i j
  have hj :
      ContinuousOn (D.potential j) (D.cover.overlap i j) :=
    (D.potential_continuousOn j).mono (by
      intro x hx
      exact hx.2)
  have hi :
      ContinuousOn (D.potential i) (D.cover.overlap i j) :=
    (D.potential_continuousOn i).mono (by
      intro x hx
      exact hx.1)
  exact hj.sub hi

/-- THEOREM 4: every basepoint Čech slice of the good-cover transition is a
1-coboundary. -/
theorem cech_oneCoboundary
    (D : ConvexClosedOneFormGoodCoverData Index E F) (x : E) :
    CechAdditiveCover.OneCoboundary
      (identityPairZeroTripleCover Index F)
      (cechTransitionAt D.potential x) :=
  cechTransitionAt_oneCoboundary D.potential x

/-- THEOREM 5: every basepoint Čech slice of the good-cover transition is
path-additive / flat. -/
theorem cech_pathAdditive
    (D : ConvexClosedOneFormGoodCoverData Index E F) (x : E) :
    PathAdditive (cechTransitionAt D.potential x) :=
  cechTransitionAt_pathAdditive D.potential x

/-- THEOREM 6: every basepoint Čech slice of the good-cover transition carries
no pointwise H¹ obstruction. -/
theorem cech_not_h1Obstruction
    [Inhabited Index]
    (D : ConvexClosedOneFormGoodCoverData Index E F) (x : E) :
    Not (CechAdditiveCover.H1Obstruction
      (identityPairZeroTripleCover Index F)
      (cechTransitionAt D.potential x)) :=
  cechTransitionAt_not_h1Obstruction D.potential x

/-- A bundled certificate produced from a convex good cover of closed `1`-forms. -/
structure GoodCoverCechDeRhamBridgeCertificate
    [Inhabited Index]
    (D : ConvexClosedOneFormGoodCoverData Index E F) : Prop where
  transition_continuous :
    ContinuousOnAdditiveTransitions D.cover
      (topologicalAdditiveExactTransition D.potential)
  local_derivative :
    ∀ i x, x ∈ D.cover.U i ->
      HasFDerivAt (D.potential i) ((D.chart i).omega x) x
  local_continuous :
    ∀ i, ContinuousOn (D.potential i) (D.cover.U i)
  pointwise_cech_oneCoboundary :
    ∀ x,
      CechAdditiveCover.OneCoboundary
        (identityPairZeroTripleCover Index F)
        (cechTransitionAt D.potential x)
  pointwise_cech_pathAdditive :
    ∀ x, PathAdditive (cechTransitionAt D.potential x)
  pointwise_cech_not_h1Obstruction :
    ∀ x,
      Not (CechAdditiveCover.H1Obstruction
        (identityPairZeroTripleCover Index F)
        (cechTransitionAt D.potential x))

/-- THEOREM 7: a convex good cover of closed `1`-forms produces the full
exact additive Čech bridge certificate available in this framework. -/
theorem goodCover_cechDeRham_bridge
    [Inhabited Index]
    (D : ConvexClosedOneFormGoodCoverData Index E F) :
    GoodCoverCechDeRhamBridgeCertificate D where
  transition_continuous := D.additiveTransition_continuousOn
  local_derivative := D.potential_hasFDerivAt
  local_continuous := D.potential_continuousOn
  pointwise_cech_oneCoboundary := D.cech_oneCoboundary
  pointwise_cech_pathAdditive := D.cech_pathAdditive
  pointwise_cech_not_h1Obstruction := D.cech_not_h1Obstruction

end ConvexClosedOneFormGoodCoverData

/-!
Summary:

* P284's local Poincare primitive is now lifted from one convex chart to every
  chart in an open convex good cover.
* The chartwise primitives induce continuous additive transitions on overlaps.
* Every basepoint Čech slice remains exact/path-additive/no-H¹.

Remaining boundary:

* This still assumes a good cover by convex chart domains with closed `1`-form
  data.
* It does not prove the general Čech-de Rham theorem, manifold de Rham
  cohomology, Poincare duality, or a smooth gauge-bundle producer.
-/


end

end GeometryConnection
end AffineRelaxation
end SaturationMonoid
