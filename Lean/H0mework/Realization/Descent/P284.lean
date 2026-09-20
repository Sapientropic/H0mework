import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import H0mework.Realization.Descent.P272

/-!
# Proposition 284: local Poincare lemma bridge for the geometry track

P272 names the Čech/de Rham comparison target and proves the exact-potential
Čech slice.  P280-P282 prove the finite Poincare-pairing arithmetic used by
the generation-slot roadmap.  This file closes the next analytic seam that
Mathlib already supports:

* a closed `1`-form on an open convex domain has a primitive
  (Mathlib's Poincare lemma for `1`-forms);
* that primitive supplies the exact local potential needed by P272;
* therefore the local Čech slice induced by that primitive is a coboundary,
  path-additive, and carries no pointwise H¹ obstruction.

Boundary: this is a local convex-chart bridge.  It is not the full global
Čech-de Rham theorem, not manifold de Rham cohomology, and not Poincare
duality.  It proves that the exact-potential certificate can be produced from
a real analytic closed-form hypothesis on one convex chart.
-/

namespace SaturationMonoid
namespace AffineRelaxation
namespace GeometryConnection

noncomputable section

/-! ## Closed one-forms on an open convex chart -/

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [CompleteSpace F]

/-- Analytic data for a closed `1`-form on an open convex domain.

Mathlib's current Poincare lemma represents a `1`-form as
`omega : E -> E ->L[ℝ] F`; closedness is symmetry of its Frechet derivative.
-/
structure ConvexClosedOneFormData (E F : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  domain : Set E
  convex_domain : Convex ℝ domain
  open_domain : IsOpen domain
  omega : E -> E →L[ℝ] F
  differentiableOn_omega : DifferentiableOn ℝ omega domain
  closed_omega :
    ∀ a ∈ domain, ∀ x y,
      fderiv ℝ omega a x y = fderiv ℝ omega a y x

namespace ConvexClosedOneFormData

/-- A primitive produced by the Poincare lemma for a closed `1`-form. -/
structure PrimitiveCertificate
    (D : ConvexClosedOneFormData E F) where
  potential : E -> F
  derivative_eq_one_form :
    ∀ x ∈ D.domain, HasFDerivAt potential (D.omega x) x

/-- THEOREM 1: Mathlib's Poincare lemma produces a primitive for every closed
`1`-form on an open convex chart. -/
theorem exists_primitive_certificate
    (D : ConvexClosedOneFormData E F) :
    Nonempty (PrimitiveCertificate D) := by
  rcases D.convex_domain.exists_forall_hasFDerivAt_of_fderiv_symmetric
      D.open_domain D.differentiableOn_omega D.closed_omega with
    ⟨potential, hpotential⟩
  exact ⟨⟨potential, hpotential⟩⟩

namespace PrimitiveCertificate

omit [CompleteSpace F] in
/-- THEOREM 2: a primitive supplied by the local Poincare bridge is continuous
on the chart domain. -/
theorem continuousOn
    {D : ConvexClosedOneFormData E F}
    (P : PrimitiveCertificate D) :
    ContinuousOn P.potential D.domain := by
  intro x hx
  exact (P.derivative_eq_one_form x hx).continuousAt.continuousWithinAt

/-- Use the same local primitive as the potential on every index of a local
Čech slice.  This is the one-chart exact comparison case: all transition
functions are zero, hence exact. -/
def constantIndexPotential
    {D : ConvexClosedOneFormData E F}
    (P : PrimitiveCertificate D) (Index : Type*) :
    Index -> E -> F :=
  fun _ => P.potential

omit [CompleteSpace F] in
/-- THEOREM 3: the constant-index local Čech transition is pointwise zero. -/
theorem constantIndexTransition_eq_zero
    {D : ConvexClosedOneFormData E F}
    (P : PrimitiveCertificate D) (Index : Type*)
    (x : E) (i j : Index) :
    cechTransitionAt (P.constantIndexPotential Index) x i j = 0 := by
  simp [cechTransitionAt, topologicalAdditiveExactTransition,
    constantIndexPotential]

omit [CompleteSpace F] in
/-- THEOREM 4: the local Čech slice induced by the Poincare primitive is a
1-coboundary. -/
theorem constantIndexTransition_oneCoboundary
    {D : ConvexClosedOneFormData E F}
    (P : PrimitiveCertificate D) (Index : Type*) (x : E) :
    CechAdditiveCover.OneCoboundary
      (identityPairZeroTripleCover Index F)
      (cechTransitionAt (P.constantIndexPotential Index) x) :=
  cechTransitionAt_oneCoboundary (P.constantIndexPotential Index) x

omit [CompleteSpace F] in
/-- THEOREM 5: the local Čech slice induced by the Poincare primitive is
path-additive / flat. -/
theorem constantIndexTransition_pathAdditive
    {D : ConvexClosedOneFormData E F}
    (P : PrimitiveCertificate D) (Index : Type*) (x : E) :
    PathAdditive (cechTransitionAt (P.constantIndexPotential Index) x) :=
  cechTransitionAt_pathAdditive (P.constantIndexPotential Index) x

omit [CompleteSpace F] in
/-- THEOREM 6: hence the local exact slice carries no pointwise H¹
obstruction. -/
theorem constantIndexTransition_not_h1Obstruction
    {D : ConvexClosedOneFormData E F}
    (P : PrimitiveCertificate D) (Index : Type*) [Inhabited Index]
    (x : E) :
    Not (CechAdditiveCover.H1Obstruction
      (identityPairZeroTripleCover Index F)
      (cechTransitionAt (P.constantIndexPotential Index) x)) :=
  cechTransitionAt_not_h1Obstruction (P.constantIndexPotential Index) x

end PrimitiveCertificate

/-- THEOREM 7: local Čech/de Rham bridge.

From a closed `1`-form on an open convex chart, obtain a primitive whose local
Čech transition is exact, flat, and non-obstructed at every basepoint. -/
theorem closedOneForm_local_cechDeRham_bridge
    (D : ConvexClosedOneFormData E F)
    (Index : Type*) [Inhabited Index] :
    ∃ potential : E -> F,
      (∀ x ∈ D.domain, HasFDerivAt potential (D.omega x) x) ∧
      (∀ x,
        CechAdditiveCover.OneCoboundary
          (identityPairZeroTripleCover Index F)
          (cechTransitionAt (fun _ : Index => potential) x)) ∧
      (∀ x,
        PathAdditive (cechTransitionAt (fun _ : Index => potential) x)) ∧
      (∀ x,
        Not (CechAdditiveCover.H1Obstruction
          (identityPairZeroTripleCover Index F)
          (cechTransitionAt (fun _ : Index => potential) x))) := by
  rcases D.exists_primitive_certificate with ⟨P⟩
  refine ⟨P.potential, P.derivative_eq_one_form, ?_, ?_, ?_⟩
  · intro x
    exact cechTransitionAt_oneCoboundary (fun _ : Index => P.potential) x
  · intro x
    exact cechTransitionAt_pathAdditive (fun _ : Index => P.potential) x
  · intro x
    exact cechTransitionAt_not_h1Obstruction (fun _ : Index => P.potential) x

end ConvexClosedOneFormData

/-!
Summary:

* Mathlib's Poincare lemma now supplies the missing local primitive producer
  for the exact-potential Čech slice in P272.
* The produced primitive is continuous on the chart and its constant-index
  local transition is zero, a coboundary, path-additive, and non-obstructed.
* The global Čech-de Rham theorem, smooth manifold cohomology, and Poincare
  duality remain explicit geometry-producer obligations.
-/


end

end GeometryConnection
end AffineRelaxation
end SaturationMonoid
