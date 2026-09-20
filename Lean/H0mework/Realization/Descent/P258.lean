import H0mework.Realization.Relations.P116
import H0mework.Realization.Descent.P242

/-!
# Proposition 258: discrete affine bundle transport and H¹ obstruction

P241 proves that affine translation transports the target-general relaxation
law between two target charts.  This file adds the next, still-discrete bridge:
when a family of chart targets is present, the induced transition cochain

`δ i j = target j - target i`

is not an arbitrary choice.  It is an exact 1-coboundary, hence flat and
path-independent.  More generally, an arbitrary affine connection cochain is
flat exactly when its triangular holonomy vanishes; in the P116 cover skeleton,
non-flatness is exactly the H¹ obstruction predicate.

Boundary: this is a discrete affine transport certificate.  It is not a smooth
principal bundle, not a Lie-group gauge theory, not a parallel connection on a
manifold, and not a Standard Model gauge-field construction.
-/

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Affine connection cochains -/

/-- A discrete affine connection is flat when its transition displacements are
path-additive: going `i -> j -> k` equals going `i -> k`. -/
abbrev FlatAffineConnection {Index E : Type*} [AddCommGroup E]
    (delta : Index -> Index -> E) : Prop :=
  PathAdditive delta

/-- The triangular holonomy residual of an affine transition cochain.  It is
zero exactly when the two-hop path and direct path agree. -/
def triangleHolonomy {Index E : Type*} [AddCommGroup E]
    (delta : Index -> Index -> E) (i j k : Index) : E :=
  delta i j + delta j k - delta i k

/-- Flatness is exactly vanishing triangular holonomy. -/
theorem flatAffineConnection_iff_triangleHolonomy_zero
    {Index E : Type*} [AddCommGroup E]
    (delta : Index -> Index -> E) :
    FlatAffineConnection delta <->
      ∀ i j k, triangleHolonomy delta i j k = 0 := by
  constructor
  · intro hflat i j k
    unfold triangleHolonomy
    rw [hflat i j k]
    simp
  · intro hzero i j k
    exact sub_eq_zero.mp (hzero i j k)

/-- Transport by a discrete affine connection cochain. -/
def connectionTransport {Index E : Type*} [AddCommGroup E]
    (delta : Index -> Index -> E) (i j : Index) (x : E) : E :=
  translateModule (delta i j) x

/-- The mismatch between two-hop transport and direct transport is exactly the
triangular holonomy residual. -/
theorem connectionTransport_comp_eq_holonomy
    {Index E : Type*} [AddCommGroup E]
    (delta : Index -> Index -> E) (i j k : Index) (x : E) :
    connectionTransport delta j k (connectionTransport delta i j x) =
      translateModule (triangleHolonomy delta i j k)
        (connectionTransport delta i k x) := by
  simp [connectionTransport, translateModule, triangleHolonomy]
  abel

/-- A flat affine connection has path-independent transport. -/
theorem flat_connectionTransport_comp
    {Index E : Type*} [AddCommGroup E]
    (delta : Index -> Index -> E)
    (hflat : FlatAffineConnection delta)
    (i j k : Index) (x : E) :
    connectionTransport delta j k (connectionTransport delta i j x) =
      connectionTransport delta i k x := by
  unfold connectionTransport
  rw [translateModule_comp, hflat i j k]

/-- In the P116 cover skeleton, H¹ obstruction for an affine connection is
exactly failure of flat/path-additive transport. -/
theorem affineConnection_h1Obstruction_iff_not_flat
    {Index E : Type*} [Inhabited Index] [AddCommGroup E]
    (delta : Index -> Index -> E) :
    CechAdditiveCover.H1Obstruction
        (identityPairZeroTripleCover Index E) delta <->
      Not (FlatAffineConnection delta) := by
  exact h1Obstruction_iff_not_pathAdditive delta

/-! ## Target-family induced transport is exact -/

/-- The transition displacement induced by a family of affine chart targets. -/
def targetTransition {Index E : Type*} [AddCommGroup E]
    (target : Index -> E) (i j : Index) : E :=
  target j - target i

/-- Target-family transitions are path-additive. -/
theorem targetTransition_flat
    {Index E : Type*} [AddCommGroup E]
    (target : Index -> E) :
    FlatAffineConnection (targetTransition target) := by
  intro i j k
  simp [targetTransition]

/-- Target-family transitions have zero triangular holonomy. -/
theorem targetTransition_triangleHolonomy_zero
    {Index E : Type*} [AddCommGroup E]
    (target : Index -> E) :
    ∀ i j k, triangleHolonomy (targetTransition target) i j k = 0 :=
  (flatAffineConnection_iff_triangleHolonomy_zero
    (targetTransition target)).mp (targetTransition_flat target)

/-- Target-family transitions are exact 1-coboundaries. -/
theorem targetTransition_oneCoboundary
    {Index E : Type*} [AddCommGroup E]
    (target : Index -> E) :
    CechAdditiveCover.OneCoboundary
      (identityPairZeroTripleCover Index E)
      (targetTransition target) := by
  refine ⟨target, ?_⟩
  funext i j
  simp [CechAdditiveCover.d0, targetTransition, identityPairZeroTripleCover]

/-- Therefore target-family transitions cannot carry a nontrivial H¹ class in
the identity-pair / zero-triple cover skeleton. -/
theorem targetTransition_not_h1Obstruction
    {Index E : Type*} [Inhabited Index] [AddCommGroup E]
    (target : Index -> E) :
    Not (CechAdditiveCover.H1Obstruction
      (identityPairZeroTripleCover Index E)
      (targetTransition target)) := by
  intro h
  exact h.2 (targetTransition_oneCoboundary target)

/-- Chart transport induced by a target family. -/
def chartTransport {Index E : Type*} [AddCommGroup E]
    (target : Index -> E) (i j : Index) (x : E) : E :=
  connectionTransport (targetTransition target) i j x

/-- Target-family chart transport composes strictly. -/
theorem chartTransport_comp
    {Index E : Type*} [AddCommGroup E]
    (target : Index -> E) (i j k : Index) (x : E) :
    chartTransport target j k (chartTransport target i j x) =
      chartTransport target i k x :=
  flat_connectionTransport_comp
    (targetTransition target) (targetTransition_flat target) i j k x

/-- Target-family chart transport has identity self-transport. -/
theorem chartTransport_self
    {Index E : Type*} [AddCommGroup E]
    (target : Index -> E) (i : Index) (x : E) :
    chartTransport target i i x = x := by
  simp [chartTransport, connectionTransport, targetTransition]

/-- Target-family chart transport is invertible by reversing the edge. -/
theorem chartTransport_left_inverse
    {Index E : Type*} [AddCommGroup E]
    (target : Index -> E) (i j : Index) (x : E) :
    chartTransport target j i (chartTransport target i j x) = x := by
  rw [chartTransport_comp]
  exact chartTransport_self target i x

/-- The symmetric inverse law for chart transport. -/
theorem chartTransport_right_inverse
    {Index E : Type*} [AddCommGroup E]
    (target : Index -> E) (i j : Index) (x : E) :
    chartTransport target i j (chartTransport target j i x) = x := by
  rw [chartTransport_comp]
  exact chartTransport_self target j x

/-! ## Transporting affine relaxation across chart targets -/

/-- Target-family chart transport conjugates relaxation in chart `i` to
relaxation in chart `j`. -/
theorem chartTransport_relaxModule_conjugate
    {Index K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : Index -> E) (i j : Index) (x : E) (sigma : K) :
    chartTransport target i j
        (relaxModule (target i) sigma
          (chartTransport target j i x)) =
      relaxModule (target j) sigma x := by
  exact relaxModule_transport_conjugate (target i) (target j) x sigma

/-- After chart transport into a common target chart, same-target noisy-OR
composition is restored. -/
theorem chartTransport_relaxModule_compose
    {Index K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : Index -> E) (i j : Index) (x : E) (sigma1 sigma2 : K) :
    chartTransport target i j
        (relaxModule (target i) sigma2
          (relaxModule (target i) sigma1
            (chartTransport target j i x))) =
      relaxModule (target j) (satOrField sigma1 sigma2) x := by
  exact relaxModule_transport_compose (target i) (target j) x sigma1 sigma2

/-- A bundled certificate for the discrete affine bundle transport supplied by
a family of chart targets. -/
structure DiscreteAffineBundleTransportCertificate
    (Index K E : Type*) [Field K] [AddCommGroup E] [Module K E]
    (target : Index -> E) : Prop where
  flat :
    FlatAffineConnection (targetTransition target)
  zero_holonomy :
    ∀ i j k, triangleHolonomy (targetTransition target) i j k = 0
  exact_coboundary :
    CechAdditiveCover.OneCoboundary
      (identityPairZeroTripleCover Index E)
      (targetTransition target)
  transport_comp :
    ∀ i j k x,
      chartTransport target j k (chartTransport target i j x) =
        chartTransport target i k x
  transport_conjugates_relaxation :
    ∀ i j x, ∀ sigma : K,
      chartTransport target i j
          (relaxModule (target i) sigma
            (chartTransport target j i x)) =
        relaxModule (target j) sigma x
  noisy_or_after_chart_transport :
    ∀ i j x, ∀ sigma1 sigma2 : K,
      chartTransport target i j
          (relaxModule (target i) sigma2
            (relaxModule (target i) sigma1
              (chartTransport target j i x))) =
        relaxModule (target j) (satOrField sigma1 sigma2) x

/-- Any affine chart target family supplies the discrete bundle transport
certificate. -/
theorem discreteAffineBundleTransportCertificate
    {Index K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : Index -> E) :
    DiscreteAffineBundleTransportCertificate Index K E target where
  flat := targetTransition_flat target
  zero_holonomy := targetTransition_triangleHolonomy_zero target
  exact_coboundary := targetTransition_oneCoboundary target
  transport_comp := chartTransport_comp target
  transport_conjugates_relaxation := chartTransport_relaxModule_conjugate target
  noisy_or_after_chart_transport := chartTransport_relaxModule_compose target


end AffineRelaxation
end SaturationMonoid
