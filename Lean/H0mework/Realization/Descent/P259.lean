import H0mework.Realization.Descent.P258

/-!
# Proposition 259: discrete principal cocycles and group-valued holonomy

P258 proves the additive affine chart-family transport bridge.  This file adds
the corresponding group-valued, still-discrete, principal-cocycle skeleton.

For a transition cochain `g : Index -> Index -> G`, flatness means that the
two-hop transition from `i` to `k` through `j` agrees with the direct
transition:

`g j k * g i j = g i k`.

The triangular holonomy residual is therefore

`g j k * g i j * (g i k)⁻¹`.

Exact transitions induced by a potential `p : Index -> G`,

`g i j = p j * (p i)⁻¹`,

are flat and have trivial holonomy.  If `G` acts on a fiber `X`, flatness gives
path-independent transport by the group action.

Boundary: this is a discrete group-valued cocycle / holonomy certificate.  It
is not a smooth principal bundle, not a Lie group gauge field on a manifold,
not a curvature tensor, and not a Standard Model gauge construction.
-/

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Group-valued transition cochains -/

/-- A discrete principal connection is flat when its group-valued transitions
compose path-independently.  The order matches left actions on fibers:
first transport `i -> j`, then `j -> k`, so the group product is
`g j k * g i j`. -/
def FlatPrincipalConnection {Index G : Type*} [Group G]
    (g : Index -> Index -> G) : Prop :=
  ∀ i j k, g j k * g i j = g i k

/-- The group-valued triangular holonomy residual.  It is `1` exactly when
the two-hop path and the direct path agree. -/
def principalTriangleHolonomy {Index G : Type*} [Group G]
    (g : Index -> Index -> G) (i j k : Index) : G :=
  g j k * g i j * (g i k)⁻¹

/-- Flatness is exactly vanishing group-valued triangular holonomy. -/
theorem flatPrincipalConnection_iff_principalTriangleHolonomy_one
    {Index G : Type*} [Group G]
    (g : Index -> Index -> G) :
    FlatPrincipalConnection g <->
      ∀ i j k, principalTriangleHolonomy g i j k = 1 := by
  constructor
  · intro hflat i j k
    simp [principalTriangleHolonomy, hflat i j k]
  · intro hzero i j k
    have h := congrArg (fun x => x * g i k) (hzero i j k)
    simpa [principalTriangleHolonomy, mul_assoc] using h

/-- A concrete obstruction predicate: some triangular holonomy is nontrivial. -/
def PrincipalHolonomyObstruction {Index G : Type*} [Group G]
    (g : Index -> Index -> G) : Prop :=
  ∃ i j k, principalTriangleHolonomy g i j k ≠ 1

/-- Non-flatness is exactly nontrivial triangular holonomy. -/
theorem principalHolonomyObstruction_iff_not_flat
    {Index G : Type*} [Group G]
    (g : Index -> Index -> G) :
    PrincipalHolonomyObstruction g <-> Not (FlatPrincipalConnection g) := by
  constructor
  · rintro ⟨i, j, k, hhol⟩ hflat
    exact hhol
      ((flatPrincipalConnection_iff_principalTriangleHolonomy_one g).mp hflat i j k)
  · intro hnot
    by_contra hnone
    apply hnot
    exact
      (flatPrincipalConnection_iff_principalTriangleHolonomy_one g).mpr
        (by
          intro i j k
          by_contra hhol
          exact hnone ⟨i, j, k, hhol⟩)

/-! ## Exact principal transitions -/

/-- The exact transition cochain induced by a group-valued chart potential. -/
def principalExactTransition {Index G : Type*} [Group G]
    (potential : Index -> G) (i j : Index) : G :=
  potential j * (potential i)⁻¹

/-- A group-valued cochain is exact when it is induced by a global potential. -/
def PrincipalOneCoboundary {Index G : Type*} [Group G]
    (g : Index -> Index -> G) : Prop :=
  ∃ potential : Index -> G, g = principalExactTransition potential

/-- Exact principal transitions are flat. -/
theorem principalExactTransition_flat
    {Index G : Type*} [Group G]
    (potential : Index -> G) :
    FlatPrincipalConnection (principalExactTransition potential) := by
  intro i j k
  simp [principalExactTransition, mul_assoc]

/-- Exact principal transitions have trivial triangular holonomy. -/
theorem principalExactTransition_holonomy_one
    {Index G : Type*} [Group G]
    (potential : Index -> G) :
    ∀ i j k,
      principalTriangleHolonomy (principalExactTransition potential) i j k = 1 :=
  (flatPrincipalConnection_iff_principalTriangleHolonomy_one
    (principalExactTransition potential)).mp
      (principalExactTransition_flat potential)

/-- Exact principal transitions are one-coboundaries by construction. -/
theorem principalExactTransition_oneCoboundary
    {Index G : Type*} [Group G]
    (potential : Index -> G) :
    PrincipalOneCoboundary (principalExactTransition potential) :=
  ⟨potential, rfl⟩

/-- Any exact principal cochain is flat. -/
theorem principalOneCoboundary_flat
    {Index G : Type*} [Group G]
    (g : Index -> Index -> G)
    (hexact : PrincipalOneCoboundary g) :
    FlatPrincipalConnection g := by
  rcases hexact with ⟨potential, rfl⟩
  exact principalExactTransition_flat potential

/-- Exact principal cochains cannot carry nontrivial triangular holonomy. -/
theorem principalOneCoboundary_not_obstruction
    {Index G : Type*} [Group G]
    (g : Index -> Index -> G)
    (hexact : PrincipalOneCoboundary g) :
    Not (PrincipalHolonomyObstruction g) := by
  intro hobs
  exact (principalHolonomyObstruction_iff_not_flat g).mp hobs
    (principalOneCoboundary_flat g hexact)

/-- Exact principal self-transition is the identity. -/
theorem principalExactTransition_self
    {Index G : Type*} [Group G]
    (potential : Index -> G) (i : Index) :
    principalExactTransition potential i i = 1 := by
  simp [principalExactTransition]

/-- Exact principal transitions invert by reversing the edge. -/
theorem principalExactTransition_left_inverse
    {Index G : Type*} [Group G]
    (potential : Index -> G) (i j : Index) :
    principalExactTransition potential j i *
      principalExactTransition potential i j = 1 := by
  simp [principalExactTransition, mul_assoc]

/-- The symmetric inverse law for exact principal transitions. -/
theorem principalExactTransition_right_inverse
    {Index G : Type*} [Group G]
    (potential : Index -> G) (i j : Index) :
    principalExactTransition potential i j *
      principalExactTransition potential j i = 1 := by
  simp [principalExactTransition, mul_assoc]

/-! ## Transport on a fiber by a group action -/

/-- Transport a fiber point by a group-valued transition cochain. -/
def principalTransport {Index G X : Type*} [Group G] [MulAction G X]
    (g : Index -> Index -> G) (i j : Index) (x : X) : X :=
  g i j • x

/-- The mismatch between two-hop transport and direct transport is exactly
the triangular holonomy action. -/
theorem principalTransport_comp_eq_holonomy
    {Index G X : Type*} [Group G] [MulAction G X]
    (g : Index -> Index -> G) (i j k : Index) (x : X) :
    principalTransport g j k (principalTransport g i j x) =
      principalTriangleHolonomy g i j k •
        principalTransport g i k x := by
  simp [principalTransport, principalTriangleHolonomy, mul_smul, mul_assoc]

/-- Flat principal connections give path-independent fiber transport. -/
theorem flat_principalTransport_comp
    {Index G X : Type*} [Group G] [MulAction G X]
    (g : Index -> Index -> G)
    (hflat : FlatPrincipalConnection g)
    (i j k : Index) (x : X) :
    principalTransport g j k (principalTransport g i j x) =
      principalTransport g i k x := by
  unfold principalTransport
  rw [← mul_smul, hflat i j k]

/-- Exact principal transport composes path-independently. -/
theorem principalExactTransport_comp
    {Index G X : Type*} [Group G] [MulAction G X]
    (potential : Index -> G) (i j k : Index) (x : X) :
    principalTransport (principalExactTransition potential) j k
        (principalTransport (principalExactTransition potential) i j x) =
      principalTransport (principalExactTransition potential) i k x :=
  flat_principalTransport_comp
    (principalExactTransition potential)
    (principalExactTransition_flat potential) i j k x

/-- Exact principal self-transport is the identity action. -/
theorem principalExactTransport_self
    {Index G X : Type*} [Group G] [MulAction G X]
    (potential : Index -> G) (i : Index) (x : X) :
    principalTransport (principalExactTransition potential) i i x = x := by
  simp [principalTransport, principalExactTransition]

/-! ## Bundled certificate -/

/-- A bundled certificate for discrete principal cocycle transport. -/
structure DiscretePrincipalCocycleTransportCertificate
    (Index G X : Type*) [Group G] [MulAction G X]
    (potential : Index -> G) : Prop where
  flat :
    FlatPrincipalConnection (principalExactTransition potential)
  one_coboundary :
    PrincipalOneCoboundary (principalExactTransition potential)
  trivial_holonomy :
    ∀ i j k,
      principalTriangleHolonomy
        (principalExactTransition potential) i j k = 1
  self_transition :
    ∀ i, principalExactTransition potential i i = 1
  inverse_left :
    ∀ i j,
      principalExactTransition potential j i *
        principalExactTransition potential i j = 1
  inverse_right :
    ∀ i j,
      principalExactTransition potential i j *
        principalExactTransition potential j i = 1
  transport_comp :
    ∀ i j k (x : X),
      principalTransport (principalExactTransition potential) j k
          (principalTransport (principalExactTransition potential) i j x) =
        principalTransport (principalExactTransition potential) i k x
  transport_self :
    ∀ i (x : X),
      principalTransport (principalExactTransition potential) i i x = x

/-- Any group-valued chart potential supplies a discrete principal cocycle
transport certificate. -/
theorem discretePrincipalCocycleTransportCertificate
    {Index G X : Type*} [Group G] [MulAction G X]
    (potential : Index -> G) :
    DiscretePrincipalCocycleTransportCertificate Index G X potential where
  flat := principalExactTransition_flat potential
  one_coboundary := principalExactTransition_oneCoboundary potential
  trivial_holonomy := principalExactTransition_holonomy_one potential
  self_transition := principalExactTransition_self potential
  inverse_left := principalExactTransition_left_inverse potential
  inverse_right := principalExactTransition_right_inverse potential
  transport_comp := principalExactTransport_comp potential
  transport_self := principalExactTransport_self potential


end AffineRelaxation
end SaturationMonoid
