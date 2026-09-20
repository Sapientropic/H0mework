import Mathlib.Topology.Algebra.Group.Basic
import H0mework.Realization.Descent.P259

/-!
# Proposition 260: topological principal transition cocycles

P259 proves the discrete group-valued principal cocycle skeleton.  This file
adds the next bridge toward genuine gauge/bundle language: transition functions
over an open cover of a topological base.

The object here is still not a constructed smooth principal bundle.  It is the
standard transition-function input data one would feed into such a construction:

* an open cover `Uᵢ` of a base `B`;
* group-valued transition maps `gᵢⱼ : B -> G`;
* continuity of `gᵢⱼ` on overlaps `Uᵢ ∩ Uⱼ`;
* flat/cocycle law on triple overlaps;
* triangular holonomy obstruction exactly when the cocycle law fails.

Exact transitions induced by continuous local potentials are continuous on
overlaps, flat on triple overlaps, and have trivial holonomy.

Boundary: this is a topological transition-cocycle certificate over an open
cover.  It is not a glued total space, not a smooth principal bundle, not a Lie
group gauge field, not a connection 1-form, and not a curvature tensor.
-/

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Open covers and topological transition data -/

/-- A small open-cover wrapper for topological transition cocycles.  The cover
condition is included because later bundle/gluing constructions need it; the
local cocycle lemmas below mainly use the overlap/triple-overlap predicates. -/
structure TopologicalPrincipalCover (B Index : Type*)
    [TopologicalSpace B] : Type _ where
  U : Index -> Set B
  isOpen_U : ∀ i, IsOpen (U i)
  covers : ∀ x : B, ∃ i, x ∈ U i

namespace TopologicalPrincipalCover

variable {B Index : Type*} [TopologicalSpace B]

/-- Pairwise chart overlap. -/
def overlap (C : TopologicalPrincipalCover B Index) (i j : Index) : Set B :=
  C.U i ∩ C.U j

/-- Triple chart overlap. -/
def tripleOverlap (C : TopologicalPrincipalCover B Index)
    (i j k : Index) : Set B :=
  C.U i ∩ (C.U j ∩ C.U k)

theorem isOpen_overlap (C : TopologicalPrincipalCover B Index) (i j : Index) :
    IsOpen (C.overlap i j) :=
  (C.isOpen_U i).inter (C.isOpen_U j)

theorem isOpen_tripleOverlap (C : TopologicalPrincipalCover B Index)
    (i j k : Index) :
    IsOpen (C.tripleOverlap i j k) :=
  (C.isOpen_U i).inter ((C.isOpen_U j).inter (C.isOpen_U k))

theorem triple_subset_left_overlap
    (C : TopologicalPrincipalCover B Index) (i j k : Index) :
    C.tripleOverlap i j k ⊆ C.overlap i j := by
  intro x hx
  exact ⟨hx.1, hx.2.1⟩

theorem triple_subset_right_overlap
    (C : TopologicalPrincipalCover B Index) (i j k : Index) :
    C.tripleOverlap i j k ⊆ C.overlap j k := by
  intro x hx
  exact ⟨hx.2.1, hx.2.2⟩

theorem triple_subset_direct_overlap
    (C : TopologicalPrincipalCover B Index) (i j k : Index) :
    C.tripleOverlap i j k ⊆ C.overlap i k := by
  intro x hx
  exact ⟨hx.1, hx.2.2⟩

end TopologicalPrincipalCover

/-! ## Topological principal cocycles -/

/-- A group-valued transition family is continuous on chart overlaps. -/
def ContinuousOnPrincipalTransitions
    {B Index G : Type*} [TopologicalSpace B] [TopologicalSpace G]
    (C : TopologicalPrincipalCover B Index)
    (g : Index -> Index -> B -> G) : Prop :=
  ∀ i j, ContinuousOn (g i j) (C.overlap i j)

/-- Flatness/cocycle law on triple overlaps. -/
def TopologicalPrincipalFlatOn
    {B Index G : Type*} [TopologicalSpace B] [Group G]
    (C : TopologicalPrincipalCover B Index)
    (g : Index -> Index -> B -> G) : Prop :=
  ∀ i j k x, x ∈ C.tripleOverlap i j k ->
    g j k x * g i j x = g i k x

/-- Pointwise triangular holonomy of topological transition functions. -/
def topologicalPrincipalTriangleHolonomy
    {B Index G : Type*} [Group G]
    (g : Index -> Index -> B -> G) (i j k : Index) (x : B) : G :=
  g j k x * g i j x * (g i k x)⁻¹

/-- Some triple-overlap point carries nontrivial holonomy. -/
def TopologicalPrincipalHolonomyObstruction
    {B Index G : Type*} [TopologicalSpace B] [Group G]
    (C : TopologicalPrincipalCover B Index)
    (g : Index -> Index -> B -> G) : Prop :=
  ∃ i j k x, x ∈ C.tripleOverlap i j k ∧
    topologicalPrincipalTriangleHolonomy g i j k x ≠ 1

/-- Flatness on triple overlaps is exactly trivial triangular holonomy on
triple overlaps. -/
theorem topologicalPrincipalFlatOn_iff_holonomy_one
    {B Index G : Type*} [TopologicalSpace B] [Group G]
    (C : TopologicalPrincipalCover B Index)
    (g : Index -> Index -> B -> G) :
    TopologicalPrincipalFlatOn C g <->
      ∀ i j k x, x ∈ C.tripleOverlap i j k ->
        topologicalPrincipalTriangleHolonomy g i j k x = 1 := by
  constructor
  · intro hflat i j k x hx
    simp [topologicalPrincipalTriangleHolonomy, hflat i j k x hx]
  · intro hhol i j k x hx
    have h :=
      congrArg (fun y => y * g i k x) (hhol i j k x hx)
    simpa [topologicalPrincipalTriangleHolonomy, mul_assoc] using h

/-- Nontrivial topological triangular holonomy is exactly failure of flatness on
triple overlaps. -/
theorem topologicalPrincipalHolonomyObstruction_iff_not_flat
    {B Index G : Type*} [TopologicalSpace B] [Group G]
    (C : TopologicalPrincipalCover B Index)
    (g : Index -> Index -> B -> G) :
    TopologicalPrincipalHolonomyObstruction C g <->
      Not (TopologicalPrincipalFlatOn C g) := by
  constructor
  · rintro ⟨i, j, k, x, hx, hhol⟩ hflat
    exact hhol
      ((topologicalPrincipalFlatOn_iff_holonomy_one C g).mp
        hflat i j k x hx)
  · intro hnot
    by_contra hnone
    apply hnot
    exact
      (topologicalPrincipalFlatOn_iff_holonomy_one C g).mpr
        (by
          intro i j k x hx
          by_contra hhol
          exact hnone ⟨i, j, k, x, hx, hhol⟩)

/-! ## Exact continuous potentials -/

/-- The exact group-valued transition induced by local potentials. -/
def topologicalPrincipalExactTransition
    {B Index G : Type*} [Group G]
    (potential : Index -> B -> G) (i j : Index) (x : B) : G :=
  potential j x * (potential i x)⁻¹

/-- Exact transitions induced by continuous potentials are continuous on
overlaps. -/
theorem topologicalPrincipalExactTransition_continuousOn
    {B Index G : Type*} [TopologicalSpace B] [TopologicalSpace G]
    [Group G] [ContinuousMul G] [ContinuousInv G]
    (C : TopologicalPrincipalCover B Index)
    (potential : Index -> B -> G)
    (hpotential : ∀ i, Continuous (potential i)) :
    ContinuousOnPrincipalTransitions C
      (topologicalPrincipalExactTransition potential) := by
  intro i j
  exact ((hpotential j).mul ((hpotential i).inv)).continuousOn

/-- Exact transitions induced by local potentials are flat on triple overlaps. -/
theorem topologicalPrincipalExactTransition_flatOn
    {B Index G : Type*} [TopologicalSpace B] [Group G]
    (C : TopologicalPrincipalCover B Index)
    (potential : Index -> B -> G) :
    TopologicalPrincipalFlatOn C
      (topologicalPrincipalExactTransition potential) := by
  intro i j k x hx
  simp [topologicalPrincipalExactTransition, mul_assoc]

/-- Exact transitions induced by local potentials have trivial holonomy on
triple overlaps. -/
theorem topologicalPrincipalExactTransition_holonomy_one
    {B Index G : Type*} [TopologicalSpace B] [Group G]
    (C : TopologicalPrincipalCover B Index)
    (potential : Index -> B -> G) :
    ∀ i j k x, x ∈ C.tripleOverlap i j k ->
      topologicalPrincipalTriangleHolonomy
        (topologicalPrincipalExactTransition potential) i j k x = 1 :=
  (topologicalPrincipalFlatOn_iff_holonomy_one C
    (topologicalPrincipalExactTransition potential)).mp
      (topologicalPrincipalExactTransition_flatOn C potential)

/-- Exact continuous potentials cannot carry topological holonomy obstruction. -/
theorem topologicalPrincipalExactTransition_not_obstruction
    {B Index G : Type*} [TopologicalSpace B] [Group G]
    (C : TopologicalPrincipalCover B Index)
    (potential : Index -> B -> G) :
    Not (TopologicalPrincipalHolonomyObstruction C
      (topologicalPrincipalExactTransition potential)) := by
  intro hobs
  exact (topologicalPrincipalHolonomyObstruction_iff_not_flat C
    (topologicalPrincipalExactTransition potential)).mp hobs
      (topologicalPrincipalExactTransition_flatOn C potential)

/-! ## Fiber transport over a base point -/

/-- Fiber transport at base point `x` by a topological transition family. -/
def topologicalPrincipalTransport
    {B Index G X : Type*} [Group G] [MulAction G X]
    (g : Index -> Index -> B -> G) (i j : Index) (x : B) (v : X) : X :=
  g i j x • v

/-- At a base point in a triple overlap, two-hop transport differs from direct
transport exactly by the triangular holonomy action. -/
theorem topologicalPrincipalTransport_comp_eq_holonomy
    {B Index G X : Type*} [Group G] [MulAction G X]
    (g : Index -> Index -> B -> G) (i j k : Index) (x : B) (v : X) :
    topologicalPrincipalTransport g j k x
        (topologicalPrincipalTransport g i j x v) =
      topologicalPrincipalTriangleHolonomy g i j k x •
        topologicalPrincipalTransport g i k x v := by
  simp [topologicalPrincipalTransport, topologicalPrincipalTriangleHolonomy,
    mul_smul, mul_assoc]

/-- Flat topological transition cocycles give path-independent fiber transport
on triple overlaps. -/
theorem topologicalPrincipalFlat_transport_comp
    {B Index G X : Type*} [TopologicalSpace B] [Group G] [MulAction G X]
    (C : TopologicalPrincipalCover B Index)
    (g : Index -> Index -> B -> G)
    (hflat : TopologicalPrincipalFlatOn C g)
    (i j k : Index) (x : B) (hx : x ∈ C.tripleOverlap i j k) (v : X) :
    topologicalPrincipalTransport g j k x
        (topologicalPrincipalTransport g i j x v) =
      topologicalPrincipalTransport g i k x v := by
  unfold topologicalPrincipalTransport
  rw [← mul_smul, hflat i j k x hx]

/-- Exact topological principal transitions give path-independent fiber
transport on triple overlaps. -/
theorem topologicalPrincipalExactTransport_comp
    {B Index G X : Type*} [TopologicalSpace B] [Group G] [MulAction G X]
    (C : TopologicalPrincipalCover B Index)
    (potential : Index -> B -> G)
    (i j k : Index) (x : B) (hx : x ∈ C.tripleOverlap i j k) (v : X) :
    topologicalPrincipalTransport
        (topologicalPrincipalExactTransition potential) j k x
        (topologicalPrincipalTransport
          (topologicalPrincipalExactTransition potential) i j x v) =
      topologicalPrincipalTransport
        (topologicalPrincipalExactTransition potential) i k x v :=
  topologicalPrincipalFlat_transport_comp C
    (topologicalPrincipalExactTransition potential)
    (topologicalPrincipalExactTransition_flatOn C potential)
    i j k x hx v

/-! ## Bundled certificates -/

/-- A topological transition-cocycle certificate: continuous transition
functions on overlaps, flatness on triple overlaps, and trivial holonomy. -/
structure TopologicalPrincipalCocycleCertificate
    (B Index G : Type*) [TopologicalSpace B] [TopologicalSpace G]
    [Group G]
    (C : TopologicalPrincipalCover B Index)
    (g : Index -> Index -> B -> G) : Prop where
  transition_continuous :
    ContinuousOnPrincipalTransitions C g
  flat_on_triples :
    TopologicalPrincipalFlatOn C g
  trivial_holonomy :
    ∀ i j k x, x ∈ C.tripleOverlap i j k ->
      topologicalPrincipalTriangleHolonomy g i j k x = 1

/-- Continuous local potentials supply a topological principal cocycle
certificate. -/
theorem topologicalPrincipalExactCocycleCertificate
    {B Index G : Type*} [TopologicalSpace B] [TopologicalSpace G]
    [Group G] [ContinuousMul G] [ContinuousInv G]
    (C : TopologicalPrincipalCover B Index)
    (potential : Index -> B -> G)
    (hpotential : ∀ i, Continuous (potential i)) :
    TopologicalPrincipalCocycleCertificate B Index G C
      (topologicalPrincipalExactTransition potential) where
  transition_continuous :=
    topologicalPrincipalExactTransition_continuousOn C potential hpotential
  flat_on_triples :=
    topologicalPrincipalExactTransition_flatOn C potential
  trivial_holonomy :=
    topologicalPrincipalExactTransition_holonomy_one C potential

/-- A topological principal transport certificate also records path-independent
fiber transport for any group action on a model fiber. -/
structure TopologicalPrincipalTransportCertificate
    (B Index G X : Type*) [TopologicalSpace B] [TopologicalSpace G]
    [Group G] [MulAction G X]
    (C : TopologicalPrincipalCover B Index)
    (g : Index -> Index -> B -> G) : Prop where
  cocycle :
    TopologicalPrincipalCocycleCertificate B Index G C g
  transport_comp :
    ∀ i j k x, x ∈ C.tripleOverlap i j k -> ∀ v : X,
      topologicalPrincipalTransport g j k x
          (topologicalPrincipalTransport g i j x v) =
        topologicalPrincipalTransport g i k x v

/-- Continuous exact potentials supply a topological principal transport
certificate for every fiber action. -/
theorem topologicalPrincipalExactTransportCertificate
    {B Index G X : Type*} [TopologicalSpace B] [TopologicalSpace G]
    [Group G] [ContinuousMul G] [ContinuousInv G] [MulAction G X]
    (C : TopologicalPrincipalCover B Index)
    (potential : Index -> B -> G)
    (hpotential : ∀ i, Continuous (potential i)) :
    TopologicalPrincipalTransportCertificate B Index G X C
      (topologicalPrincipalExactTransition potential) where
  cocycle :=
    topologicalPrincipalExactCocycleCertificate C potential hpotential
  transport_comp :=
    topologicalPrincipalExactTransport_comp C potential


end AffineRelaxation
end SaturationMonoid
