import H0mework.Physics.SourceContracts.P434

/-!
# Proposition 435: formal exact-geometry collapse audit

P431/P432 strengthen the geometry side from a bare Poincare slot certificate to
a good-cover Čech/de Rham producer plus 4D Poincare duality.  This file audits
that strengthened interface.

There is still a canonical formal inhabitant:

* the one-chart/universal open cover;
* the zero closed `1`-form on every chart;
* the P422 degree-orbit Poincare normal form.

Therefore the current good-cover interface is enough to prove exactness/no-H¹
for a formal trivial geometry, but it is not yet a physical smooth spacetime /
gauge-bundle producer.  Under this explicitly named formal-exact geometry
audit, the remaining strict good-cover front door collapses to the matrix
sigma/RG table alone.
-/

namespace SaturationMonoid
namespace AffineRelaxation
namespace GeometryConnection

noncomputable section

/-! ## Trivial good-cover exact geometry -/

variable {CoverIndex E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable [Inhabited CoverIndex]

/-- The universal one-shape open cover: every chart is the full base. -/
def universalTopologicalPrincipalCover
    (CoverIndex E : Type*) [TopologicalSpace E] [Inhabited CoverIndex] :
    TopologicalPrincipalCover E CoverIndex where
  U := fun _ => Set.univ
  isOpen_U := by
    intro _
    exact isOpen_univ
  covers := by
    intro x
    exact ⟨default, by simp⟩

/-- The zero closed `1`-form on the full convex domain. -/
def zeroConvexClosedOneFormData
    (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ConvexClosedOneFormData E F where
  domain := Set.univ
  convex_domain := by
    exact convex_univ
  open_domain := isOpen_univ
  omega := fun _ => 0
  differentiableOn_omega := by
    exact (differentiable_const (c := (0 : E →L[ℝ] F))).differentiableOn
  closed_omega := by
    intro a ha x y
    simp

/-- A formal exact good cover: universal charts carrying the zero closed
`1`-form. -/
def formalZeroGoodCoverData
    (CoverIndex E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Inhabited CoverIndex] :
    ConvexClosedOneFormGoodCoverData CoverIndex E F where
  cover := universalTopologicalPrincipalCover CoverIndex E
  chart := fun _ => zeroConvexClosedOneFormData E F
  chart_domain_eq_cover := by
    intro i
    rfl

/-- THEOREM 1: the formal zero good cover supplies P285's exact Čech/de Rham
bridge. -/
theorem formalZeroGoodCover_cechDeRhamBridge :
    ConvexClosedOneFormGoodCoverData.GoodCoverCechDeRhamBridgeCertificate
      (formalZeroGoodCoverData CoverIndex E F) :=
  ConvexClosedOneFormGoodCoverData.goodCover_cechDeRham_bridge
    (formalZeroGoodCoverData CoverIndex E F)

/-- The current formal exact good-cover plus Poincare geometry: zero closed
`1`-forms together with P422's degree-orbit Poincare normal form. -/
def formalExactGoodCoverPoincarePhysicalGeometry :
    GoodCoverPoincarePhysicalGeometry CoverIndex E F where
  goodCover := formalZeroGoodCoverData CoverIndex E F
  poincare :=
    FourDimensionalPoincareOrbitCohomologyNormalForm.unitOrbitNormalForm.toPoincareDualityCohomologyCertificate

/-- THEOREM 2: the current good-cover/Poincare geometry interface is formally
inhabited.  This is an interface-strength audit, not a physical spacetime
construction. -/
theorem formalExactGoodCoverPoincarePhysicalGeometry_nonempty :
    Nonempty (GoodCoverPoincarePhysicalGeometry CoverIndex E F) :=
  ⟨formalExactGoodCoverPoincarePhysicalGeometry⟩

end

end GeometryConnection
end AffineRelaxation

namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

/-! ## Collapse under the current formal exact geometry interface -/

/-- THEOREM 3: under the current formal exact good-cover geometry interface,
the P431/P432 strict good-cover producer is equivalent to the matrix sigma/RG
table alone. -/
theorem goodCoverPoincareStrictMatrixUnifiedProducer_iff_matrixTable_under_currentFormalExactGeometry
    {Index A CKMCarrier CoverIndex E F : Type*} [AddCommGroup A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    ExistsGoodCoverPoincareStrictMatrixUnifiedProducer
        Index A CKMCarrier CoverIndex E F ↔
      ExistsMatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
        Index A CKMCarrier := by
  constructor
  · exact And.left
  · intro hmatrix
    exact
      ⟨hmatrix,
        formalExactGoodCoverPoincarePhysicalGeometry_nonempty
          (CoverIndex := CoverIndex) (E := E) (F := F)⟩

/-- THEOREM 4: with the current formal exact geometry inhabitant, the strict
good-cover holy-grail output exists exactly when the matrix sigma/RG table
exists.  The theorem name keeps the `currentFormalExactGeometry` qualifier to
avoid mistaking this for a physical geometry theorem. -/
theorem goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_matrixTable_under_currentFormalExactGeometry
    {Index A CKMCarrier CoverIndex E F : Type*} [AddCommGroup A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    Nonempty
        (StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier
          (GoodCoverPoincarePhysicalGeometry CoverIndex E F)
          GoodCoverPoincarePhysicalGeometry.adapter) ↔
      ExistsMatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
        Index A CKMCarrier := by
  exact
    goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_producer.trans
      goodCoverPoincareStrictMatrixUnifiedProducer_iff_matrixTable_under_currentFormalExactGeometry

end StandardModelConstraint
end SaturationMonoid
