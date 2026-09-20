import H0mework.Realization.Descent.P431

/-!
# Proposition 432: explicit field front door for the grand-unification receipt

P431 replaces the bare physical-geometry placeholder with a named good-cover
Čech/de Rham + 4D Poincare-duality producer.  One wrapper still remains at the
front door: the two producers are carried as existence statements.

This file opens that front door into one concrete field record:

* one primitive atom payload;
* one `3 × 3` Yukawa matrix sigma/RG table on that payload;
* one convex good-cover closed-`1`-form Čech/de Rham producer;
* one 4D Poincare-duality certificate.

The theorem is still producer-relative.  It does not manufacture the physical
RG table or the physical manifold/gauge geometry.  It proves that, for the
current Lean spine, those four fields are exactly the remaining grand-
unification input surface.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

/-! ## Explicit field-level producer -/

/-- The fully opened field-level producer for the current strict-matrix
good-cover grand-unification front door.

This is the P431 producer with both existence wrappers removed.  The matrix
table is dependent on the same primitive atom payload that carries the
zero-free/gauge/Yukawa data, and the geometry side is split into its two named
obligations. -/
structure MatrixGoodCoverPoincareUnifiedProducerFields
    (Index A CKMCarrier CoverIndex E F : Type*) [AddCommGroup A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] where
  atoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier
  matrixTable :
    MatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer atoms
  goodCover : ConvexClosedOneFormGoodCoverData CoverIndex E F
  poincare : PoincareDualityCohomologyCertificate.{0} 4

namespace MatrixGoodCoverPoincareUnifiedProducerFields

variable {Index A CKMCarrier CoverIndex E F : Type*} [AddCommGroup A]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable [Inhabited CoverIndex]

/-- THEOREM 1: the field record supplies the P431 good-cover physical geometry
producer. -/
def toGoodCoverPoincarePhysicalGeometry
    (P : MatrixGoodCoverPoincareUnifiedProducerFields
      Index A CKMCarrier CoverIndex E F) :
    GoodCoverPoincarePhysicalGeometry CoverIndex E F where
  goodCover := P.goodCover
  poincare := P.poincare

/-- THEOREM 2: the field record supplies P431's named strict-matrix producer
surface. -/
theorem toGoodCoverPoincareStrictMatrixUnifiedProducer
    (P : MatrixGoodCoverPoincareUnifiedProducerFields
      Index A CKMCarrier CoverIndex E F) :
    ExistsGoodCoverPoincareStrictMatrixUnifiedProducer
      Index A CKMCarrier CoverIndex E F :=
  ⟨⟨P.atoms, ⟨P.matrixTable⟩⟩,
    ⟨P.toGoodCoverPoincarePhysicalGeometry⟩⟩

/-- THEOREM 3: the field record exposes the same good-cover Čech/de Rham bridge
as its `goodCover` field. -/
theorem cechDeRhamBridge
    (P : MatrixGoodCoverPoincareUnifiedProducerFields
      Index A CKMCarrier CoverIndex E F) :
    ConvexClosedOneFormGoodCoverData.GoodCoverCechDeRhamBridgeCertificate
      P.goodCover :=
  ConvexClosedOneFormGoodCoverData.goodCover_cechDeRham_bridge P.goodCover

/-- THEOREM 4: the field record exposes the P280 current generation-slot
certificate from its Poincare-duality field. -/
def toCurrentCertificate
    (P : MatrixGoodCoverPoincareUnifiedProducerFields
      Index A CKMCarrier CoverIndex E F) :
    FourDimensionalPoincareGenerationSlotCertificate where
  geometry := P.poincare

end MatrixGoodCoverPoincareUnifiedProducerFields

/-! ## Exact normal form -/

/-- THEOREM 5: P431's named strict-matrix good-cover producer is nonempty
exactly when the four explicit field groups above are inhabited. -/
theorem goodCoverPoincareStrictMatrixUnifiedProducer_iff_fieldProducer
    {Index A CKMCarrier CoverIndex E F : Type*} [AddCommGroup A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    ExistsGoodCoverPoincareStrictMatrixUnifiedProducer
        Index A CKMCarrier CoverIndex E F ↔
      Nonempty
        (MatrixGoodCoverPoincareUnifiedProducerFields
          Index A CKMCarrier CoverIndex E F) := by
  constructor
  · rintro ⟨⟨atoms, ⟨matrixTable⟩⟩, ⟨geometry⟩⟩
    exact
      ⟨{ atoms := atoms
         matrixTable := matrixTable
         goodCover := geometry.goodCover
         poincare := geometry.poincare }⟩
  · rintro ⟨P⟩
    exact P.toGoodCoverPoincareStrictMatrixUnifiedProducer

/-- THEOREM 6: the strict-matrix unified holy-grail output, specialized to the
good-cover geometry producer, exists exactly when the explicit field-level
producer exists. -/
theorem goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_fieldProducer
    {Index A CKMCarrier CoverIndex E F : Type*} [AddCommGroup A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    Nonempty
        (StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier
          (GoodCoverPoincarePhysicalGeometry CoverIndex E F)
          GoodCoverPoincarePhysicalGeometry.adapter) ↔
      Nonempty
        (MatrixGoodCoverPoincareUnifiedProducerFields
          Index A CKMCarrier CoverIndex E F) := by
  exact
    goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_producer.trans
      goodCoverPoincareStrictMatrixUnifiedProducer_iff_fieldProducer

/-- THEOREM 7: compact holy-grail citation at the opened field level.  The four
explicit field groups construct the current holy-grail output and the unified
19-slot parameter-carrier certificate. -/
theorem matrixGoodCoverPoincareUnified_field_holy_grail_normal_form
    {Index A CKMCarrier CoverIndex E F : Type*} [AddCommGroup A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    MatrixGoodCoverPoincareUnifiedProducerFields
        Index A CKMCarrier CoverIndex E F ->
      ∃ O : StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier
          (GoodCoverPoincarePhysicalGeometry CoverIndex E F)
          GoodCoverPoincarePhysicalGeometry.adapter,
        Nonempty
          (MatrixGoodCoverPoincareUnifiedProducerFields
            Index A CKMCarrier CoverIndex E F) ∧
        SingleSourceHolyGrailReceiptStatement O.output.receipt ∧
        AffineRelaxation.UnifiedAffineRelaxationModuleCertificate
          ℝ (ParameterVector ℝ) ∧
        (∀ target x : ParameterVector ℝ, ∀ sigma : ℝ,
          parameterVectorComponentsEquiv ℝ
              (AffineRelaxation.relaxModule target sigma x) =
            AffineRelaxation.relaxModule
              (parameterVectorComponentsEquiv ℝ target)
              sigma
              (parameterVectorComponentsEquiv ℝ x)) := by
  intro P
  rcases
    goodCoverPoincareStrictMatrixUnified_holy_grail_normal_form
      P.toGoodCoverPoincareStrictMatrixUnifiedProducer with
    ⟨O, _hproducer, hreceipt, hparam, hconj⟩
  exact ⟨O, ⟨P⟩, hreceipt, hparam, hconj⟩

end StandardModelConstraint
end SaturationMonoid
