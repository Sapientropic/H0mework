import H0mework.Realization.Descent.P285
import H0mework.Physics.SourceForms.P430

/-!
# Proposition 431: good-cover Poincare geometry as the strict physical producer

P430 leaves the strict-matrix unified holy-grail output behind two producers:

* a matrix-indexed primitive sigma/RG table;
* an independent physical Poincare-geometry producer.

This file lowers the second producer from an arbitrary type to a concrete
geometry certificate shape already present in the framework:

* a convex-good-cover closed-`1`-form Čech/de Rham bridge from P285;
* a dimension-`4` Poincare-duality cohomology certificate from P280.

The result is still producer-relative.  It does not prove that the actual
Standard-Model spacetime/gauge bundle supplies such data.  But it removes the
bare `Nonempty PhysicalGeometry` placeholder from the grand-unification front
door and replaces it with a named, machine-checkable geometry obligation.
-/

namespace SaturationMonoid
namespace AffineRelaxation
namespace GeometryConnection

/-! ## Good-cover plus Poincare-duality physical geometry -/

/-- A concrete geometry-producer obligation for the strict Standard-Model
front door: a good-cover exact Čech/de Rham bridge together with 4D Poincare
duality. -/
structure GoodCoverPoincarePhysicalGeometry
    (CoverIndex E F : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] where
  goodCover : ConvexClosedOneFormGoodCoverData CoverIndex E F
  poincare : PoincareDualityCohomologyCertificate.{0} 4

namespace GoodCoverPoincarePhysicalGeometry

variable {CoverIndex E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable [Inhabited CoverIndex]

/-- THEOREM 1: the good-cover half supplies the exact additive Čech/de Rham
bridge proved in P285. -/
theorem cechDeRhamBridge
    (G : GoodCoverPoincarePhysicalGeometry CoverIndex E F) :
    ConvexClosedOneFormGoodCoverData.GoodCoverCechDeRhamBridgeCertificate
      G.goodCover :=
  ConvexClosedOneFormGoodCoverData.goodCover_cechDeRham_bridge G.goodCover

/-- THEOREM 2: the Poincare-duality half supplies the current P280 generation
slot certificate. -/
def toCurrentCertificate
    (G : GoodCoverPoincarePhysicalGeometry CoverIndex E F) :
    FourDimensionalPoincareGenerationSlotCertificate where
  geometry := G.poincare

/-- THEOREM 3: the good-cover Poincare geometry is a valid P423 physical
geometry producer for the current Standard-Model track. -/
def adapter :
    PhysicalPoincareGeometryAdapter
      (GoodCoverPoincarePhysicalGeometry CoverIndex E F) where
  toCurrentCertificate := toCurrentCertificate

/-- THEOREM 4: the adapter exposes the same P280 slot certificate as the
producer's Poincare-duality field. -/
theorem adapter_toCurrentCertificate
    (G : GoodCoverPoincarePhysicalGeometry CoverIndex E F) :
    (adapter : PhysicalPoincareGeometryAdapter
      (GoodCoverPoincarePhysicalGeometry CoverIndex E F)).toCurrentCertificate G =
      G.toCurrentCertificate :=
  rfl

end GoodCoverPoincarePhysicalGeometry

end GeometryConnection
end AffineRelaxation

namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

/-! ## Good-cover strict-matrix unified front door -/

/-- The P430 strict-matrix producer with its physical geometry specialized to
the good-cover Čech/de Rham + 4D Poincare-duality obligation. -/
def ExistsGoodCoverPoincareStrictMatrixUnifiedProducer
    (Index A CKMCarrier CoverIndex E F : Type*) [AddCommGroup A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] : Prop :=
  ExistsMatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
      Index A CKMCarrier ∧
    Nonempty
      (GoodCoverPoincarePhysicalGeometry CoverIndex E F)

/-- THEOREM 5: this named good-cover front door is exactly P430's strict
matrix unified producer after specializing the physical-geometry type. -/
theorem goodCoverPoincareStrictMatrixUnifiedProducer_iff_strictPhysical
    {Index A CKMCarrier CoverIndex E F : Type*} [AddCommGroup A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    ExistsGoodCoverPoincareStrictMatrixUnifiedProducer
        Index A CKMCarrier CoverIndex E F ↔
      ExistsStrictPhysicalMatrixUnifiedProducer
        Index A CKMCarrier
        (GoodCoverPoincarePhysicalGeometry CoverIndex E F) := by
  rfl

/-- THEOREM 6: exact normal form with the good-cover geometry producer.  The
strict-matrix unified holy-grail output specialized to this geometry type is
nonempty exactly when the matrix sigma/RG table and good-cover Poincare
geometry producer are nonempty. -/
theorem goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_producer
    {Index A CKMCarrier CoverIndex E F : Type*} [AddCommGroup A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    Nonempty
        (StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier
          (GoodCoverPoincarePhysicalGeometry CoverIndex E F)
          GoodCoverPoincarePhysicalGeometry.adapter) ↔
      ExistsGoodCoverPoincareStrictMatrixUnifiedProducer
        Index A CKMCarrier CoverIndex E F := by
  exact
    (strictPhysicalMatrixUnifiedHolyGrailOutput_nonempty_iff_producer
      (GoodCoverPoincarePhysicalGeometry.adapter
        (CoverIndex := CoverIndex) (E := E) (F := F))).trans
      goodCoverPoincareStrictMatrixUnifiedProducer_iff_strictPhysical.symm

/-- THEOREM 7: compact downstream citation.  A matrix sigma/RG table plus a
good-cover Čech/de Rham + Poincare-duality producer supplies the current
holy-grail output and the unified 19-slot parameter-carrier certificate. -/
theorem goodCoverPoincareStrictMatrixUnified_holy_grail_normal_form
    {Index A CKMCarrier CoverIndex E F : Type*} [AddCommGroup A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    ExistsGoodCoverPoincareStrictMatrixUnifiedProducer
        Index A CKMCarrier CoverIndex E F ->
      ∃ O : StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier
          (GoodCoverPoincarePhysicalGeometry CoverIndex E F)
          GoodCoverPoincarePhysicalGeometry.adapter,
        ExistsGoodCoverPoincareStrictMatrixUnifiedProducer
          Index A CKMCarrier CoverIndex E F ∧
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
  intro h
  rcases
    strictPhysicalMatrixUnified_holy_grail_normal_form
      (GoodCoverPoincarePhysicalGeometry.adapter
        (CoverIndex := CoverIndex) (E := E) (F := F))
      ((goodCoverPoincareStrictMatrixUnifiedProducer_iff_strictPhysical).mp h)
    with ⟨O, _hproducer, hreceipt, hparam, hconj⟩
  exact ⟨O, h, hreceipt, hparam, hconj⟩

end StandardModelConstraint
end SaturationMonoid
