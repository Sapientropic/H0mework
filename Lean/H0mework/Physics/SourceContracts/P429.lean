import H0mework.Physics.CouplingSources.P428

/-!
# Proposition 429: strict matrix front door plus unified parameter carrier

P424 gives the current strict physical front door in matrix coordinates:

* a primitive-atom-native `3 × 3` Yukawa sigma/RG table;
* an independent physical Poincare-geometry producer.

P428 gives the uniform affine-relaxation certificate on the full 19-slot
Standard-Model parameter carrier and proves that the `3 × 3` Yukawa /
non-Yukawa-complement split conjugates the formula exactly.

This file puts those two central pieces in one normal form.  The strict matrix
front door does not merely produce the current holy-grail output package; it
does so while the whole parameter surface is already equipped with the unified
P242 affine-relaxation certificate.

Boundary: this is still a front-door normal form.  It does not construct the
physical matrix sigma table or the smooth/de Rham/Poincare geometry producer.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

/-! ## Strict matrix unified front door -/

/-- The current strict grand-unification producer, in the coordinate system
where the nine Yukawa rows are a `3 × 3` matrix and the Poincare producer is a
separate physical object. -/
def ExistsStrictPhysicalMatrixUnifiedProducer
    (Index A CKMCarrier PhysicalGeometry : Type*) [AddCommGroup A] : Prop :=
  ExistsMatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
      Index A CKMCarrier ∧
    Nonempty PhysicalGeometry

/-- THEOREM 1: the strict matrix unified producer is definitionally the matrix
table plus physical-geometry front door. -/
theorem strictPhysicalMatrixUnifiedProducer_iff_matrixTable_and_physical
    {Index A CKMCarrier PhysicalGeometry : Type*} [AddCommGroup A] :
    ExistsStrictPhysicalMatrixUnifiedProducer
        Index A CKMCarrier PhysicalGeometry ↔
      ExistsMatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
        Index A CKMCarrier ∧
        Nonempty PhysicalGeometry := by
  rfl

/-- THEOREM 2: the strict matrix unified producer is exactly P423's strict
nine-row Poincare front door after P424's matrix normal form. -/
theorem strictPhysicalMatrixUnifiedProducer_iff_strictPhysicalNineRowPoincare
    {Index A CKMCarrier PhysicalGeometry : Type*} [AddCommGroup A]
    (adapter : PhysicalPoincareGeometryAdapter PhysicalGeometry) :
    ExistsStrictPhysicalMatrixUnifiedProducer
        Index A CKMCarrier PhysicalGeometry ↔
      ExistsStrictPhysicalNineRowPoincareProducer
        Index A CKMCarrier PhysicalGeometry adapter := by
  rw [strictPhysicalNineRowPoincare_nonempty_iff_matrixTable_and_physical
    adapter]
  rfl

/-! ## Parameter-carrier certificates exposed at the same front door -/

/-- THEOREM 3: the full 19-slot Standard-Model parameter carrier carries the
P242 unified affine-relaxation certificate. -/
theorem strictPhysicalMatrixUnified_parameterVector_certificate :
    AffineRelaxation.UnifiedAffineRelaxationModuleCertificate
      ℝ (ParameterVector ℝ) :=
  parameterVector_unifiedAffineRelaxationModuleCertificate ℝ

/-- THEOREM 4: the matrix/complement component product carrier carries the
same P242 unified affine-relaxation certificate. -/
theorem strictPhysicalMatrixUnified_componentProduct_certificate :
    AffineRelaxation.UnifiedAffineRelaxationModuleCertificate
      ℝ (YukawaMatrixSubvector ℝ × NonYukawaSubvector ℝ) :=
  parameterVectorComponentProduct_unifiedAffineRelaxationModuleCertificate ℝ

/-- THEOREM 5: under the P426 component equivalence, uniform relaxation on the
full parameter vector is exactly product-carrier uniform relaxation on the
matrix Yukawa subvector and ten-slot complement. -/
theorem strictPhysicalMatrixUnified_component_conjugacy
    (target x : ParameterVector ℝ) (sigma : ℝ) :
    parameterVectorComponentsEquiv ℝ
        (AffineRelaxation.relaxModule target sigma x) =
      AffineRelaxation.relaxModule
        (parameterVectorComponentsEquiv ℝ target)
        sigma
        (parameterVectorComponentsEquiv ℝ x) :=
  parameterVectorComponentsEquiv_relaxModule target x sigma

/-! ## Compact unified holy-grail output -/

/-- THEOREM 6: the strict physical matrix front door supplies the current
concrete holy-grail output and, in the same theorem, exposes the unified
affine-relaxation certificate on the full 19-slot parameter carrier and its
matrix/complement component carrier. -/
theorem strictPhysicalMatrixUnified_concrete_holy_grail_output
    {Index A CKMCarrier PhysicalGeometry : Type*} [AddCommGroup A]
    (adapter : PhysicalPoincareGeometryAdapter PhysicalGeometry) :
    ExistsStrictPhysicalMatrixUnifiedProducer
        Index A CKMCarrier PhysicalGeometry ->
      ∃ O : StandardModelPoincareHolyGrailOutput Index A CKMCarrier,
        SingleSourceHolyGrailReceiptStatement O.receipt ∧
          Nonempty
            (StandardModelFermionGeneration ≃ FourDimensionalPoincareSlot) ∧
          Function.Surjective yukawaPoincareSlot ∧
          IsEmpty (Fin 4 ↪ StandardModelFermionGeneration) ∧
          AffineRelaxation.UnifiedAffineRelaxationModuleCertificate
            ℝ (ParameterVector ℝ) ∧
          AffineRelaxation.UnifiedAffineRelaxationModuleCertificate
            ℝ (YukawaMatrixSubvector ℝ) ∧
          AffineRelaxation.UnifiedAffineRelaxationModuleCertificate
            ℝ (NonYukawaSubvector ℝ) ∧
          AffineRelaxation.UnifiedAffineRelaxationModuleCertificate
            ℝ (YukawaMatrixSubvector ℝ × NonYukawaSubvector ℝ) ∧
          (∀ target x : ParameterVector ℝ, ∀ sigma : ℝ,
            parameterVectorComponentsEquiv ℝ
                (AffineRelaxation.relaxModule target sigma x) =
              AffineRelaxation.relaxModule
                (parameterVectorComponentsEquiv ℝ target)
                sigma
                (parameterVectorComponentsEquiv ℝ x)) := by
  intro h
  rcases
    strictPhysicalMatrixNineRow_concrete_holy_grail_output adapter h with
    ⟨O, hreceipt, hgen, hsurj, hno4⟩
  exact
    ⟨O, hreceipt, hgen, hsurj, hno4,
      parameterVector_unifiedAffineRelaxationModuleCertificate ℝ,
      yukawaMatrixSubvector_unifiedAffineRelaxationModuleCertificate ℝ,
      nonYukawaSubvector_unifiedAffineRelaxationModuleCertificate ℝ,
      parameterVectorComponentProduct_unifiedAffineRelaxationModuleCertificate ℝ,
      fun target x sigma =>
        parameterVectorComponentsEquiv_relaxModule target x sigma⟩

end StandardModelConstraint
end SaturationMonoid
