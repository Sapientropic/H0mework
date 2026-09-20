import H0mework.Physics.SourceContracts.P429

/-!
# Proposition 430: exact strict-matrix unified holy-grail normal form

P429 proves that the strict physical matrix front door supplies the current
Standard-Model holy-grail output together with the unified affine-relaxation
certificate on the full 19-slot parameter carrier.

This file turns that implication into an exact normal form.  A strict-matrix
unified holy-grail output is precisely:

* a matrix-indexed primitive sigma/RG table;
* an independent physical Poincare-geometry producer;
* the current concrete holy-grail output;
* the P428 parameter-carrier certificates and component conjugacy.

The final theorem is an iff: such an output exists exactly when the strict
matrix unified producer exists.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

/-! ## Exact output structure -/

/-- The strict matrix unified holy-grail output: the physical front door, the
current concrete Standard-Model holy-grail output, and the unified affine
parameter-carrier certificate carried together. -/
structure StrictPhysicalMatrixUnifiedHolyGrailOutput
    (Index A CKMCarrier PhysicalGeometry : Type*) [AddCommGroup A]
    (_adapter : PhysicalPoincareGeometryAdapter PhysicalGeometry) where
  matrixTable :
    ExistsMatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
      Index A CKMCarrier
  physicalGeometry : Nonempty PhysicalGeometry
  output : StandardModelPoincareHolyGrailOutput Index A CKMCarrier
  receiptStatement : SingleSourceHolyGrailReceiptStatement output.receipt
  generationSlotEquiv :
    Nonempty (StandardModelFermionGeneration ≃ FourDimensionalPoincareSlot)
  yukawaPoincareSurjective : Function.Surjective yukawaPoincareSlot
  noFourthGeneration : IsEmpty (Fin 4 ↪ StandardModelFermionGeneration)
  parameterVectorCertificate :
    AffineRelaxation.UnifiedAffineRelaxationModuleCertificate
      ℝ (ParameterVector ℝ)
  yukawaMatrixCertificate :
    AffineRelaxation.UnifiedAffineRelaxationModuleCertificate
      ℝ (YukawaMatrixSubvector ℝ)
  nonYukawaCertificate :
    AffineRelaxation.UnifiedAffineRelaxationModuleCertificate
      ℝ (NonYukawaSubvector ℝ)
  componentProductCertificate :
    AffineRelaxation.UnifiedAffineRelaxationModuleCertificate
      ℝ (YukawaMatrixSubvector ℝ × NonYukawaSubvector ℝ)
  componentConjugacy :
    ∀ target x : ParameterVector ℝ, ∀ sigma : ℝ,
      parameterVectorComponentsEquiv ℝ
          (AffineRelaxation.relaxModule target sigma x) =
        AffineRelaxation.relaxModule
          (parameterVectorComponentsEquiv ℝ target)
          sigma
          (parameterVectorComponentsEquiv ℝ x)

namespace StrictPhysicalMatrixUnifiedHolyGrailOutput

variable {Index A CKMCarrier PhysicalGeometry : Type*} [AddCommGroup A]
variable {adapter : PhysicalPoincareGeometryAdapter PhysicalGeometry}

/-- THEOREM 1: a strict-matrix unified output exposes exactly the current
strict matrix unified producer surface. -/
theorem toStrictPhysicalMatrixUnifiedProducer
    (O : StrictPhysicalMatrixUnifiedHolyGrailOutput
      Index A CKMCarrier PhysicalGeometry adapter) :
    ExistsStrictPhysicalMatrixUnifiedProducer
      Index A CKMCarrier PhysicalGeometry :=
  ⟨O.matrixTable, O.physicalGeometry⟩

/-- THEOREM 2: its concrete output is still the current Poincare holy-grail
output package. -/
theorem concrete_holy_grail_output
    (O : StrictPhysicalMatrixUnifiedHolyGrailOutput
      Index A CKMCarrier PhysicalGeometry adapter) :
    SingleSourceHolyGrailReceiptStatement O.output.receipt ∧
      Nonempty
        (StandardModelFermionGeneration ≃ FourDimensionalPoincareSlot) ∧
      Function.Surjective yukawaPoincareSlot ∧
      IsEmpty (Fin 4 ↪ StandardModelFermionGeneration) :=
  ⟨O.receiptStatement, O.generationSlotEquiv,
    O.yukawaPoincareSurjective, O.noFourthGeneration⟩

/-- THEOREM 3: its parameter carrier carries the P242 certificate and the P426
component equivalence conjugates uniform relaxation. -/
theorem unified_parameter_carrier
    (O : StrictPhysicalMatrixUnifiedHolyGrailOutput
      Index A CKMCarrier PhysicalGeometry adapter) :
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
            (parameterVectorComponentsEquiv ℝ x)) :=
  ⟨O.parameterVectorCertificate, O.yukawaMatrixCertificate,
    O.nonYukawaCertificate, O.componentProductCertificate,
    O.componentConjugacy⟩

end StrictPhysicalMatrixUnifiedHolyGrailOutput

/-! ## Exact normal form -/

/-- THEOREM 4: a strict matrix unified producer constructs the exact
strict-matrix unified holy-grail output. -/
theorem strictPhysicalMatrixUnifiedHolyGrailOutput_nonempty_of_producer
    {Index A CKMCarrier PhysicalGeometry : Type*} [AddCommGroup A]
    (adapter : PhysicalPoincareGeometryAdapter PhysicalGeometry) :
    ExistsStrictPhysicalMatrixUnifiedProducer
        Index A CKMCarrier PhysicalGeometry ->
      Nonempty
        (StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier PhysicalGeometry adapter) := by
  intro h
  rcases
    strictPhysicalMatrixUnified_concrete_holy_grail_output adapter h with
    ⟨O, hreceipt, hgen, hsurj, hno4, hparam, hmatrix,
      hnon, hproduct, hconj⟩
  exact
    ⟨{ matrixTable := h.1
       physicalGeometry := h.2
       output := O
       receiptStatement := hreceipt
       generationSlotEquiv := hgen
       yukawaPoincareSurjective := hsurj
       noFourthGeneration := hno4
       parameterVectorCertificate := hparam
       yukawaMatrixCertificate := hmatrix
       nonYukawaCertificate := hnon
       componentProductCertificate := hproduct
       componentConjugacy := hconj }⟩

/-- THEOREM 5: exact normal form.  The strict-matrix unified holy-grail output
exists iff the strict physical matrix unified producer exists. -/
theorem strictPhysicalMatrixUnifiedHolyGrailOutput_nonempty_iff_producer
    {Index A CKMCarrier PhysicalGeometry : Type*} [AddCommGroup A]
    (adapter : PhysicalPoincareGeometryAdapter PhysicalGeometry) :
    Nonempty
        (StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier PhysicalGeometry adapter) ↔
      ExistsStrictPhysicalMatrixUnifiedProducer
        Index A CKMCarrier PhysicalGeometry := by
  constructor
  · rintro ⟨O⟩
    exact O.toStrictPhysicalMatrixUnifiedProducer
  · exact strictPhysicalMatrixUnifiedHolyGrailOutput_nonempty_of_producer
      adapter

/-- THEOREM 6: compact downstream citation for the exact strict-matrix unified
normal form. -/
theorem strictPhysicalMatrixUnified_holy_grail_normal_form
    {Index A CKMCarrier PhysicalGeometry : Type*} [AddCommGroup A]
    (adapter : PhysicalPoincareGeometryAdapter PhysicalGeometry) :
    ExistsStrictPhysicalMatrixUnifiedProducer
        Index A CKMCarrier PhysicalGeometry ->
      ∃ O : StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier PhysicalGeometry adapter,
        ExistsStrictPhysicalMatrixUnifiedProducer
          Index A CKMCarrier PhysicalGeometry ∧
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
    strictPhysicalMatrixUnifiedHolyGrailOutput_nonempty_of_producer adapter h
    with ⟨O⟩
  exact
    ⟨O, O.toStrictPhysicalMatrixUnifiedProducer,
      O.receiptStatement, O.parameterVectorCertificate,
      O.componentConjugacy⟩

end StandardModelConstraint
end SaturationMonoid
