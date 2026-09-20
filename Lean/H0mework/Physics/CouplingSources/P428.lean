import H0mework.Physics.JointSources.P427

/-!
# Proposition 428: the bundled unified-affine certificate on SM parameter carriers

P427 proved the pointwise variable-rate law on the 19-slot parameter vector.
This file pins the uniform-rate, module-valued P242 certificate directly to the
Standard-Model-facing carriers:

* the whole `ParameterVector K`;
* the `3 × 3` Yukawa matrix subvector;
* the ten-slot non-Yukawa complement;
* their product carrier.

It also proves that the P426 component equivalence conjugates uniform-rate
`relaxModule` on the 19-slot carrier to ordinary product-carrier `relaxModule`.

Boundary: the theorem identifies the algebraic carrier and formula.  It still
does not construct the physical producer that selects target/rate vectors.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## P242 certificate instances on Standard-Model parameter carriers -/

/-- THEOREM 1: the complete 19-slot parameter vector carrier satisfies the
bundled P242 unified-affine relaxation certificate. -/
theorem parameterVector_unifiedAffineRelaxationModuleCertificate
    (K : Type*) [Field K] :
    AffineRelaxation.UnifiedAffineRelaxationModuleCertificate
      K (ParameterVector K) :=
  AffineRelaxation.unifiedAffineRelaxationModuleCertificate

/-- THEOREM 2: the `3 × 3` Yukawa matrix subvector carrier satisfies the
bundled P242 unified-affine relaxation certificate. -/
theorem yukawaMatrixSubvector_unifiedAffineRelaxationModuleCertificate
    (K : Type*) [Field K] :
    AffineRelaxation.UnifiedAffineRelaxationModuleCertificate
      K (YukawaMatrixSubvector K) :=
  AffineRelaxation.unifiedAffineRelaxationModuleCertificate

/-- THEOREM 3: the ten-slot non-Yukawa complement carrier satisfies the
bundled P242 unified-affine relaxation certificate. -/
theorem nonYukawaSubvector_unifiedAffineRelaxationModuleCertificate
    (K : Type*) [Field K] :
    AffineRelaxation.UnifiedAffineRelaxationModuleCertificate
      K (NonYukawaSubvector K) :=
  AffineRelaxation.unifiedAffineRelaxationModuleCertificate

/-- THEOREM 4: the product carrier supplied by the P426 decomposition satisfies
the bundled P242 unified-affine relaxation certificate. -/
theorem parameterVectorComponentProduct_unifiedAffineRelaxationModuleCertificate
    (K : Type*) [Field K] :
    AffineRelaxation.UnifiedAffineRelaxationModuleCertificate
      K (YukawaMatrixSubvector K × NonYukawaSubvector K) :=
  AffineRelaxation.unifiedAffineRelaxationModuleCertificate

/-! ## Uniform-rate conjugacy across the P426 component equivalence -/

/-- THEOREM 5: projecting a uniform-rate whole-vector `relaxModule` to the
Yukawa matrix equals uniform-rate `relaxModule` on the projected matrix data. -/
theorem parameterVectorToYukawaMatrix_relaxModule
    {K : Type*} [Field K]
    (target x : ParameterVector K) (sigma : K) :
    parameterVectorToYukawaMatrix
        (AffineRelaxation.relaxModule target sigma x) =
      AffineRelaxation.relaxModule
        (parameterVectorToYukawaMatrix target) sigma
        (parameterVectorToYukawaMatrix x) := by
  funext g s
  rfl

/-- THEOREM 6: projecting a uniform-rate whole-vector `relaxModule` to the
non-Yukawa complement equals uniform-rate `relaxModule` on the projected
complement data. -/
theorem parameterVectorToNonYukawaComplement_relaxModule
    {K : Type*} [Field K]
    (target x : ParameterVector K) (sigma : K) :
    parameterVectorToNonYukawaComplement
        (AffineRelaxation.relaxModule target sigma x) =
      AffineRelaxation.relaxModule
        (parameterVectorToNonYukawaComplement target) sigma
        (parameterVectorToNonYukawaComplement x) := by
  funext n
  cases n <;> rfl

/-- THEOREM 7: reconstructing after componentwise uniform-rate `relaxModule`
is exactly whole-vector uniform-rate `relaxModule` after reconstruction. -/
theorem parameterVectorFromComponents_relaxModule
    {K : Type*} [Field K]
    (targetY xY : YukawaMatrixSubvector K)
    (targetN xN : NonYukawaSubvector K)
    (sigma : K) :
    parameterVectorFromComponents
        (AffineRelaxation.relaxModule targetY sigma xY)
        (AffineRelaxation.relaxModule targetN sigma xN) =
      AffineRelaxation.relaxModule
        (parameterVectorFromComponents targetY targetN)
        sigma
        (parameterVectorFromComponents xY xN) := by
  funext slot
  cases slot <;> rfl

/-- THEOREM 8: P426's component equivalence conjugates uniform-rate
`relaxModule` on the 19-slot carrier to ordinary product-carrier
`relaxModule`. -/
theorem parameterVectorComponentsEquiv_relaxModule
    {K : Type*} [Field K]
    (target x : ParameterVector K) (sigma : K) :
    parameterVectorComponentsEquiv K
        (AffineRelaxation.relaxModule target sigma x) =
      AffineRelaxation.relaxModule
        (parameterVectorComponentsEquiv K target)
        sigma
        (parameterVectorComponentsEquiv K x) := by
  apply Prod.ext
  · exact parameterVectorToYukawaMatrix_relaxModule target x sigma
  · exact parameterVectorToNonYukawaComplement_relaxModule target x sigma

/-- THEOREM 9: the inverse direction of the same conjugacy: going from product
components back to the 19-slot carrier commutes with uniform-rate
`relaxModule`. -/
theorem parameterVectorComponentsEquiv_symm_relaxModule
    {K : Type*} [Field K]
    (target x : YukawaMatrixSubvector K × NonYukawaSubvector K)
    (sigma : K) :
    (parameterVectorComponentsEquiv K).symm
        (AffineRelaxation.relaxModule target sigma x) =
      AffineRelaxation.relaxModule
        ((parameterVectorComponentsEquiv K).symm target)
        sigma
        ((parameterVectorComponentsEquiv K).symm x) := by
  rcases target with ⟨targetY, targetN⟩
  rcases x with ⟨xY, xN⟩
  exact parameterVectorFromComponents_relaxModule
    targetY xY targetN xN sigma

/-- THEOREM 10: the whole-vector P242 certificate transported through the
P426 equivalence is the product-carrier P242 certificate at the level of the
actual update operation. -/
theorem parameterVector_unifiedRelaxation_conjugates_to_components
    {K : Type*} [Field K]
    (target x : ParameterVector K) (sigma : K) :
    parameterVectorComponentsEquiv K
        (AffineRelaxation.relaxModule target sigma x) =
      AffineRelaxation.relaxModule
        (parameterVectorComponentsEquiv K target)
        sigma
        (parameterVectorComponentsEquiv K x) :=
  parameterVectorComponentsEquiv_relaxModule target x sigma

end StandardModelConstraint
end SaturationMonoid
