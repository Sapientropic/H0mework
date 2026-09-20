import H0mework.Realization.Descent.P435

/-!
# Proposition 436: matrix-only holy-grail normal form

P435 audits the current good-cover/Poincare geometry interface: under the
explicit formal-exact geometry inhabitant, the strict good-cover holy-grail
output is equivalent to the matrix sigma/RG table producer alone.

This file opens that last wrapper.  The remaining producer is a raw
matrix-only field record:

* primitive grand-unification atoms;
* one RG step relation;
* the non-order reach certificate;
* `4π = realFourPi`;
* the `3 × 3` Yukawa-to-weak reachability table;
* sigma monotonicity along RG steps.

No geometry fields remain here.  This is therefore the current Lean front door
for the "grand-unification holy grail": all central constants and the unified
19-slot affine carrier are downstream of exactly this matrix-only producer,
provided we work under the P435 formal-exact geometry audit.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

/-! ## Matrix-only raw producer -/

/-- The geometry-free raw producer left after the P435 formal-exact geometry
collapse.

It directly extends the primitive atom payload and carries exactly the
dependent `3 × 3` matrix sigma/RG table fields. -/
structure RawMatrixUnifiedProducerFields
    (Index A CKMCarrier : Type*) [AddCommGroup A]
    extends GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier where
  step : StandardModelScaleCode -> StandardModelScaleCode -> Prop
  reach_not_sigma_order :
    RGStepReach step ≠
      fun a b : StandardModelScaleCode => sigma a ≤ sigma b
  fourPi_eq_realFourPi : fourPi = realFourPi
  matrix_reaches_weak :
    ∀ g s,
      RGStepReach step
        (StandardModelScaleCode.yukawa (yukawaMatrixParameter g s))
        StandardModelScaleCode.weak
  step_sigma_monotone :
    ∀ {a b : StandardModelScaleCode}, step a b -> sigma a ≤ sigma b

namespace RawMatrixUnifiedProducerFields

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- THEOREM 1: the raw matrix-only record repacks into P424's matrix table on
its own primitive atom payload. -/
def toMatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
    (R : RawMatrixUnifiedProducerFields Index A CKMCarrier) :
    MatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
      R.toGrandUnificationPrimitiveProducerAtoms where
  step := R.step
  reach_not_sigma_order := R.reach_not_sigma_order
  fourPi_eq_realFourPi := R.fourPi_eq_realFourPi
  matrix_reaches_weak := R.matrix_reaches_weak
  step_sigma_monotone := R.step_sigma_monotone

/-- THEOREM 2: P424's matrix table opens to the raw matrix-only record. -/
def ofMatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
    {atoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier}
    (C : MatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer atoms) :
    RawMatrixUnifiedProducerFields Index A CKMCarrier where
  toGrandUnificationPrimitiveProducerAtoms := atoms
  step := C.step
  reach_not_sigma_order := C.reach_not_sigma_order
  fourPi_eq_realFourPi := C.fourPi_eq_realFourPi
  matrix_reaches_weak := C.matrix_reaches_weak
  step_sigma_monotone := C.step_sigma_monotone

end RawMatrixUnifiedProducerFields

/-! ## Existence-level normal form -/

/-- THEOREM 3: P424's matrix producer exists iff the raw matrix-only record is
inhabited. -/
theorem existsMatrixPrimitiveTable_iff_rawMatrixUnifiedFields
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsMatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
        Index A CKMCarrier ↔
      Nonempty (RawMatrixUnifiedProducerFields Index A CKMCarrier) := by
  constructor
  · rintro ⟨atoms, ⟨C⟩⟩
    exact
      ⟨RawMatrixUnifiedProducerFields.ofMatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer C⟩
  · rintro ⟨R⟩
    exact
      ⟨R.toGrandUnificationPrimitiveProducerAtoms,
        ⟨R.toMatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer⟩⟩

/-- THEOREM 4: under P435's current formal-exact geometry audit, the strict
good-cover holy-grail output exists exactly when the raw matrix-only producer
is inhabited. -/
theorem goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_rawMatrixUnifiedFields_under_currentFormalExactGeometry
    {Index A CKMCarrier CoverIndex E F : Type*} [AddCommGroup A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    Nonempty
        (StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier
          (GoodCoverPoincarePhysicalGeometry CoverIndex E F)
          GoodCoverPoincarePhysicalGeometry.adapter) ↔
      Nonempty (RawMatrixUnifiedProducerFields Index A CKMCarrier) := by
  exact
    goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_matrixTable_under_currentFormalExactGeometry.trans
      existsMatrixPrimitiveTable_iff_rawMatrixUnifiedFields

/-- THEOREM 5: compact matrix-only holy-grail citation.  Under the current
formal-exact geometry audit, the raw matrix-only producer already supplies the
P433 central constants and the unified 19-slot affine carrier certificate. -/
theorem rawMatrixUnified_currentFormalExactGeometry_central_holy_grail_constants
    {Index A CKMCarrier CoverIndex E F : Type*} [AddCommGroup A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    RawMatrixUnifiedProducerFields Index A CKMCarrier ->
      ∃ O : StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier
          (GoodCoverPoincarePhysicalGeometry CoverIndex E F)
          GoodCoverPoincarePhysicalGeometry.adapter,
        NoContinuousFreeParameters
          O.output.receipt.receipt.spine.target.sampled.zeroFree.running.pinned.base.constraints ∧
        (∀ p : ParameterVector ℝ,
          O.output.receipt.receipt.spine.target.sampled.zeroFree.running.pinned.base.constraints p ->
            p StandardModelParameter.qcd_theta = 0) ∧
        alphaEMFromIntegerConstraint ℝ = (1 : ℝ) / (137 : ℝ) ∧
        gutWeakMixingFromStructuralCards ℝ = threeEighths ℝ ∧
        alphaGUTInverseFromStructuralCards ℝ = ((133 : ℝ) / (3 : ℝ)) ∧
        O.output.receipt.receipt.spine.target.strongResidualProducer.correctedOutput =
          alphaStrongDisplayed ℝ ∧
        (ckmCPDepthSum : ℝ) *
            O.output.receipt.receipt.spine.target.cpRunningSigma =
          cpRawPhaseClaim ℝ ∧
        cpDeltaCPClaim ℝ =
          cpTauProxy ℝ -
            (ckmCPDepthSum : ℝ) *
              O.output.receipt.receipt.spine.target.cpRunningSigma ∧
        (∀ p : ParameterVector ℝ,
          O.output.receipt.receipt.spine.target.sampled.zeroFree.running.pinned.base.constraints p ->
            ∀ y : YukawaParameter,
              p (yukawaSlot y) =
                O.output.receipt.receipt.spine.target.sampled.zeroFree.running.pinned.yukawaAmplitude y *
                  AffineRelaxation.realDecayResidual
                    (O.output.receipt.receipt.spine.target.sampled.yukawaLambda y)
                    ((O.output.receipt.receipt.spine.target.sampled.zeroFree.running.pinned.yukawaExponent
                        O.output.receipt.receipt.spine.target.sampled.zeroFree.selectedSeed y : ℝ) *
                      O.output.receipt.receipt.spine.target.sampled.yukawaStep y)) ∧
        Nonempty
          (StandardModelFermionGeneration ≃ FourDimensionalPoincareSlot) ∧
        Function.Surjective yukawaPoincareSlot ∧
        IsEmpty (Fin 4 ↪ StandardModelFermionGeneration) ∧
        AffineRelaxation.UnifiedAffineRelaxationModuleCertificate
          ℝ (ParameterVector ℝ) ∧
        (∀ target x : ParameterVector ℝ, ∀ sigma : ℝ,
          parameterVectorComponentsEquiv ℝ
              (AffineRelaxation.relaxModule target sigma x) =
            AffineRelaxation.relaxModule
              (parameterVectorComponentsEquiv ℝ target)
              sigma
              (parameterVectorComponentsEquiv ℝ x)) := by
  intro R
  exact
    matrixGoodCoverPoincareUnified_field_central_holy_grail_constants
      { atoms := R.toGrandUnificationPrimitiveProducerAtoms
        matrixTable := R.toMatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
        goodCover :=
          formalZeroGoodCoverData CoverIndex E F
        poincare :=
          FourDimensionalPoincareOrbitCohomologyNormalForm.unitOrbitNormalForm.toPoincareDualityCohomologyCertificate }

end StandardModelConstraint
end SaturationMonoid
