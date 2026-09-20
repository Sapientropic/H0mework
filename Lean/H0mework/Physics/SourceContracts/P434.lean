import H0mework.Physics.JointSources.P433

/-!
# Proposition 434: raw field normal form for the strict good-cover front door

P432 opens the strict good-cover Standard-Model front door to one field
producer, but that producer still contains two structured fields:

* `atoms : GrandUnificationPrimitiveProducerAtoms ...`;
* `matrixTable : MatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer atoms`.

This file removes that remaining wrapper layer.  The raw producer directly
extends the primitive atom fields and directly carries the matrix sigma/RG
step-table fields, together with the good-cover Čech/de Rham and 4D Poincare
fields.

No new physics is added.  The theorem is an exact normal form: the raw field
record is inhabited iff P432's field producer is inhabited, and it therefore
feeds P433's central holy-grail constants without any downstream wrapper.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

/-! ## Raw field-level producer -/

/-- The raw opened front door for the current strict good-cover Standard-Model
holy-grail theorem.

It extends the primitive producer atoms directly, then adds the dependent
`3 × 3` matrix sigma/RG table fields and the two good-cover/Poincare geometry
fields. -/
structure RawMatrixGoodCoverPoincareUnifiedProducerFields
    (Index A CKMCarrier CoverIndex E F : Type*) [AddCommGroup A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex]
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
  goodCover : ConvexClosedOneFormGoodCoverData CoverIndex E F
  poincare : PoincareDualityCohomologyCertificate.{0} 4

namespace RawMatrixGoodCoverPoincareUnifiedProducerFields

variable {Index A CKMCarrier CoverIndex E F : Type*} [AddCommGroup A]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable [Inhabited CoverIndex]

/-- THEOREM 1: the raw field record repacks into P424's matrix table on its
own primitive atom payload. -/
def toMatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
    (R : RawMatrixGoodCoverPoincareUnifiedProducerFields
      Index A CKMCarrier CoverIndex E F) :
    MatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
      R.toGrandUnificationPrimitiveProducerAtoms where
  step := R.step
  reach_not_sigma_order := R.reach_not_sigma_order
  fourPi_eq_realFourPi := R.fourPi_eq_realFourPi
  matrix_reaches_weak := R.matrix_reaches_weak
  step_sigma_monotone := R.step_sigma_monotone

/-- THEOREM 2: the raw field record repacks into P432's field-level front
door. -/
def toMatrixGoodCoverPoincareUnifiedProducerFields
    (R : RawMatrixGoodCoverPoincareUnifiedProducerFields
      Index A CKMCarrier CoverIndex E F) :
    MatrixGoodCoverPoincareUnifiedProducerFields
      Index A CKMCarrier CoverIndex E F where
  atoms := R.toGrandUnificationPrimitiveProducerAtoms
  matrixTable := R.toMatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
  goodCover := R.goodCover
  poincare := R.poincare

/-- THEOREM 3: P432's field-level front door opens into the raw field record. -/
def ofMatrixGoodCoverPoincareUnifiedProducerFields
    (P : MatrixGoodCoverPoincareUnifiedProducerFields
      Index A CKMCarrier CoverIndex E F) :
    RawMatrixGoodCoverPoincareUnifiedProducerFields
      Index A CKMCarrier CoverIndex E F where
  toGrandUnificationPrimitiveProducerAtoms := P.atoms
  step := P.matrixTable.step
  reach_not_sigma_order := P.matrixTable.reach_not_sigma_order
  fourPi_eq_realFourPi := P.matrixTable.fourPi_eq_realFourPi
  matrix_reaches_weak := P.matrixTable.matrix_reaches_weak
  step_sigma_monotone := P.matrixTable.step_sigma_monotone
  goodCover := P.goodCover
  poincare := P.poincare

/-- THEOREM 4: the raw record exposes the same good-cover Čech/de Rham bridge
as its field. -/
theorem cechDeRhamBridge
    (R : RawMatrixGoodCoverPoincareUnifiedProducerFields
      Index A CKMCarrier CoverIndex E F) :
    ConvexClosedOneFormGoodCoverData.GoodCoverCechDeRhamBridgeCertificate
      R.goodCover :=
  ConvexClosedOneFormGoodCoverData.goodCover_cechDeRham_bridge R.goodCover

/-- THEOREM 5: the raw record exposes the P280 current generation-slot
certificate from its Poincare-duality field. -/
def toCurrentCertificate
    (R : RawMatrixGoodCoverPoincareUnifiedProducerFields
      Index A CKMCarrier CoverIndex E F) :
    FourDimensionalPoincareGenerationSlotCertificate where
  geometry := R.poincare

end RawMatrixGoodCoverPoincareUnifiedProducerFields

/-! ## Raw-field exact normal form -/

/-- THEOREM 6: P432's field-level producer is inhabited iff the raw field
record is inhabited. -/
theorem matrixGoodCoverPoincareUnifiedProducerFields_nonempty_iff_rawFields
    {Index A CKMCarrier CoverIndex E F : Type*} [AddCommGroup A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    Nonempty
        (MatrixGoodCoverPoincareUnifiedProducerFields
          Index A CKMCarrier CoverIndex E F) ↔
      Nonempty
        (RawMatrixGoodCoverPoincareUnifiedProducerFields
          Index A CKMCarrier CoverIndex E F) := by
  constructor
  · rintro ⟨P⟩
    exact
      ⟨RawMatrixGoodCoverPoincareUnifiedProducerFields.ofMatrixGoodCoverPoincareUnifiedProducerFields P⟩
  · rintro ⟨R⟩
    exact
      ⟨R.toMatrixGoodCoverPoincareUnifiedProducerFields⟩

/-- THEOREM 7: the strict good-cover holy-grail output exists exactly when the
raw field record is inhabited. -/
theorem goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_rawFields
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
        (RawMatrixGoodCoverPoincareUnifiedProducerFields
          Index A CKMCarrier CoverIndex E F) := by
  exact
    goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_fieldProducer.trans
      matrixGoodCoverPoincareUnifiedProducerFields_nonempty_iff_rawFields

/-- THEOREM 8: compact raw-field citation.  The raw record directly supplies
the P433 central constants and the unified 19-slot affine carrier certificate. -/
theorem rawMatrixGoodCoverPoincareUnified_central_holy_grail_constants
    {Index A CKMCarrier CoverIndex E F : Type*} [AddCommGroup A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    RawMatrixGoodCoverPoincareUnifiedProducerFields
        Index A CKMCarrier CoverIndex E F ->
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
      R.toMatrixGoodCoverPoincareUnifiedProducerFields

end StandardModelConstraint
end SaturationMonoid
