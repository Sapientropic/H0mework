import H0mework.Physics.FinalJoint.FixedActionWrite
import H0mework.Physics.IdentityHessian.CartanECNormalFixedGlobalRegularity
import H0mework.Physics.Coframe.CurrentCoframeMatterTimeResponse

/-!
# Fixed P506/L0 final-common time-axis coframe

This module reads the coframe retained by the final common action write from
the already generated KIN-16 primitive diagonal.  On every recentered fixed
P506/L0 occurrence it gives the literal quadratic normal form on the
canonical time axis.  In particular, the time row and column remain the
identity row and column for every time.

The construction is source/action forward: no determinant value, residual
coordinate, target coframe, radius, branch, or nondegeneracy certificate is
an input.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisCoframe

open DiracExteriorMatterAction
open DiracCliffordRepresentation
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeHolonomicSecondJetCarrier
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedContactRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalJointLocalActualLift
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianSection
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianUpdate
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionPrincipal
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionResponse
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineMatterActionTimeVelocity
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedCompleteP286CauchyPath

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-! ## Generated quadratic normal form -/

/-- The fixed contact's source/action-generated holonomic coframe Hessian. -/
abbrev fixedP506L0ContactCoframeHessian
    (space : StageNineSpatialPoint) : CoframeHolonomicSecondJet :=
  sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
    positiveSmoothUnifiedSource (fixedCartanReactionContact space)

private theorem fixedP506L0TimeAxisPoint
    (time : ℝ) :
    canonicalCauchySlicePoint time 0 =
      time • coordinateDirection canonicalLorentzianTimeDirection := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, coordinateDirection,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]

private theorem identityECNormalCoframeHessianCoordinate_timeRow
    (coordinates : LorentzianCoframe)
    (column : LorentzianIndex) :
    identityECNormalCoframeHessianCoordinate coordinates
      0 0 0 column = 0 := by
  fin_cases column <;>
    simp [identityECNormalCoframeHessianCoordinate,
      identityECNormalMetricHessianCoordinate,
      identityECWeylZeroRiemannCoordinate,
      identityECRicciTensorCoordinate,
      identityECEinsteinTensorCoordinate,
      identityECEinsteinTrace,
      identityECScalarCurvature,
      identityECMinkowskiMetricCoordinate,
      identityECEtaSymmetricPart,
      identityECEtaAdjoint,
      minkowskiInternalSign,
      Fin.sum_univ_four]

private theorem identityECNormalCoframeHessianCoordinate_timeColumn
    (coordinates : LorentzianCoframe)
    (internal : LorentzianIndex) :
    identityECNormalCoframeHessianCoordinate coordinates
      0 0 internal 0 = 0 := by
  fin_cases internal <;>
    simp [identityECNormalCoframeHessianCoordinate,
      identityECNormalMetricHessianCoordinate,
      identityECWeylZeroRiemannCoordinate,
      identityECRicciTensorCoordinate,
      identityECEinsteinTensorCoordinate,
      identityECEinsteinTrace,
      identityECScalarCurvature,
      identityECMinkowskiMetricCoordinate,
      identityECEtaSymmetricPart,
      identityECEtaAdjoint,
      minkowskiInternalSign,
      Fin.sum_univ_four]

private theorem fixedP506L0ContactCoframeHessian_timeRow
    (space : StageNineSpatialPoint)
    (column : LorentzianIndex) :
    (fixedP506L0ContactCoframeHessian space).1
        (coordinateDirection canonicalLorentzianTimeDirection)
        (coordinateDirection canonicalLorentzianTimeDirection)
        canonicalLorentzianTimeDirection column = 0 := by
  simpa [fixedP506L0ContactCoframeHessian,
    canonicalLorentzianTimeDirection,
    sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement,
    identityECTypedHolonomicCoframeHessianSection,
    identityECHolonomicCoframeHessianSection_coordinate] using
      identityECNormalCoframeHessianCoordinate_timeRow
        (sourceActionGeneratedIdentityECCoframeAccelerationRows
          positiveSmoothUnifiedSource (fixedCartanReactionContact space))
        column

private theorem fixedP506L0ContactCoframeHessian_timeColumn
    (space : StageNineSpatialPoint)
    (internal : LorentzianIndex) :
    (fixedP506L0ContactCoframeHessian space).1
        (coordinateDirection canonicalLorentzianTimeDirection)
        (coordinateDirection canonicalLorentzianTimeDirection)
        internal canonicalLorentzianTimeDirection = 0 := by
  simpa [fixedP506L0ContactCoframeHessian,
    canonicalLorentzianTimeDirection,
    sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement,
    identityECTypedHolonomicCoframeHessianSection,
    identityECHolonomicCoframeHessianSection_coordinate] using
      identityECNormalCoframeHessianCoordinate_timeColumn
        (sourceActionGeneratedIdentityECCoframeAccelerationRows
          positiveSmoothUnifiedSource (fixedCartanReactionContact space))
        internal

/-- The generated contact coframe is literally identity plus its canonical
quadratic holonomic Hessian realization. -/
theorem fixedIdentityECHessianCartanECNormalContactActual_coframe_eq_quadratic
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    (fixedIdentityECHessianCartanECNormalContactActual space).coframe point =
      1 + coframeHolonomicSecondJetQuadraticRealization
        (fixedP506L0ContactCoframeHessian space) point := by
  change
    (sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
      positiveSmoothUnifiedSource
      (fixedCartanReactionContact space)).coframe point = _
  simp [fixedP506L0ContactCoframeHessian,
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift,
    identityECHolonomicCoframeHessianIncrementLocalActualLift]

/-- Every later leg of the final common action write retains the recentered
KIN-16 coframe. -/
theorem fixedP506L0FinalCommonActionActual_coframe_eq_recenteredInput
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).coframe =
      (fixedP506L0RecenteredInput space).coframe := by
  rw [fixedP506L0FinalCommonActionActual_coframe]
  unfold recenteredCartanRepairedScalarSecondJetActual
  rw [installScalarQuadraticTimeCorrection_coframe,
    recenteredCartanRepairedConstitutiveCurrent_coframe_eq_cartan]
  unfold fixedP506L0CartanRestartActual
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe]

private theorem fixedP506L0RecenteredInput_coframe_eq_primitiveDiagonal
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    (fixedP506L0RecenteredInput space).coframe point =
      positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.coframe
        (canonicalSpatialContactTranslation space point) := by
  unfold fixedP506L0RecenteredInput
  change
    FixedP506FormNativeJointActionSolvedSuccessor.coframe
        (canonicalSpatialContactTranslation space point) = _
  rw [fixedP506FormNativeJointActionSolvedSuccessor_coframe,
    fixedP506JointActionSuccessor_coframe,
    fixedGlobalMatterDualP286Complete_coframe,
    fixedGlobalMatterDualFullCauchy_coframe,
    fixedGlobalFullCauchy_coframe]

/-- On the recentered canonical time axis, the final common coframe is the
same generated contact field whose Hessian was produced at that occurrence. -/
theorem fixedP506L0FinalCommonActionActual_coframe_timeAxis_eq_contact
    (space : StageNineSpatialPoint)
    (time : ℝ) :
    (fixedP506L0FinalCommonActionActual space).coframe
        (canonicalCauchySlicePoint time 0) =
      (fixedIdentityECHessianCartanECNormalContactActual space).coframe
        (canonicalCauchySlicePoint time 0) := by
  rw [fixedP506L0FinalCommonActionActual_coframe_eq_recenteredInput]
  rw [fixedP506L0RecenteredInput_coframe_eq_primitiveDiagonal]
  rw [canonicalSpatialContactTranslation_timeAxis]
  change
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState).coframe
        (canonicalCauchySlicePoint time space) = _
  simpa only [
      ← fixedIdentityECHessianCartanECNormalContactActual_eq_generated] using
    primitiveDiagonalActual_coframe_slice
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentFullSynchronizedCauchyState time space

/-- Componentwise explicit quadratic normal form of the final common
coframe on its recentered canonical time axis. -/
theorem fixedP506L0FinalCommonActionActual_coframe_timeAxis_normalForm
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (internal column : LorentzianIndex) :
    (fixedP506L0FinalCommonActionActual space).coframe
        (canonicalCauchySlicePoint time 0) internal column =
      (1 : LorentzianCoframe) internal column +
        time ^ 2 / 2 *
          (fixedP506L0ContactCoframeHessian space).1
            (coordinateDirection canonicalLorentzianTimeDirection)
            (coordinateDirection canonicalLorentzianTimeDirection)
            internal column := by
  rw [fixedP506L0FinalCommonActionActual_coframe_timeAxis_eq_contact,
    fixedIdentityECHessianCartanECNormalContactActual_coframe_eq_quadratic,
    fixedP506L0TimeAxisPoint]
  simp only [Matrix.add_apply,
    coframeHolonomicSecondJetQuadraticRealization_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [map_smul, map_smul]
  simp only [smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-! ## Time block and temporal principal -/

/-- The complete time row stays the identity row for every time. -/
theorem fixedP506L0FinalCommonActionActual_coframe_timeAxis_timeRow
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (column : LorentzianIndex) :
    (fixedP506L0FinalCommonActionActual space).coframe
        (canonicalCauchySlicePoint time 0)
        canonicalLorentzianTimeDirection column =
      (1 : LorentzianCoframe) canonicalLorentzianTimeDirection column := by
  rw [fixedP506L0FinalCommonActionActual_coframe_timeAxis_normalForm,
    fixedP506L0ContactCoframeHessian_timeRow]
  ring

/-- The complete time column stays the identity column for every time. -/
theorem fixedP506L0FinalCommonActionActual_coframe_timeAxis_timeColumn
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (internal : LorentzianIndex) :
    (fixedP506L0FinalCommonActionActual space).coframe
        (canonicalCauchySlicePoint time 0)
        internal canonicalLorentzianTimeDirection =
      (1 : LorentzianCoframe) internal canonicalLorentzianTimeDirection := by
  rw [fixedP506L0FinalCommonActionActual_coframe_timeAxis_normalForm,
    fixedP506L0ContactCoframeHessian_timeColumn]
  ring

private theorem fixedP506L0FinalCommonActionActual_coframe_timeAxis_timeRow_zero
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (column : LorentzianIndex) :
    (fixedP506L0FinalCommonActionActual space).coframe
        (canonicalCauchySlicePoint time 0) 0 column =
      (1 : LorentzianCoframe) 0 column := by
  have identityRow :=
    fixedP506L0FinalCommonActionActual_coframe_timeAxis_timeRow
      space time column
  unfold canonicalLorentzianTimeDirection at identityRow
  exact identityRow

/-! ## Exact determinant polynomial and canonical live domain -/

/-- The spatial block of the fixed final-common coframe on its recentered
time axis. -/
def fixedP506L0FinalCommonTimeAxisSpatialCoframe
    (space : StageNineSpatialPoint)
    (time : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun internal column =>
    (fixedP506L0FinalCommonActionActual space).coframe
      (canonicalCauchySlicePoint time 0) internal.succ column.succ

/-- The spatial block has the same literal quadratic normal form. -/
theorem fixedP506L0FinalCommonTimeAxisSpatialCoframe_normalForm
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (internal column : Fin 3) :
    fixedP506L0FinalCommonTimeAxisSpatialCoframe space time
        internal column =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) internal column +
        time ^ 2 / 2 *
          (fixedP506L0ContactCoframeHessian space).1
            (coordinateDirection canonicalLorentzianTimeDirection)
            (coordinateDirection canonicalLorentzianTimeDirection)
            internal.succ column.succ := by
  rw [fixedP506L0FinalCommonTimeAxisSpatialCoframe,
    fixedP506L0FinalCommonActionActual_coframe_timeAxis_normalForm]
  simp [Matrix.one_apply]

/-- The four-dimensional determinant is exactly the determinant of the
quadratic spatial block; the time direction contributes the unit block. -/
theorem fixedP506L0FinalCommonActionActual_coframe_timeAxis_det_eq_spatial
    (space : StageNineSpatialPoint)
    (time : ℝ) :
    Matrix.det
        ((fixedP506L0FinalCommonActionActual space).coframe
          (canonicalCauchySlicePoint time 0)) =
      Matrix.det
        (fixedP506L0FinalCommonTimeAxisSpatialCoframe space time) := by
  let coframe :=
    (fixedP506L0FinalCommonActionActual space).coframe
      (canonicalCauchySlicePoint time 0)
  have timeRow (column : LorentzianIndex) :
      coframe 0 column = (1 : LorentzianCoframe) 0 column := by
    exact
      fixedP506L0FinalCommonActionActual_coframe_timeAxis_timeRow_zero
        space time column
  change Matrix.det coframe = _
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  rw [timeRow 0, timeRow 1, timeRow 2, timeRow 3]
  simp
  rfl

/-- Polynomial matrix whose evaluation is the fixed final-common time-axis
coframe.  All coefficients are generated by the same fixed source/contact. -/
def fixedP506L0FinalCommonTimeAxisCoframePolynomialMatrix
    (space : StageNineSpatialPoint) :
    Matrix LorentzianIndex LorentzianIndex (Polynomial ℝ) :=
  fun internal column =>
    Polynomial.C ((1 : LorentzianCoframe) internal column) +
      Polynomial.C
          ((1 / 2 : ℝ) *
            (fixedP506L0ContactCoframeHessian space).1
              (coordinateDirection canonicalLorentzianTimeDirection)
              (coordinateDirection canonicalLorentzianTimeDirection)
              internal column) *
        Polynomial.X ^ 2

/-- Exact determinant polynomial of the fixed time-axis coframe. -/
def fixedP506L0FinalCommonTimeAxisDeterminantPolynomial
    (space : StageNineSpatialPoint) : Polynomial ℝ :=
  Matrix.det
    (fixedP506L0FinalCommonTimeAxisCoframePolynomialMatrix space)

/-- Evaluation of the source-generated determinant polynomial is the actual
coframe determinant, with no fitted coefficient or selected root. -/
theorem fixedP506L0FinalCommonTimeAxisDeterminantPolynomial_eval
    (space : StageNineSpatialPoint)
    (time : ℝ) :
    Polynomial.eval time
        (fixedP506L0FinalCommonTimeAxisDeterminantPolynomial space) =
      Matrix.det
        ((fixedP506L0FinalCommonActionActual space).coframe
          (canonicalCauchySlicePoint time 0)) := by
  calc
    Polynomial.eval time
        (fixedP506L0FinalCommonTimeAxisDeterminantPolynomial space) =
        Matrix.det
          ((Polynomial.evalRingHom time).mapMatrix
            (fixedP506L0FinalCommonTimeAxisCoframePolynomialMatrix space)) := by
      change
        (Polynomial.evalRingHom time)
            (Matrix.det
              (fixedP506L0FinalCommonTimeAxisCoframePolynomialMatrix space)) = _
      exact
        (Polynomial.evalRingHom time).map_det
          (fixedP506L0FinalCommonTimeAxisCoframePolynomialMatrix space)
    _ = _ := by
      congr 1
      ext internal column
      simp [fixedP506L0FinalCommonTimeAxisCoframePolynomialMatrix,
        fixedP506L0FinalCommonActionActual_coframe_timeAxis_normalForm]
      ring

/-- The exact real zero set of the generated determinant polynomial. -/
def fixedP506L0FinalCommonTimeAxisSingularSet
    (space : StageNineSpatialPoint) : Set ℝ :=
  { time |
    Polynomial.eval time
      (fixedP506L0FinalCommonTimeAxisDeterminantPolynomial space) = 0 }

theorem fixedP506L0FinalCommonTimeAxisSingularSet_eq_actualZeroSet
    (space : StageNineSpatialPoint) :
    fixedP506L0FinalCommonTimeAxisSingularSet space =
      { time |
        Matrix.det
          ((fixedP506L0FinalCommonActionActual space).coframe
            (canonicalCauchySlicePoint time 0)) = 0 } := by
  ext time
  simp [fixedP506L0FinalCommonTimeAxisSingularSet,
    fixedP506L0FinalCommonTimeAxisDeterminantPolynomial_eval]

/-- The canonical nondegenerate time domain is the connected component of
the exact determinant complement that contains the generated origin.  This
definition contains no chosen radius, endpoint, or branch receipt. -/
def fixedP506L0FinalCommonTimeAxisOriginDomain
    (space : StageNineSpatialPoint) : Set ℝ :=
  connectedComponentIn
    (fixedP506L0FinalCommonTimeAxisSingularSet space)ᶜ 0

theorem fixedP506L0FinalCommonActionActual_coframe_timeAxis_zero
    (space : StageNineSpatialPoint) :
    (fixedP506L0FinalCommonActionActual space).coframe
        (canonicalCauchySlicePoint 0 0) = 1 := by
  ext internal column
  simp [fixedP506L0FinalCommonActionActual_coframe_timeAxis_normalForm]

theorem fixedP506L0FinalCommonTimeAxis_origin_not_singular
    (space : StageNineSpatialPoint) :
    0 ∉ fixedP506L0FinalCommonTimeAxisSingularSet space := by
  rw [fixedP506L0FinalCommonTimeAxisSingularSet_eq_actualZeroSet]
  change
    Matrix.det
      ((fixedP506L0FinalCommonActionActual space).coframe
        (canonicalCauchySlicePoint 0 0)) ≠ 0
  rw [fixedP506L0FinalCommonActionActual_coframe_timeAxis_zero]
  norm_num

theorem fixedP506L0FinalCommonTimeAxis_zero_mem_originDomain
    (space : StageNineSpatialPoint) :
    0 ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space := by
  apply mem_connectedComponentIn
  exact fixedP506L0FinalCommonTimeAxis_origin_not_singular space

theorem fixedP506L0FinalCommonTimeAxisOriginDomain_connected
    (space : StageNineSpatialPoint) :
    IsConnected (fixedP506L0FinalCommonTimeAxisOriginDomain space) := by
  unfold fixedP506L0FinalCommonTimeAxisOriginDomain
  rw [isConnected_connectedComponentIn_iff]
  exact fixedP506L0FinalCommonTimeAxis_origin_not_singular space

theorem fixedP506L0FinalCommonTimeAxisOriginDomain_open
    (space : StageNineSpatialPoint) :
    IsOpen (fixedP506L0FinalCommonTimeAxisOriginDomain space) := by
  unfold fixedP506L0FinalCommonTimeAxisOriginDomain
  apply IsOpen.connectedComponentIn
  change IsOpen
    { time |
      Polynomial.eval time
          (fixedP506L0FinalCommonTimeAxisDeterminantPolynomial space) ≠
        0 }
  exact isOpen_ne_fun
    (fixedP506L0FinalCommonTimeAxisDeterminantPolynomial space).continuous
    continuous_const

/-- The canonical component is an actual neighborhood of the generated
origin, not merely a nonempty proof-selected subset. -/
theorem fixedP506L0FinalCommonTimeAxisOriginDomain_mem_nhds_zero
    (space : StageNineSpatialPoint) :
    fixedP506L0FinalCommonTimeAxisOriginDomain space ∈ nhds (0 : ℝ) :=
  (fixedP506L0FinalCommonTimeAxisOriginDomain_open space).mem_nhds
    (fixedP506L0FinalCommonTimeAxis_zero_mem_originDomain space)

theorem fixedP506L0FinalCommonTimeAxisOriginDomain_nondegenerate
    (space : StageNineSpatialPoint)
    {time : ℝ}
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    Matrix.det
        ((fixedP506L0FinalCommonActionActual space).coframe
          (canonicalCauchySlicePoint time 0)) ≠ 0 := by
  have outsideSingular :
      time ∈ (fixedP506L0FinalCommonTimeAxisSingularSet space)ᶜ :=
    connectedComponentIn_subset
      (fixedP506L0FinalCommonTimeAxisSingularSet space)ᶜ 0 inDomain
  rw [fixedP506L0FinalCommonTimeAxisSingularSet_eq_actualZeroSet] at outsideSingular
  simpa using outsideSingular

/-! ## Matter temporal principal on the canonical live domain -/

private theorem fixedP506L0FinalCommonTimeAxis_inverse_timeRow
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (nondegenerate :
      Matrix.det
        ((fixedP506L0FinalCommonActionActual space).coframe
          (canonicalCauchySlicePoint time 0)) ≠ 0)
    (internal : LorentzianIndex) :
    (((fixedP506L0FinalCommonActionActual space).coframe
          (canonicalCauchySlicePoint time 0))⁻¹)
        0 internal =
      (1 : LorentzianCoframe)
        0 internal := by
  let coframe :=
    (fixedP506L0FinalCommonActionActual space).coframe
      (canonicalCauchySlicePoint time 0)
  have determinantUnit : IsUnit (Matrix.det coframe) :=
    isUnit_iff_ne_zero.mpr nondegenerate
  have product := congrFun
    (congrFun (Matrix.mul_nonsing_inv coframe determinantUnit)
      0) internal
  have timeRow (column : LorentzianIndex) :
      coframe 0 column = (1 : LorentzianCoframe) 0 column := by
    exact
      fixedP506L0FinalCommonActionActual_coframe_timeAxis_timeRow_zero
        space time column
  simp only [Matrix.mul_apply, Fin.sum_univ_four] at product
  rw [timeRow 0, timeRow 1, timeRow 2, timeRow 3] at product
  dsimp [coframe] at product
  simpa [Matrix.one_apply] using product

private theorem fixedP506L0FinalCommonTimeAxis_inverseGamma_time
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (nondegenerate :
      Matrix.det
        ((fixedP506L0FinalCommonActionActual space).coframe
          (canonicalCauchySlicePoint time 0)) ≠ 0) :
    inverseCoframeDiracGamma
        { coframe :=
            (fixedP506L0FinalCommonActionActual space).coframe
              (canonicalCauchySlicePoint time 0),
          derivative := 0 }
        0 =
      diracGamma 0 := by
  unfold inverseCoframeDiracGamma
  simp_rw [fixedP506L0FinalCommonTimeAxis_inverse_timeRow
    space time nondegenerate]
  simp [Matrix.one_apply]

/-- On the canonical source-determined nondegenerate component, the actual
temporal matter principal is exactly the identity-coframe principal. -/
theorem fixedP506L0FinalCommonTimeAxis_matterTemporalPrincipal_eq_identity
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space)
    (matter : DiracExteriorMatterCarrier) :
    currentCoframeMatterTemporalPrincipal
        ((fixedP506L0FinalCommonActionActual space).coframe
          (canonicalCauchySlicePoint time 0)) matter =
      identityCoframeMatterTimePrincipal matter := by
  unfold currentCoframeMatterTemporalPrincipal
    identityCoframeMatterTimePrincipal
  simp only [LinearMap.smul_apply]
  rw [fixedP506L0FinalCommonTimeAxis_inverseGamma_time space time
    (fixedP506L0FinalCommonTimeAxisOriginDomain_nondegenerate
      space inDomain)]

theorem fixedP506L0FinalCommonTimeAxis_temporalPrincipalScalar_eq_one
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    coframeTemporalPrincipalScalar
        ((fixedP506L0FinalCommonActionActual space).coframe
          (canonicalCauchySlicePoint time 0)) = 1 := by
  unfold coframeTemporalPrincipalScalar
  simp_rw [fixedP506L0FinalCommonTimeAxis_inverse_timeRow space time
    (fixedP506L0FinalCommonTimeAxisOriginDomain_nondegenerate
      space inDomain)]
  norm_num [Fin.sum_univ_four, minkowskiInternalSign, Matrix.one_apply]

/-- The inverse temporal principal is the same involution on the same live
domain, so the matter evolution kernel needs no additional branch data. -/
theorem
    fixedP506L0FinalCommonTimeAxis_matterTemporalPrincipalInverse_eq_identity
    (space : StageNineSpatialPoint)
    (time : ℝ)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space)
    (matter : DiracExteriorMatterCarrier) :
    currentCoframeMatterTemporalPrincipalInverse
        ((fixedP506L0FinalCommonActionActual space).coframe
          (canonicalCauchySlicePoint time 0)) matter =
      identityCoframeMatterTimePrincipal matter := by
  unfold currentCoframeMatterTemporalPrincipalInverse
  rw [fixedP506L0FinalCommonTimeAxis_temporalPrincipalScalar_eq_one
    space time inDomain]
  simp only [Complex.ofReal_one, inv_one, one_smul]
  exact
    fixedP506L0FinalCommonTimeAxis_matterTemporalPrincipal_eq_identity
      space time inDomain matter


end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisCoframe
