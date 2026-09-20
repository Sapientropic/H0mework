import H0mework.Physics.Geometry.CanonicalTimePrimitiveSegmentRegularity

/-!
# Canonical temporal second-primitive diagonal Hessian

A smooth source/action profile is integrated twice along the fixed canonical
time foliation.  On the complete zero slice, the resulting ambient diagonal
Hessian reads the profile in the temporal direction and vanishes in all
spatial directions.

This is calculus for an already generated profile.  It accepts no residual,
target jet, branch, zero-fiber receipt, or completion payload.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCanonicalTimeSecondPrimitiveDiagonalHessian

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCanonicalTimePrimitiveSegmentRegularity
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDynamicBreakingVacuum
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineJointActionCanonicalPhasePathLaw
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

theorem canonicalTimeSecondPrimitive_contDiff_two_of_contDiff
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiff ℝ ∞ profile) :
    ContDiff ℝ 2 (canonicalTimeSecondPrimitive profile) := by
  rw [contDiff_iff_contDiffAt]
  intro point
  have finiteOrder : ((2 + 2 : ℕ) : ℕ∞ω) ≤ ∞ := by
    change (((2 + 2 : ℕ) : ℕ∞) : ℕ∞ω) ≤
      ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  exact canonicalTimeSecondPrimitive_contDiffAt_of_contDiffOn_segment_finite
    2 profile Set.univ isOpen_univ
    (regular.contDiffOn.of_le finiteOrder) point (by simp)

private theorem canonicalSlice_timeLine_continuous
    (space : StageNineSpatialPoint) :
    Continuous fun candidateTime =>
      canonicalCauchySlicePoint candidateTime space := by
  rw [show (fun candidateTime => canonicalCauchySlicePoint candidateTime space) =
      fun candidateTime =>
        candidateTime • coordinateDirection canonicalLorentzianTimeDirection +
          canonicalSpatialInclusion space by
    funext candidateTime
    rw [canonicalCauchySlicePoint_eq_const_add_inclusion]
    ext direction
    fin_cases direction <;>
      simp [coordinateDirection, canonicalLorentzianTimeDirection]]
  fun_prop

private theorem field_affineDirectionLine_hasDerivAt
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (field : BasePoint → E)
    (point : BasePoint)
    (direction : LorentzianIndex)
    (differentiable : DifferentiableAt ℝ field point) :
    NormedHasDerivAt
      (fun parameter =>
        field (point + parameter • coordinateDirection direction))
      (fieldDirectionalDerivative field point direction) 0 := by
  have differentiableAtLine : DifferentiableAt ℝ field
      (point + (0 : ℝ) • coordinateDirection direction) := by
    simpa using differentiable
  have composed :=
    differentiableAtLine.hasFDerivAt.comp_hasDerivAt 0
      (hasDerivAt_const_add_time_smul point
        (coordinateDirection direction) 0)
  simpa [fieldDirectionalDerivative, Function.comp_def] using composed

private theorem canonicalSecondPrimitive_temporalFirstDerivative
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiff ℝ ∞ profile)
    (space : StageNineSpatialPoint)
    (time : ℝ) :
    fieldDirectionalDerivative (canonicalTimeSecondPrimitive profile)
        (canonicalCauchySlicePoint time space)
        canonicalLorentzianTimeDirection =
      canonicalTimePrimitive profile
        (canonicalCauchySlicePoint time space) := by
  let primitive := canonicalTimeSecondPrimitive profile
  have primitiveDifferentiable : DifferentiableAt ℝ primitive
      (canonicalCauchySlicePoint time space) :=
    (canonicalTimeSecondPrimitive_contDiff_two_of_contDiff profile regular).differentiable
      (by norm_num) |>.differentiableAt
  have ambient := field_timeLine_hasDerivAt primitive space time
    primitiveDifferentiable
  have lineContinuous : Continuous fun candidateTime =>
      profile (canonicalCauchySlicePoint candidateTime space) :=
    regular.continuous.comp (canonicalSlice_timeLine_continuous space)
  have action := canonicalTimeSecondPrimitive_timeLine_hasDerivAt
    profile space time lineContinuous
  exact ambient.unique action

private theorem canonicalSecondPrimitive_spatialFirstDerivative_zero
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiff ℝ ∞ profile)
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex)
    (directionNe : direction ≠ canonicalLorentzianTimeDirection)
    (parameter : ℝ) :
    fieldDirectionalDerivative (canonicalTimeSecondPrimitive profile)
        (canonicalCauchySlicePoint 0 space +
          parameter • coordinateDirection direction) direction = 0 := by
  let point := canonicalCauchySlicePoint 0 space +
    parameter • coordinateDirection direction
  let line := fun increment : ℝ =>
    point + increment • coordinateDirection direction
  have timeProjectionZero (increment : ℝ) :
      canonicalTimeProjection (line increment) = 0 := by
    have zeroNe : (0 : LorentzianIndex) ≠ direction := by
      simpa [canonicalLorentzianTimeDirection] using Ne.symm directionNe
    unfold line point canonicalTimeProjection
    simp [canonicalCauchySlicePoint, coordinateDirection,
      canonicalLorentzianTimeDirection, zeroNe]
  have lineZero : (fun increment =>
      canonicalTimeSecondPrimitive profile (line increment)) =
      fun _ : ℝ => (0 : E) := by
    funext increment
    unfold canonicalTimeSecondPrimitive
    rw [timeProjectionZero]
    simp
  have primitiveDifferentiable : DifferentiableAt ℝ
      (canonicalTimeSecondPrimitive profile) point :=
    (canonicalTimeSecondPrimitive_contDiff_two_of_contDiff profile regular).differentiable
      (by norm_num) |>.differentiableAt
  have ambient := field_affineDirectionLine_hasDerivAt
    (canonicalTimeSecondPrimitive profile) point direction
    primitiveDifferentiable
  have zeroDerivative : HasDerivAt (fun _ : ℝ => (0 : E))
      (0 : E) (0 : ℝ) := by
    simpa using (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : E)))
  have lineDerivative : HasDerivAt (fun increment =>
      canonicalTimeSecondPrimitive profile (line increment)) 0 0 := by
    rw [lineZero]
    exact zeroDerivative
  exact ambient.unique lineDerivative

/-- The canonical twice-integrated profile has zero complete first germ on
the distinguished zero slice.  This is the finite-dimensional companion to
the diagonal Hessian readout below. -/
theorem canonicalTimeSecondPrimitive_hasFDerivAt_zeroSlice_of_contDiff
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiff ℝ ∞ profile)
    (space : StageNineSpatialPoint) :
    HasFDerivAt (canonicalTimeSecondPrimitive profile)
      (0 : BasePoint →L[ℝ] E) (canonicalCauchySlicePoint 0 space) := by
  let primitive := canonicalTimeSecondPrimitive profile
  let point := canonicalCauchySlicePoint 0 space
  have primitiveDifferentiable : DifferentiableAt ℝ primitive point :=
    (canonicalTimeSecondPrimitive_contDiff_two_of_contDiff profile regular
      ).differentiable (by norm_num) |>.differentiableAt
  have derivativeZero : fderiv ℝ primitive point = 0 := by
    apply ContinuousLinearMap.ext
    intro tangent
    have tangentExpansion :
        tangent = ∑ direction : LorentzianIndex,
          tangent direction • coordinateDirection direction := by
      ext direction
      fin_cases direction <;>
        simp [coordinateDirection, Fin.sum_univ_four]
    rw [tangentExpansion, map_sum]
    apply Finset.sum_eq_zero
    intro direction _
    rw [map_smul]
    suffices fieldDirectionalDerivative primitive point direction = 0 by
      simpa [fieldDirectionalDerivative] using congrArg (tangent direction • ·) this
    by_cases temporal : direction = canonicalLorentzianTimeDirection
    · subst direction
      simpa [primitive, point] using
        canonicalSecondPrimitive_temporalFirstDerivative
          profile regular space 0
    · simpa [primitive, point] using
        canonicalSecondPrimitive_spatialFirstDerivative_zero
          profile regular space direction temporal 0
  exact primitiveDifferentiable.hasFDerivAt.congr_fderiv derivativeZero

private theorem mixedFieldDirectionalDerivative_comm_of_contDiff_two
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (field : BasePoint → E)
    (regular : ContDiff ℝ 2 field)
    (point : BasePoint)
    (first second : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate => fieldDirectionalDerivative field candidate first)
        point second =
      fieldDirectionalDerivative
        (fun candidate => fieldDirectionalDerivative field candidate second)
        point first := by
  have derivativeRegular : ContDiff ℝ 1 (fderiv ℝ field) :=
    regular.fderiv_right (m := 1) (by norm_num)
  have derivativeDifferentiable :
      DifferentiableAt ℝ (fderiv ℝ field) point :=
    (derivativeRegular.differentiable (by norm_num)).differentiableAt
  have evaluatedSecondDerivative (inner outer : LorentzianIndex) :
      fderiv ℝ
          (fun candidate =>
            fderiv ℝ field candidate (coordinateDirection inner))
          point (coordinateDirection outer) =
        fderiv ℝ (fderiv ℝ field) point
          (coordinateDirection outer) (coordinateDirection inner) := by
    let evaluation : (BasePoint →L[ℝ] E) →L[ℝ] E :=
      ContinuousLinearMap.apply ℝ E (coordinateDirection inner)
    have evaluated : HasFDerivAt
        (fun candidate => evaluation (fderiv ℝ field candidate))
        (evaluation.comp (fderiv ℝ (fderiv ℝ field) point)) point :=
      evaluation.hasFDerivAt.comp point derivativeDifferentiable.hasFDerivAt
    exact congrArg
      (fun derivative : BasePoint →L[ℝ] E =>
        derivative (coordinateDirection outer)) evaluated.fderiv
  have symmetricSecond : IsSymmSndFDerivAt ℝ field point :=
    regular.contDiffAt.isSymmSndFDerivAt (by
      simp)
  unfold fieldDirectionalDerivative
  calc
    fderiv ℝ
        (fun candidate =>
          fderiv ℝ field candidate (coordinateDirection first))
        point (coordinateDirection second) =
      fderiv ℝ (fderiv ℝ field) point
        (coordinateDirection second) (coordinateDirection first) :=
      evaluatedSecondDerivative first second
    _ = fderiv ℝ (fderiv ℝ field) point
        (coordinateDirection first) (coordinateDirection second) :=
      symmetricSecond.eq
        (coordinateDirection second) (coordinateDirection first)
    _ = fderiv ℝ
        (fun candidate =>
          fderiv ℝ field candidate (coordinateDirection second))
        point (coordinateDirection first) :=
      (evaluatedSecondDerivative second first).symm

private theorem
    canonicalSecondPrimitive_temporalFirstJet_spatialDerivative_zero
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiff ℝ ∞ profile)
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex)
    (directionNe : direction ≠ canonicalLorentzianTimeDirection) :
    fieldDirectionalDerivative
        (fun point => fieldDirectionalDerivative
          (canonicalTimeSecondPrimitive profile) point
          canonicalLorentzianTimeDirection)
        (canonicalCauchySlicePoint 0 space) direction = 0 := by
  let primitive := canonicalTimeSecondPrimitive profile
  let point := canonicalCauchySlicePoint 0 space
  let firstJet := fun candidate => fieldDirectionalDerivative primitive candidate
    canonicalLorentzianTimeDirection
  have primitiveRegular : ContDiff ℝ 2 primitive :=
    canonicalTimeSecondPrimitive_contDiff_two_of_contDiff profile regular
  have firstJetRegular : ContDiff ℝ 1 firstJet := by
    unfold firstJet fieldDirectionalDerivative
    exact (primitiveRegular.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiff_const
  have ambient := field_affineDirectionLine_hasDerivAt firstJet point direction
    ((firstJetRegular.differentiable (by norm_num)).differentiableAt)
  have lineZero :
      (fun parameter =>
        firstJet (point + parameter • coordinateDirection direction)) =
        fun _ : ℝ => (0 : E) := by
    funext parameter
    let shifted := point + parameter • coordinateDirection direction
    have zeroNe : (0 : LorentzianIndex) ≠ direction := by
      simpa [canonicalLorentzianTimeDirection] using Ne.symm directionNe
    have timeZero : canonicalTimeProjection shifted = 0 := by
      unfold shifted point canonicalTimeProjection
      simp [canonicalCauchySlicePoint, coordinateDirection,
        canonicalLorentzianTimeDirection, zeroNe]
    have reconstruct : shifted =
        canonicalCauchySlicePoint 0 (canonicalSpatialProjection shifted) := by
      calc
        shifted = canonicalCauchySlicePoint
            (canonicalTimeProjection shifted)
            (canonicalSpatialProjection shifted) :=
          (canonicalCauchySlicePoint_projections shifted).symm
        _ = canonicalCauchySlicePoint 0
            (canonicalSpatialProjection shifted) := by rw [timeZero]
    change fieldDirectionalDerivative primitive shifted
      canonicalLorentzianTimeDirection = 0
    rw [reconstruct,
      canonicalSecondPrimitive_temporalFirstDerivative profile regular]
    simp
  have lineDerivative : HasDerivAt
      (fun parameter =>
        firstJet (point + parameter • coordinateDirection direction))
      (0 : E) (0 : ℝ) := by
    simpa only [lineZero] using
      (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : E)))
  simpa [firstJet, point, primitive] using ambient.unique lineDerivative

private theorem
    canonicalSecondPrimitive_spatialFirstJet_spatialDerivative_zero
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiff ℝ ∞ profile)
    (space : StageNineSpatialPoint)
    (inner outer : LorentzianIndex)
    (innerNe : inner ≠ canonicalLorentzianTimeDirection)
    (outerNe : outer ≠ canonicalLorentzianTimeDirection) :
    fieldDirectionalDerivative
        (fun point => fieldDirectionalDerivative
          (canonicalTimeSecondPrimitive profile) point inner)
        (canonicalCauchySlicePoint 0 space) outer = 0 := by
  let primitive := canonicalTimeSecondPrimitive profile
  let point := canonicalCauchySlicePoint 0 space
  let firstJet := fun candidate => fieldDirectionalDerivative primitive candidate
    inner
  have primitiveRegular : ContDiff ℝ 2 primitive :=
    canonicalTimeSecondPrimitive_contDiff_two_of_contDiff profile regular
  have firstJetRegular : ContDiff ℝ 1 firstJet := by
    unfold firstJet fieldDirectionalDerivative
    exact (primitiveRegular.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiff_const
  have ambient := field_affineDirectionLine_hasDerivAt firstJet point outer
    ((firstJetRegular.differentiable (by norm_num)).differentiableAt)
  have lineZero :
      (fun parameter =>
        firstJet (point + parameter • coordinateDirection outer)) =
        fun _ : ℝ => (0 : E) := by
    funext parameter
    let shifted := point + parameter • coordinateDirection outer
    have zeroNe : (0 : LorentzianIndex) ≠ outer := by
      simpa [canonicalLorentzianTimeDirection] using Ne.symm outerNe
    have timeZero : canonicalTimeProjection shifted = 0 := by
      unfold shifted point canonicalTimeProjection
      simp [canonicalCauchySlicePoint, coordinateDirection,
        canonicalLorentzianTimeDirection, zeroNe]
    have reconstruct : shifted =
        canonicalCauchySlicePoint 0 (canonicalSpatialProjection shifted) := by
      calc
        shifted = canonicalCauchySlicePoint
            (canonicalTimeProjection shifted)
            (canonicalSpatialProjection shifted) :=
          (canonicalCauchySlicePoint_projections shifted).symm
        _ = canonicalCauchySlicePoint 0
            (canonicalSpatialProjection shifted) := by rw [timeZero]
    change fieldDirectionalDerivative primitive shifted inner = 0
    rw [reconstruct]
    simpa [primitive] using
      canonicalSecondPrimitive_spatialFirstDerivative_zero
        profile regular (canonicalSpatialProjection shifted) inner innerNe 0
  have lineDerivative : HasDerivAt
      (fun parameter =>
        firstJet (point + parameter • coordinateDirection outer))
      (0 : E) (0 : ℝ) := by
    simpa only [lineZero] using
      (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : E)))
  simpa [firstJet, point, primitive] using ambient.unique lineDerivative

/-- Along every spatial fibre, the canonical twice-integrated profile has
the source profile as its exact second time derivative.  This is the
all-time form of the zero-slice Hessian readout below; no equation or target
field is supplied to the primitive. -/
theorem canonicalTimeSecondPrimitive_temporalSecondDerivative_of_contDiff
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiff ℝ ∞ profile)
    (time : ℝ)
    (space : StageNineSpatialPoint) :
    fieldDirectionalDerivative
        (fun point => fieldDirectionalDerivative
          (canonicalTimeSecondPrimitive profile) point
          canonicalLorentzianTimeDirection)
        (canonicalCauchySlicePoint time space)
        canonicalLorentzianTimeDirection =
      profile (canonicalCauchySlicePoint time space) := by
  let primitive := canonicalTimeSecondPrimitive profile
  have primitiveRegular : ContDiff ℝ 2 primitive :=
    canonicalTimeSecondPrimitive_contDiff_two_of_contDiff profile regular
  let firstJet := fun point =>
    fieldDirectionalDerivative primitive point
      canonicalLorentzianTimeDirection
  have firstJetRegular : ContDiff ℝ 1 firstJet := by
    unfold firstJet fieldDirectionalDerivative
    exact (primitiveRegular.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiff_const
  have ambient := field_timeLine_hasDerivAt firstJet space time
    ((firstJetRegular.differentiable (by norm_num)).differentiableAt)
  have lineEquality :
      (fun candidateTime =>
        firstJet (canonicalCauchySlicePoint candidateTime space)) =
        fun candidateTime => canonicalTimePrimitive profile
          (canonicalCauchySlicePoint candidateTime space) := by
    funext candidateTime
    exact canonicalSecondPrimitive_temporalFirstDerivative
      profile regular space candidateTime
  have lineContinuous : Continuous fun candidateTime =>
      profile (canonicalCauchySlicePoint candidateTime space) :=
    regular.continuous.comp (canonicalSlice_timeLine_continuous space)
  have action := canonicalTimePrimitive_timeLine_hasDerivAt
    profile space time lineContinuous
  have lineDerivative : HasDerivAt
      (fun candidateTime =>
        firstJet (canonicalCauchySlicePoint candidateTime space))
      (profile (canonicalCauchySlicePoint time space)) time := by
    rw [lineEquality]
    exact action
  simpa [firstJet, primitive] using ambient.unique lineDerivative

/-- Exact diagonal Hessian of the canonical twice-integrated action profile
on the full zero slice.  The theorem is a readout of the source-free
primitive and does not select the profile or any downstream update. -/
theorem canonicalTimeSecondPrimitive_diagonalSecondDerivative_zeroSlice_of_contDiff
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiff ℝ ∞ profile)
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => fieldDirectionalDerivative
          (canonicalTimeSecondPrimitive profile) point direction)
        (canonicalCauchySlicePoint 0 space) direction =
      if direction = canonicalLorentzianTimeDirection then
        profile (canonicalCauchySlicePoint 0 space)
      else 0 := by
  let primitive := canonicalTimeSecondPrimitive profile
  have primitiveRegular : ContDiff ℝ 2 primitive :=
    canonicalTimeSecondPrimitive_contDiff_two_of_contDiff profile regular
  have firstJetRegular : ContDiff ℝ 1 fun point =>
      fieldDirectionalDerivative primitive point direction := by
    unfold fieldDirectionalDerivative
    exact ((primitiveRegular.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiff_const)
  by_cases temporal : direction = canonicalLorentzianTimeDirection
  · subst direction
    let firstJet := fun point =>
      fieldDirectionalDerivative primitive point
        canonicalLorentzianTimeDirection
    have ambient := field_timeLine_hasDerivAt firstJet space 0
      ((firstJetRegular.differentiable (by norm_num)).differentiableAt)
    have lineEquality : (fun time =>
        firstJet (canonicalCauchySlicePoint time space)) =
        fun time => canonicalTimePrimitive profile
          (canonicalCauchySlicePoint time space) := by
      funext time
      exact canonicalSecondPrimitive_temporalFirstDerivative
        profile regular space time
    have lineContinuous : Continuous fun candidateTime =>
        profile (canonicalCauchySlicePoint candidateTime space) :=
      regular.continuous.comp (canonicalSlice_timeLine_continuous space)
    have action := canonicalTimePrimitive_timeLine_hasDerivAt
      profile space 0 lineContinuous
    have lineDerivative : HasDerivAt (fun time =>
        firstJet (canonicalCauchySlicePoint time space))
        (profile (canonicalCauchySlicePoint 0 space)) 0 := by
      rw [lineEquality]
      exact action
    simpa [firstJet, primitive] using ambient.unique lineDerivative
  · let point := canonicalCauchySlicePoint 0 space
    let firstJet := fun candidate =>
      fieldDirectionalDerivative primitive candidate direction
    have ambient := field_affineDirectionLine_hasDerivAt firstJet point
      direction
      ((firstJetRegular.differentiable (by norm_num)).differentiableAt)
    have lineEquality : (fun parameter =>
        firstJet (point + parameter • coordinateDirection direction)) =
        fun _ : ℝ => (0 : E) := by
      funext parameter
      exact canonicalSecondPrimitive_spatialFirstDerivative_zero
        profile regular space direction temporal parameter
    have lineDerivative : HasDerivAt (fun parameter =>
        firstJet (point + parameter • coordinateDirection direction))
        (0 : E) (0 : ℝ) := by
      have zeroDerivative :=
        (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : E)))
      rw [← lineEquality] at zeroDerivative
      exact zeroDerivative
    simpa [firstJet, point, primitive, temporal] using
      ambient.unique lineDerivative

/-- Full coordinate Hessian of the canonical twice-integrated profile on the
zero slice.  Its sole support is the time--time coordinate. -/
theorem canonicalTimeSecondPrimitive_mixedSecondDerivative_zeroSlice_of_contDiff
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiff ℝ ∞ profile)
    (space : StageNineSpatialPoint)
    (inner outer : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point => fieldDirectionalDerivative
          (canonicalTimeSecondPrimitive profile) point inner)
        (canonicalCauchySlicePoint 0 space) outer =
      if inner = canonicalLorentzianTimeDirection ∧
          outer = canonicalLorentzianTimeDirection then
        profile (canonicalCauchySlicePoint 0 space)
      else 0 := by
  by_cases innerTemporal : inner = canonicalLorentzianTimeDirection
  · subst inner
    by_cases outerTemporal : outer = canonicalLorentzianTimeDirection
    · subst outer
      simpa using
        canonicalTimeSecondPrimitive_diagonalSecondDerivative_zeroSlice_of_contDiff
          profile regular space canonicalLorentzianTimeDirection
    · simpa [outerTemporal] using
        canonicalSecondPrimitive_temporalFirstJet_spatialDerivative_zero
          profile regular space outer outerTemporal
  · by_cases outerTemporal : outer = canonicalLorentzianTimeDirection
    · subst outer
      rw [mixedFieldDirectionalDerivative_comm_of_contDiff_two
        (canonicalTimeSecondPrimitive profile)
        (canonicalTimeSecondPrimitive_contDiff_two_of_contDiff profile regular)
        (canonicalCauchySlicePoint 0 space) inner
        canonicalLorentzianTimeDirection]
      simpa [innerTemporal] using
        canonicalSecondPrimitive_temporalFirstJet_spatialDerivative_zero
          profile regular space inner innerTemporal
    · simpa [innerTemporal, outerTemporal] using
        canonicalSecondPrimitive_spatialFirstJet_spatialDerivative_zero
          profile regular space inner outer innerTemporal outerTemporal

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCanonicalTimeSecondPrimitiveDiagonalHessian
