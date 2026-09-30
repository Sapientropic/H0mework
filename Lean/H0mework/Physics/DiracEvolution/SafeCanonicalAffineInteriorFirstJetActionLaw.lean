import H0mework.Physics.DiracEvolution.SafeCanonicalAffineEssentialBound

namespace SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineInteriorFirstJetActionLaw

open MeasureTheory Set
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGreenRateL2Read
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyEstimate
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakGalerkinEnergy
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineEssentialBound
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffinePhysicalGreenEquation
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineTailEnergyActionLaw
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineTailEnergyCenter
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterSameSourceGalerkinFamily
open StageNineHolonomicField
open StageNineP286ActionVelocityLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open scoped ComplexOrder ENNReal Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

local instance probeMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

def interiorSpacetimeTest
    {a b : DiracMatterSpatialCoordinates}
    (test : CauchySafeMatterCanonicalInteriorSmoothTest a b) :
    BasePoint → MatterCoordinateCarrier :=
  fun point ↦ test.1.1
    ((EuclideanSpace.equiv (Fin 3) ℝ) (canonicalSpatialProjection point))

theorem interiorSpacetimeTest_contDiff_one
    {a b : DiracMatterSpatialCoordinates}
    (test : CauchySafeMatterCanonicalInteriorSmoothTest a b) :
    ContDiff ℝ 1 (interiorSpacetimeTest test) := by
  exact (test.1.property.2.of_le (by norm_num)).comp
    ((EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearEquiv.contDiff.comp
      canonicalSpatialProjection.contDiff)

@[simp] private theorem interiorSpacetimeTest_slice
    {a b : DiracMatterSpatialCoordinates}
    (test : CauchySafeMatterCanonicalInteriorSmoothTest a b)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    interiorSpacetimeTest test
        (diracMatterSpacetimeCoordinatePoint time space) = test.1.1 space := by
  simp only [interiorSpacetimeTest, diracMatterSpacetimeCoordinatePoint,
    canonicalSpatialProjection_slice]
  exact congrArg test.1.1
    ((EuclideanSpace.equiv (Fin 3) ℝ).apply_symm_apply space)

private theorem spatialProjection_coordinateSpatial (direction : Fin 3) :
    (EuclideanSpace.equiv (Fin 3) ℝ)
        (canonicalSpatialProjection (coordinateDirection direction.succ)) =
      Pi.single direction 1 := by
  funext coordinate
  fin_cases direction <;> fin_cases coordinate <;>
    simp [canonicalSpatialProjection, coordinateDirection,
      localBaseCoordinate_apply]

private theorem interiorSpacetimeTest_spatialDerivative_slice
    {a b : DiracMatterSpatialCoordinates}
    (test : CauchySafeMatterCanonicalInteriorSmoothTest a b)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (direction : Fin 3) :
    fieldDirectionalDerivative (interiorSpacetimeTest test)
        (diracMatterSpacetimeCoordinatePoint time space) direction.succ =
      (cauchySafeMatterCanonicalInteriorSmoothTestDerivative test direction).1
        space := by
  let spatialMap : BasePoint →L[ℝ] DiracMatterSpatialCoordinates :=
    (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearEquiv.toContinuousLinearMap.comp
      canonicalSpatialProjection
  have spatialValue : spatialMap
      (diracMatterSpacetimeCoordinatePoint time space) = space := by
    change (EuclideanSpace.equiv (Fin 3) ℝ)
      (canonicalSpatialProjection
        (diracMatterSpacetimeCoordinatePoint time space)) = space
    rw [diracMatterSpacetimeCoordinatePoint,
      canonicalSpatialProjection_slice]
    exact (EuclideanSpace.equiv (Fin 3) ℝ).apply_symm_apply space
  have testDifferentiable : DifferentiableAt ℝ test.1.1 space :=
    (test.1.property.2.differentiable (by norm_num)).differentiableAt
  have testDifferentiableAtMap : DifferentiableAt ℝ test.1.1
      (spatialMap (diracMatterSpacetimeCoordinatePoint time space)) := by
    rw [spatialValue]
    exact testDifferentiable
  have composed := testDifferentiableAtMap.hasFDerivAt.comp
    (diracMatterSpacetimeCoordinatePoint time space) spatialMap.hasFDerivAt
  change fderiv ℝ (test.1.1 ∘ spatialMap)
      (diracMatterSpacetimeCoordinatePoint time space)
        (coordinateDirection direction.succ) =
    fderiv ℝ test.1.1 space (Pi.single direction 1)
  rw [composed.fderiv, ContinuousLinearMap.comp_apply, spatialValue]
  congr 1
  exact spatialProjection_coordinateSpatial direction

private def spatialFirstJetValueInjection :
    MatterCoordinateCarrier →L[ℝ] CauchySafeMatterSpatialFirstJetFiber :=
  ContinuousLinearMap.inl ℝ MatterCoordinateCarrier
    (WithLp 2 (Fin 3 → MatterCoordinateCarrier))

private def spatialFirstJetDerivativeInjection (direction : Fin 3) :
    MatterCoordinateCarrier →L[ℝ] CauchySafeMatterSpatialFirstJetFiber := by
  let linear : MatterCoordinateCarrier →ₗ[ℝ]
      CauchySafeMatterSpatialFirstJetFiber :=
    { toFun := fun value ↦
        (0, WithLp.toLp 2 (Pi.single direction value))
      map_add' := by
        intro first second
        apply Prod.ext
        · simp
        · exact PiLp.single_add 2 direction
      map_smul' := by
        intro parameter value
        apply Prod.ext
        · simp
        · apply PiLp.ext
          intro index
          simp [PiLp.single_apply, Pi.single_apply, smul_ite] }
  exact ⟨linear, linear.continuous_of_finiteDimensional⟩

private theorem spatialFirstJetDerivativeInjection_sum
    (derivative : Fin 3 → MatterCoordinateCarrier) :
    (∑ direction : Fin 3,
        spatialFirstJetDerivativeInjection direction
          (derivative direction)) =
      (0, WithLp.toLp 2 derivative) := by
  apply Prod.ext
  · rw [Fin.sum_univ_three]
    change (0 + 0 + 0 : MatterCoordinateCarrier) = 0
    simp
  · apply PiLp.ext
    intro direction
    fin_cases direction <;>
      simp [spatialFirstJetDerivativeInjection, Fin.sum_univ_three]

private def packCanonicalInteriorFirstJetL2
    (a b : DiracMatterSpatialCoordinates) :
    CauchySafeMatterCanonicalInteriorFirstJetL2 a b →L[ℝ]
      Lp CauchySafeMatterSpatialFirstJetFiber 2
        (volume.restrict (Icc a b)) :=
  ((spatialFirstJetValueInjection.compLpL 2
      (volume.restrict (Icc a b))).comp
    (ContinuousLinearMap.fst ℝ
      (CauchySafeMatterSpatialL2 a b)
      (Fin 3 → CauchySafeMatterSpatialL2 a b))) +
    ∑ direction : Fin 3,
      ((spatialFirstJetDerivativeInjection direction).compLpL 2
          (volume.restrict (Icc a b))).comp
        ((ContinuousLinearMap.proj direction).comp
          (ContinuousLinearMap.snd ℝ
            (CauchySafeMatterSpatialL2 a b)
            (Fin 3 → CauchySafeMatterSpatialL2 a b)))

private theorem packCanonicalInteriorFirstJetL2_coe_ae
    {a b : DiracMatterSpatialCoordinates}
    (test : CauchySafeMatterCanonicalInteriorSmoothTest a b) :
    packCanonicalInteriorFirstJetL2 a b
        (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test) =ᵐ[
          volume.restrict (Icc a b)]
      fun space ↦
        (test.1.1 space,
          WithLp.toLp 2 fun direction ↦
            (cauchySafeMatterCanonicalInteriorSmoothTestDerivative
              test direction).1 space) := by
  let valueL2 := cauchySafeMatterSmoothCompactTestToL2 a b test.1
  let derivativeL2 (direction : Fin 3) :=
    cauchySafeMatterSmoothCompactTestToL2 a b
      (cauchySafeMatterCanonicalInteriorSmoothTestDerivative test direction)
  have valueInput : valueL2 =ᵐ[volume.restrict (Icc a b)] test.1.1 :=
    (cauchySafeMatterSmoothCompactTest_memLp a b test.1).coeFn_toLp
  have derivativeInput : ∀ᶠ space in ae (volume.restrict (Icc a b)),
      ∀ direction, derivativeL2 direction space =
        (cauchySafeMatterCanonicalInteriorSmoothTestDerivative
          test direction).1 space := by
    rw [Filter.eventually_all]
    intro direction
    exact (cauchySafeMatterSmoothCompactTest_memLp a b
      (cauchySafeMatterCanonicalInteriorSmoothTestDerivative
        test direction)).coeFn_toLp
  have valueLift := spatialFirstJetValueInjection.coeFn_compLp
    (p := (2 : ℝ≥0∞)) valueL2
  have derivativeLift : ∀ᶠ space in ae (volume.restrict (Icc a b)),
      ∀ direction,
        ((spatialFirstJetDerivativeInjection direction).compLp
          (derivativeL2 direction)) space =
        spatialFirstJetDerivativeInjection direction
          (derivativeL2 direction space) := by
    rw [Filter.eventually_all]
    intro direction
    exact (spatialFirstJetDerivativeInjection direction).coeFn_compLp
      (derivativeL2 direction)
  have derivativeSum := Lp.coeFn_finsetSum Finset.univ
    (fun direction ↦
      (spatialFirstJetDerivativeInjection direction).compLp
        (derivativeL2 direction))
  have totalSum := Lp.coeFn_add
    (spatialFirstJetValueInjection.compLp valueL2)
    (∑ direction : Fin 3,
      (spatialFirstJetDerivativeInjection direction).compLp
        (derivativeL2 direction))
  filter_upwards [valueInput, derivativeInput, valueLift, derivativeLift,
    derivativeSum, totalSum] with space valueEq derivativeEq valueLiftEq
      derivativeLiftEq derivativeSumEq totalSumEq
  rw [show packCanonicalInteriorFirstJetL2 a b
      (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test) =
        spatialFirstJetValueInjection.compLp valueL2 +
          ∑ direction : Fin 3,
            (spatialFirstJetDerivativeInjection direction).compLp
              (derivativeL2 direction) by
      rfl]
  rw [totalSumEq]
  change (spatialFirstJetValueInjection.compLp valueL2) space +
      ((∑ direction : Fin 3,
        (spatialFirstJetDerivativeInjection direction).compLp
          (derivativeL2 direction)) :
        Lp CauchySafeMatterSpatialFirstJetFiber 2
          (volume.restrict (Icc a b))) space = _
  rw [valueLiftEq, valueEq, derivativeSumEq]
  change spatialFirstJetValueInjection (test.1.1 space) +
      ∑ direction : Fin 3,
        ((spatialFirstJetDerivativeInjection direction).compLp
          (derivativeL2 direction)) space = _
  simp_rw [derivativeLiftEq, derivativeEq]
  rw [spatialFirstJetDerivativeInjection_sum]
  simp [spatialFirstJetValueInjection]

private def greenRateSpatialFirstJetRieszFiberRead
    (point : ℝ × DiracMatterSpatialCoordinates) :
    CauchySafeMatterSpatialFirstJetFiber →L[ℝ] MatterCoordinateCarrier :=
  (InnerProductSpace.toDual ℝ MatterCoordinateCarrier).symm.toContinuousLinearMap.comp
    (fixedP506L0CauchySafeMatterGreenRateSpatialFirstJetFiberRead point)

private def greenRateSpatialFirstJetEvaluation :
    (CauchySafeMatterSpatialFirstJetFiber →L[ℝ] MatterCoordinateCarrier) →L[ℝ]
      CauchySafeMatterSpatialFirstJetFiber →L[ℝ] MatterCoordinateCarrier :=
  isBoundedBilinearMap_apply.toContinuousLinearMap

private theorem greenRateSpatialFirstJetRieszFiberRead_continuous :
    Continuous greenRateSpatialFirstJetRieszFiberRead := by
  apply (ContinuousLinearMap.compL ℝ CauchySafeMatterSpatialFirstJetFiber
    (MatterCoordinateCarrier →L[ℝ] ℝ) MatterCoordinateCarrier
    (InnerProductSpace.toDual ℝ MatterCoordinateCarrier
      ).symm.toContinuousLinearMap).continuous.comp
  exact fixedP506L0CauchySafeMatterGreenRateSpatialFirstJetFiberRead_continuous

private theorem greenRateSpatialFirstJetRieszFiberRead_memLp_top
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    MemLp (fun space ↦
      greenRateSpatialFirstJetRieszFiberRead (time, space)) ∞
      (volume.restrict (Icc a b)) := by
  have fieldContinuous : Continuous (fun space ↦
      greenRateSpatialFirstJetRieszFiberRead (time, space)) :=
    greenRateSpatialFirstJetRieszFiberRead_continuous.comp
      (continuous_const.prodMk continuous_id)
  obtain ⟨C, bound⟩ := isCompact_Icc.exists_bound_of_continuousOn
    fieldContinuous.continuousOn
  apply memLp_top_of_bound fieldContinuous.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with space spaceMem
  exact bound space spaceMem

private theorem lpTop_norm_le_of_ae_bound
    {X E : Type*}
    [MeasurableSpace X]
    [NormedAddCommGroup E]
    (μ : Measure X)
    (field : X → E)
    (fieldMem : MemLp field ∞ μ)
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (bound : ∀ᵐ point ∂μ, ‖field point‖ ≤ C) :
    ‖fieldMem.toLp field‖ ≤ C := by
  rw [Lp.norm_toLp, eLpNorm_exponent_top]
  calc
    ENNReal.toReal (eLpNormEssSup field μ) ≤
        ENNReal.toReal (ENNReal.ofReal C) := by
      apply ENNReal.toReal_mono ENNReal.ofReal_ne_top
      exact eLpNormEssSup_le_of_ae_bound bound
    _ = C := ENNReal.toReal_ofReal CNonnegative

private def greenRateSpatialFirstJetRieszFiberReadLp
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    Lp (CauchySafeMatterSpatialFirstJetFiber →L[ℝ]
      MatterCoordinateCarrier) ∞ (volume.restrict (Icc a b)) :=
  (greenRateSpatialFirstJetRieszFiberRead_memLp_top time a b).toLp
    (fun space ↦ greenRateSpatialFirstJetRieszFiberRead (time, space))

private def greenRateSpatialFirstJetRieszFiberReadCompactPath
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    C(Icc 0 timeEnd,
      BoundedContinuousFunction (Icc a b)
        (CauchySafeMatterSpatialFirstJetFiber →L[ℝ]
          MatterCoordinateCarrier)) := by
  let joint : C((Icc 0 timeEnd) × Icc a b,
      CauchySafeMatterSpatialFirstJetFiber →L[ℝ]
        MatterCoordinateCarrier) :=
    ⟨fun point ↦ greenRateSpatialFirstJetRieszFiberRead
        (point.1.1, point.2.1),
      greenRateSpatialFirstJetRieszFiberRead_continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd))⟩
  exact ⟨fun time ↦
      ContinuousMap.linearIsometryBoundedOfCompact
        (Icc a b)
        (CauchySafeMatterSpatialFirstJetFiber →L[ℝ]
          MatterCoordinateCarrier) ℝ
        (joint.curry time),
    (ContinuousMap.linearIsometryBoundedOfCompact
      (Icc a b)
      (CauchySafeMatterSpatialFirstJetFiber →L[ℝ]
        MatterCoordinateCarrier) ℝ).continuous.comp
      joint.curry.continuous⟩

@[simp] private theorem greenRateSpatialFirstJetRieszFiberReadCompactPath_apply
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (time : Icc 0 timeEnd)
    (space : Icc a b) :
    greenRateSpatialFirstJetRieszFiberReadCompactPath
        timeEnd a b time space =
      greenRateSpatialFirstJetRieszFiberRead (time.1, space.1) :=
  rfl

private theorem greenRateSpatialFirstJetRieszFiberReadLp_dist_le
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (first second : Icc 0 timeEnd) :
    dist
        (greenRateSpatialFirstJetRieszFiberReadLp first.1 a b)
        (greenRateSpatialFirstJetRieszFiberReadLp second.1 a b) ≤
      dist
        (greenRateSpatialFirstJetRieszFiberReadCompactPath
          timeEnd a b first)
        (greenRateSpatialFirstJetRieszFiberReadCompactPath
          timeEnd a b second) := by
  let firstMem := greenRateSpatialFirstJetRieszFiberRead_memLp_top
    first.1 a b
  let secondMem := greenRateSpatialFirstJetRieszFiberRead_memLp_top
    second.1 a b
  let differenceMem := firstMem.sub secondMem
  have differenceEq :
      greenRateSpatialFirstJetRieszFiberReadLp first.1 a b -
          greenRateSpatialFirstJetRieszFiberReadLp second.1 a b =
        differenceMem.toLp
          ((fun space ↦
              greenRateSpatialFirstJetRieszFiberRead (first.1, space)) -
            fun space ↦
              greenRateSpatialFirstJetRieszFiberRead (second.1, space)) := by
    apply Lp.ext
    filter_upwards [
      Lp.coeFn_sub
        (greenRateSpatialFirstJetRieszFiberReadLp first.1 a b)
        (greenRateSpatialFirstJetRieszFiberReadLp second.1 a b),
      firstMem.coeFn_toLp, secondMem.coeFn_toLp,
      differenceMem.coeFn_toLp] with space subEq firstEq secondEq differenceRead
    have firstRead :
        greenRateSpatialFirstJetRieszFiberReadLp first.1 a b space =
          greenRateSpatialFirstJetRieszFiberRead (first.1, space) :=
      firstEq
    have secondRead :
        greenRateSpatialFirstJetRieszFiberReadLp second.1 a b space =
          greenRateSpatialFirstJetRieszFiberRead (second.1, space) :=
      secondEq
    rw [subEq, Pi.sub_apply, firstRead, secondRead, differenceRead]
    rfl
  rw [dist_eq_norm, differenceEq]
  apply lpTop_norm_le_of_ae_bound
    (volume.restrict (Icc a b))
    ((fun space ↦
        greenRateSpatialFirstJetRieszFiberRead (first.1, space)) -
      fun space ↦
        greenRateSpatialFirstJetRieszFiberRead (second.1, space)) differenceMem
    (dist
      (greenRateSpatialFirstJetRieszFiberReadCompactPath
        timeEnd a b first)
      (greenRateSpatialFirstJetRieszFiberReadCompactPath
        timeEnd a b second)) dist_nonneg
  filter_upwards [ae_restrict_mem measurableSet_Icc] with space spaceMem
  simpa only [Pi.sub_apply,
    greenRateSpatialFirstJetRieszFiberReadCompactPath_apply,
    dist_eq_norm] using
    BoundedContinuousFunction.dist_coe_le_dist
      (f := greenRateSpatialFirstJetRieszFiberReadCompactPath
        timeEnd a b first)
      (g := greenRateSpatialFirstJetRieszFiberReadCompactPath
        timeEnd a b second)
      ⟨space, spaceMem⟩

private theorem greenRateSpatialFirstJetRieszFiberReadLp_continuous
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    Continuous (fun time : Icc 0 timeEnd ↦
      greenRateSpatialFirstJetRieszFiberReadLp time.1 a b) := by
  rw [Metric.continuous_iff]
  intro time ε εPositive
  obtain ⟨δ, δPositive, pathControl⟩ := Metric.continuous_iff.mp
    (greenRateSpatialFirstJetRieszFiberReadCompactPath
      timeEnd a b).continuous time ε εPositive
  refine ⟨δ, δPositive, fun candidate close ↦ ?_⟩
  exact (greenRateSpatialFirstJetRieszFiberReadLp_dist_le
    timeEnd a b candidate time).trans_lt (pathControl candidate close)

def greenRateCanonicalInteriorFirstJetL2Action
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    CauchySafeMatterCanonicalInteriorFirstJetL2 a b →L[ℝ]
      CauchySafeMatterSpatialL2 a b :=
  ((greenRateSpatialFirstJetEvaluation.holderL
      (volume.restrict (Icc a b)) ∞ 2 2)
    (greenRateSpatialFirstJetRieszFiberReadLp time a b)).comp
      (packCanonicalInteriorFirstJetL2 a b)

private def massSpatialFirstJetRieszFiberRead
    (point : ℝ × DiracMatterSpatialCoordinates) :
    CauchySafeMatterSpatialFirstJetFiber →L[ℝ] MatterCoordinateCarrier :=
  (matterFiberMassRieszCoordinateBilinear
      (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        point.1 point.2)).comp
    (ContinuousLinearMap.fst ℝ MatterCoordinateCarrier
      (WithLp 2 (Fin 3 → MatterCoordinateCarrier)))

private theorem massSpatialFirstJetRieszFiberRead_continuous :
    Continuous massSpatialFirstJetRieszFiberRead := by
  apply Continuous.clm_comp
  · exact matterFiberMassRieszCoordinateBilinear.continuous.comp
      fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField_joint_continuous
  · exact continuous_const

private theorem massSpatialFirstJetRieszFiberRead_memLp_top
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    MemLp (fun space ↦ massSpatialFirstJetRieszFiberRead (time, space)) ∞
      (volume.restrict (Icc a b)) := by
  have fieldContinuous : Continuous (fun space ↦
      massSpatialFirstJetRieszFiberRead (time, space)) :=
    massSpatialFirstJetRieszFiberRead_continuous.comp
      (continuous_const.prodMk continuous_id)
  obtain ⟨C, bound⟩ := isCompact_Icc.exists_bound_of_continuousOn
    fieldContinuous.continuousOn
  apply memLp_top_of_bound fieldContinuous.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with space spaceMem
  exact bound space spaceMem

private def massSpatialFirstJetRieszFiberReadLp
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    Lp (CauchySafeMatterSpatialFirstJetFiber →L[ℝ]
      MatterCoordinateCarrier) ∞ (volume.restrict (Icc a b)) :=
  (massSpatialFirstJetRieszFiberRead_memLp_top time a b).toLp
    (fun space ↦ massSpatialFirstJetRieszFiberRead (time, space))

private def massSpatialFirstJetRieszFiberReadCompactPath
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    C(Icc 0 timeEnd,
      BoundedContinuousFunction (Icc a b)
        (CauchySafeMatterSpatialFirstJetFiber →L[ℝ]
          MatterCoordinateCarrier)) := by
  let joint : C((Icc 0 timeEnd) × Icc a b,
      CauchySafeMatterSpatialFirstJetFiber →L[ℝ]
        MatterCoordinateCarrier) :=
    ⟨fun point ↦ massSpatialFirstJetRieszFiberRead
        (point.1.1, point.2.1),
      massSpatialFirstJetRieszFiberRead_continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd))⟩
  exact ⟨fun time ↦
      ContinuousMap.linearIsometryBoundedOfCompact
        (Icc a b)
        (CauchySafeMatterSpatialFirstJetFiber →L[ℝ]
          MatterCoordinateCarrier) ℝ
        (joint.curry time),
    (ContinuousMap.linearIsometryBoundedOfCompact
      (Icc a b)
      (CauchySafeMatterSpatialFirstJetFiber →L[ℝ]
        MatterCoordinateCarrier) ℝ).continuous.comp
      joint.curry.continuous⟩

@[simp] private theorem massSpatialFirstJetRieszFiberReadCompactPath_apply
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (time : Icc 0 timeEnd)
    (space : Icc a b) :
    massSpatialFirstJetRieszFiberReadCompactPath timeEnd a b time space =
      massSpatialFirstJetRieszFiberRead (time.1, space.1) :=
  rfl

private theorem massSpatialFirstJetRieszFiberReadLp_dist_le
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (first second : Icc 0 timeEnd) :
    dist
        (massSpatialFirstJetRieszFiberReadLp first.1 a b)
        (massSpatialFirstJetRieszFiberReadLp second.1 a b) ≤
      dist
        (massSpatialFirstJetRieszFiberReadCompactPath timeEnd a b first)
        (massSpatialFirstJetRieszFiberReadCompactPath
          timeEnd a b second) := by
  let firstMem := massSpatialFirstJetRieszFiberRead_memLp_top first.1 a b
  let secondMem := massSpatialFirstJetRieszFiberRead_memLp_top second.1 a b
  let differenceMem := firstMem.sub secondMem
  have differenceEq :
      massSpatialFirstJetRieszFiberReadLp first.1 a b -
          massSpatialFirstJetRieszFiberReadLp second.1 a b =
        differenceMem.toLp
          ((fun space ↦ massSpatialFirstJetRieszFiberRead (first.1, space)) -
            fun space ↦
              massSpatialFirstJetRieszFiberRead (second.1, space)) := by
    apply Lp.ext
    filter_upwards [
      Lp.coeFn_sub
        (massSpatialFirstJetRieszFiberReadLp first.1 a b)
        (massSpatialFirstJetRieszFiberReadLp second.1 a b),
      firstMem.coeFn_toLp, secondMem.coeFn_toLp,
      differenceMem.coeFn_toLp] with space subEq firstEq secondEq differenceRead
    have firstRead :
        massSpatialFirstJetRieszFiberReadLp first.1 a b space =
          massSpatialFirstJetRieszFiberRead (first.1, space) :=
      firstEq
    have secondRead :
        massSpatialFirstJetRieszFiberReadLp second.1 a b space =
          massSpatialFirstJetRieszFiberRead (second.1, space) :=
      secondEq
    rw [subEq, Pi.sub_apply, firstRead, secondRead, differenceRead]
    rfl
  rw [dist_eq_norm, differenceEq]
  apply lpTop_norm_le_of_ae_bound
    (volume.restrict (Icc a b))
    ((fun space ↦ massSpatialFirstJetRieszFiberRead (first.1, space)) -
      fun space ↦ massSpatialFirstJetRieszFiberRead (second.1, space))
    differenceMem
    (dist
      (massSpatialFirstJetRieszFiberReadCompactPath timeEnd a b first)
      (massSpatialFirstJetRieszFiberReadCompactPath
        timeEnd a b second)) dist_nonneg
  filter_upwards [ae_restrict_mem measurableSet_Icc] with space spaceMem
  simpa only [Pi.sub_apply,
    massSpatialFirstJetRieszFiberReadCompactPath_apply,
    dist_eq_norm] using
    BoundedContinuousFunction.dist_coe_le_dist
      (f := massSpatialFirstJetRieszFiberReadCompactPath
        timeEnd a b first)
      (g := massSpatialFirstJetRieszFiberReadCompactPath
        timeEnd a b second)
      ⟨space, spaceMem⟩

private theorem massSpatialFirstJetRieszFiberReadLp_continuous
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    Continuous (fun time : Icc 0 timeEnd ↦
      massSpatialFirstJetRieszFiberReadLp time.1 a b) := by
  rw [Metric.continuous_iff]
  intro time ε εPositive
  obtain ⟨δ, δPositive, pathControl⟩ := Metric.continuous_iff.mp
    (massSpatialFirstJetRieszFiberReadCompactPath
      timeEnd a b).continuous time ε εPositive
  refine ⟨δ, δPositive, fun candidate close ↦ ?_⟩
  exact (massSpatialFirstJetRieszFiberReadLp_dist_le
    timeEnd a b candidate time).trans_lt (pathControl candidate close)

def massCanonicalInteriorFirstJetL2Action
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    CauchySafeMatterCanonicalInteriorFirstJetL2 a b →L[ℝ]
      CauchySafeMatterSpatialL2 a b :=
  ((greenRateSpatialFirstJetEvaluation.holderL
      (volume.restrict (Icc a b)) ∞ 2 2)
    (massSpatialFirstJetRieszFiberReadLp time a b)).comp
      (packCanonicalInteriorFirstJetL2 a b)

def weightedCanonicalInteriorFirstJetL2Action
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (weight : ℝ → ℝ) :
    CauchySafeMatterCanonicalInteriorFirstJetL2 a b →L[ℝ]
      CauchySafeMatterSpatialL2 a b :=
  weight time • greenRateCanonicalInteriorFirstJetL2Action time a b +
    deriv weight time • massCanonicalInteriorFirstJetL2Action time a b

private theorem greenRateCanonicalInteriorFirstJetL2Action_continuous
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    Continuous (fun time : Icc 0 timeEnd ↦
      greenRateCanonicalInteriorFirstJetL2Action time.1 a b) := by
  apply Continuous.clm_comp
  · exact ((greenRateSpatialFirstJetEvaluation.holderL
      (volume.restrict (Icc a b)) ∞ 2 2).continuous.comp
        (greenRateSpatialFirstJetRieszFiberReadLp_continuous
          timeEnd a b))
  · exact continuous_const

private theorem massCanonicalInteriorFirstJetL2Action_continuous
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    Continuous (fun time : Icc 0 timeEnd ↦
      massCanonicalInteriorFirstJetL2Action time.1 a b) := by
  apply Continuous.clm_comp
  · exact ((greenRateSpatialFirstJetEvaluation.holderL
      (volume.restrict (Icc a b)) ∞ 2 2).continuous.comp
        (massSpatialFirstJetRieszFiberReadLp_continuous timeEnd a b))
  · exact continuous_const

/-- The generated Green-rate action operator varies continuously along the
fixed compact time interval. -/
theorem greenRateCanonicalInteriorFirstJetL2Action_continuousOnTimeBox
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    Continuous (fun time : Icc 0 timeEnd ↦
      greenRateCanonicalInteriorFirstJetL2Action time.1 a b) :=
  greenRateCanonicalInteriorFirstJetL2Action_continuous timeEnd a b

/-- The generated mass action operator varies continuously along the fixed
compact time interval. -/
theorem massCanonicalInteriorFirstJetL2Action_continuousOnTimeBox
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    Continuous (fun time : Icc 0 timeEnd ↦
      massCanonicalInteriorFirstJetL2Action time.1 a b) :=
  massCanonicalInteriorFirstJetL2Action_continuous timeEnd a b

private theorem weightedCanonicalInteriorFirstJetL2Action_continuous
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    Continuous (fun time : Icc 0 timeEnd ↦
      weightedCanonicalInteriorFirstJetL2Action time.1 a b weight) := by
  apply Continuous.add
  · exact (weightRegular.continuous.comp continuous_subtype_val).smul
      (greenRateCanonicalInteriorFirstJetL2Action_continuous
        timeEnd a b)
  · exact (weightRegular.continuous_deriv le_rfl |>.comp
      continuous_subtype_val).smul
        (massCanonicalInteriorFirstJetL2Action_continuous timeEnd a b)

private def weightedCanonicalInteriorFirstJetL2ActionBoundedPath
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    BoundedContinuousFunction (Icc 0 timeEnd)
      (CauchySafeMatterCanonicalInteriorFirstJetL2 a b →L[ℝ]
        CauchySafeMatterSpatialL2 a b) :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun time ↦ weightedCanonicalInteriorFirstJetL2Action
        time.1 a b weight,
      weightedCanonicalInteriorFirstJetL2Action_continuous
        timeEnd a b weight weightRegular⟩

private def greenRateCanonicalInteriorFirstJetL2ActionBoundedPath
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    BoundedContinuousFunction (Icc 0 timeEnd)
      (CauchySafeMatterCanonicalInteriorFirstJetL2 a b →L[ℝ]
        CauchySafeMatterSpatialL2 a b) :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun time ↦ greenRateCanonicalInteriorFirstJetL2Action time.1 a b,
      greenRateCanonicalInteriorFirstJetL2Action_continuous timeEnd a b⟩

private def boundedOperatorPathApply
    {T X Y : Type*}
    [TopologicalSpace T]
    [CompactSpace T]
    [NormedAddCommGroup X]
    [NormedSpace ℝ X]
    [NormedAddCommGroup Y]
    [NormedSpace ℝ Y]
    (operatorPath : BoundedContinuousFunction T (X →L[ℝ] Y)) :
    X →L[ℝ] BoundedContinuousFunction T Y :=
  LinearMap.mkContinuous
    { toFun := fun value ↦ BoundedContinuousFunction.mkOfCompact
        ⟨fun point ↦ operatorPath point value,
          operatorPath.continuous.clm_apply continuous_const⟩
      map_add' := by
        intro first second
        apply BoundedContinuousFunction.ext
        intro point
        exact map_add (operatorPath point) first second
      map_smul' := by
        intro parameter value
        apply BoundedContinuousFunction.ext
        intro point
        exact map_smul (operatorPath point) parameter value }
    ‖operatorPath‖
    (fun value ↦ by
      apply (BoundedContinuousFunction.norm_le
        (mul_nonneg (norm_nonneg operatorPath) (norm_nonneg value))).2
      intro point
      exact (ContinuousLinearMap.le_opNorm (operatorPath point) value).trans
        (mul_le_mul_of_nonneg_right
          (operatorPath.norm_coe_le_norm point) (norm_nonneg value)))

@[simp] private theorem weightedCanonicalInteriorFirstJetL2Action_apply
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (weight : ℝ → ℝ)
    (jet : CauchySafeMatterCanonicalInteriorFirstJetL2 a b) :
    weightedCanonicalInteriorFirstJetL2Action time a b weight jet =
      weight time • greenRateCanonicalInteriorFirstJetL2Action time a b jet +
        deriv weight time •
          massCanonicalInteriorFirstJetL2Action time a b jet :=
  rfl

private theorem massCanonicalInteriorFirstJetL2Action_coe_ae
    {a b : DiracMatterSpatialCoordinates}
    (test : CauchySafeMatterCanonicalInteriorSmoothTest a b)
    (time : ℝ) :
    massCanonicalInteriorFirstJetL2Action time a b
        (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test) =ᵐ[
          volume.restrict (Icc a b)]
      fun space ↦ matterFiberMassRiesz
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
        (test.1.1 space) := by
  have coefficientAE :=
    (massSpatialFirstJetRieszFiberRead_memLp_top time a b).coeFn_toLp
  have packedAE := packCanonicalInteriorFirstJetL2_coe_ae test
  have holderAE := greenRateSpatialFirstJetEvaluation.coeFn_holder (r := 2)
    (massSpatialFirstJetRieszFiberReadLp time a b)
    (packCanonicalInteriorFirstJetL2 a b
      (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test))
  filter_upwards [coefficientAE, packedAE, holderAE] with space coefficientEq
    packedEq holderEq
  rw [show massCanonicalInteriorFirstJetL2Action time a b
      (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test) =
        greenRateSpatialFirstJetEvaluation.holder 2
          (massSpatialFirstJetRieszFiberReadLp time a b)
          (packCanonicalInteriorFirstJetL2 a b
            (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test)) by
      rfl]
  rw [holderEq]
  have coefficientEq' :
      (massSpatialFirstJetRieszFiberReadLp time a b) space =
        massSpatialFirstJetRieszFiberRead (time, space) := coefficientEq
  rw [coefficientEq', packedEq]
  rfl

private theorem greenRateCanonicalInteriorFirstJetL2Action_coe_ae
    {a b : DiracMatterSpatialCoordinates}
    (test : CauchySafeMatterCanonicalInteriorSmoothTest a b)
    (time : ℝ) :
    greenRateCanonicalInteriorFirstJetL2Action time a b
        (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test) =ᵐ[
          volume.restrict (Icc a b)]
      fixedP506L0CauchySafeMatterGreenRateRieszField
        (interiorSpacetimeTest test) time := by
  have coefficientAE :=
    (greenRateSpatialFirstJetRieszFiberRead_memLp_top
      time a b).coeFn_toLp
  have packedAE := packCanonicalInteriorFirstJetL2_coe_ae test
  have holderAE := greenRateSpatialFirstJetEvaluation.coeFn_holder (r := 2)
    (greenRateSpatialFirstJetRieszFiberReadLp time a b)
    (packCanonicalInteriorFirstJetL2 a b
      (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test))
  filter_upwards [coefficientAE, packedAE, holderAE] with space coefficientEq
    packedEq holderEq
  rw [show greenRateCanonicalInteriorFirstJetL2Action time a b
      (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test) =
        greenRateSpatialFirstJetEvaluation.holder 2
          (greenRateSpatialFirstJetRieszFiberReadLp time a b)
          (packCanonicalInteriorFirstJetL2 a b
            (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test)) by
      rfl]
  rw [holderEq]
  have coefficientEq' :
      (greenRateSpatialFirstJetRieszFiberReadLp time a b) space =
        greenRateSpatialFirstJetRieszFiberRead (time, space) :=
    coefficientEq
  rw [coefficientEq', packedEq]
  unfold greenRateSpatialFirstJetEvaluation
  change greenRateSpatialFirstJetRieszFiberRead (time, space)
      (test.1.1 space,
        WithLp.toLp 2 fun direction ↦
          (cauchySafeMatterCanonicalInteriorSmoothTestDerivative
            test direction).1 space) = _
  unfold greenRateSpatialFirstJetRieszFiberRead
  change (InnerProductSpace.toDual ℝ MatterCoordinateCarrier).symm
      (fixedP506L0CauchySafeMatterGreenRateSpatialFirstJetFiberRead
        (time, space)
        (test.1.1 space,
          WithLp.toLp 2 fun direction ↦
            (cauchySafeMatterCanonicalInteriorSmoothTestDerivative
              test direction).1 space)) =
    (InnerProductSpace.toDual ℝ MatterCoordinateCarrier).symm
      (fixedP506L0CauchySafeMatterGreenRateFiberRead
        (interiorSpacetimeTest test) (time, space))
  apply congrArg (InnerProductSpace.toDual ℝ MatterCoordinateCarrier).symm
  rw [fixedP506L0CauchySafeMatterGreenRateFiberRead_eq_spatialFirstJetRead]
  apply congrArg
    (fixedP506L0CauchySafeMatterGreenRateSpatialFirstJetFiberRead
      (time, space))
  apply Prod.ext
  · exact (interiorSpacetimeTest_slice test time space).symm
  · apply PiLp.ext
    intro direction
    exact (interiorSpacetimeTest_spatialDerivative_slice
      test time space direction).symm

private def greenRateCanonicalInteriorFirstJetL2Read
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    CauchySafeMatterCanonicalInteriorFirstJetL2 a b →L[ℝ]
      (CauchySafeMatterSpatialL2 a b →L[ℝ] ℝ) :=
  (innerSL ℝ).comp (greenRateCanonicalInteriorFirstJetL2Action time a b)

theorem greenRateCanonicalInteriorFirstJetL2Read_eq
    {a b : DiracMatterSpatialCoordinates}
    (test : CauchySafeMatterCanonicalInteriorSmoothTest a b)
    (time : ℝ)
    (trial : CauchySafeMatterSpatialL2 a b) :
    greenRateCanonicalInteriorFirstJetL2Read time a b
        (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test) trial =
      fixedP506L0CauchySafeMatterGreenRateL2Read
        (interiorSpacetimeTest test)
        (interiorSpacetimeTest_contDiff_one test)
        time a b trial := by
  change inner ℝ
      (greenRateCanonicalInteriorFirstJetL2Action time a b
        (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test)) trial = _
  calc
    _ = ∫ space,
        inner ℝ
          ((greenRateCanonicalInteriorFirstJetL2Action time a b
            (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test)) space)
          (trial space)
        ∂volume.restrict (Icc a b) := L2.inner_def _ _
    _ = ∫ space,
        fixedP506L0CauchySafeMatterGreenRateFiberRead
          (interiorSpacetimeTest test) (time, space) (trial space)
        ∂volume.restrict (Icc a b) := by
      apply integral_congr_ae
      filter_upwards [greenRateCanonicalInteriorFirstJetL2Action_coe_ae
          test time] with space actionEq
      rw [actionEq]
      exact InnerProductSpace.toDual_symm_apply
    _ = _ := (fixedP506L0CauchySafeMatterGreenRateL2Read_eq_integral
      (interiorSpacetimeTest test)
      (interiorSpacetimeTest_contDiff_one test)
      time a b trial).symm

theorem massCanonicalInteriorFirstJetL2Read_eq_integral
    {a b : DiracMatterSpatialCoordinates}
    (test : CauchySafeMatterCanonicalInteriorSmoothTest a b)
    (time : ℝ)
    (trial : CauchySafeMatterSpatialL2 a b) :
    inner ℝ
        (massCanonicalInteriorFirstJetL2Action time a b
          (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test))
        trial =
      ∫ space,
        matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
          (test.1.1 space) (trial space)
        ∂volume.restrict (Icc a b) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [massCanonicalInteriorFirstJetL2Action_coe_ae test time]
    with space actionEq
  rw [actionEq, matterFiberMassRiesz_pairing]

theorem weightedCanonicalInteriorFirstJetL2Action_inner_eq
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (weight : ℝ → ℝ)
    (jet : CauchySafeMatterCanonicalInteriorFirstJetL2 a b)
    (trial : CauchySafeMatterSpatialL2 a b) :
    inner ℝ
        (weightedCanonicalInteriorFirstJetL2Action time a b weight jet)
        trial =
      weight time *
          inner ℝ
            (greenRateCanonicalInteriorFirstJetL2Action time a b jet) trial +
        deriv weight time *
          inner ℝ
            (massCanonicalInteriorFirstJetL2Action time a b jet) trial := by
  calc
    _ = inner ℝ
        (weight time • greenRateCanonicalInteriorFirstJetL2Action time a b jet +
          deriv weight time • massCanonicalInteriorFirstJetL2Action time a b jet)
        trial := congrArg (fun field ↦ inner ℝ field trial)
          (weightedCanonicalInteriorFirstJetL2Action_apply time a b weight jet)
    _ = inner ℝ
          (weight time • greenRateCanonicalInteriorFirstJetL2Action time a b jet)
          trial +
        inner ℝ
          (deriv weight time • massCanonicalInteriorFirstJetL2Action time a b jet)
          trial := inner_add_left _ _ _
    _ = _ := congrArg₂ (· + ·)
      (inner_smul_left _ _ _)
      (inner_smul_left _ _ _)

private theorem greenRateCanonicalInteriorFirstJetL2Action_dense_inner_eq
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (index : ℕ)
    (time : Icc 0 timeEnd) :
    inner ℝ
        (greenRateCanonicalInteriorFirstJetL2Action time.1 a b
          (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b
            (cauchySafeMatterCanonicalInteriorFirstJetDenseTest a b index)))
        (canonicalAffinePhysicalTimeL2Output
          timeEnd timeNonnegative a b boxOrder time) =
      canonicalAffinePhysicalTimeL2GreenRate
        timeEnd timeNonnegative a b boxOrder index time := by
  change greenRateCanonicalInteriorFirstJetL2Read time.1 a b
      (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b
        (cauchySafeMatterCanonicalInteriorFirstJetDenseTest a b index))
      (canonicalAffinePhysicalTimeL2Output
        timeEnd timeNonnegative a b boxOrder time) = _
  rw [greenRateCanonicalInteriorFirstJetL2Read_eq]
  rfl

theorem canonicalInteriorDenseMassIntegral_eq_spatialMassRead
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (index : ℕ)
    (field : CauchySafeMatterSpatialL2 a b) :
    (∫ space,
        matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
          ((cauchySafeMatterCanonicalInteriorDenseTest a b index).1 space)
          (field space)
        ∂volume.restrict (Icc a b)) =
      fixedP506L0CauchySafeMatterSpatialMassRead time a b field index := by
  rw [fixedP506L0CauchySafeMatterSpatialMassRead]
  apply integral_congr_ae
  filter_upwards [
    (cauchySafeMatterSmoothCompactTest_memLp a b
      (cauchySafeMatterCanonicalInteriorDenseTest a b index)).coeFn_toLp]
    with space testEq
  have testRead :
      (cauchySafeMatterSmoothCompactTestToL2 a b
        (cauchySafeMatterCanonicalInteriorDenseTest a b index)) space =
      (cauchySafeMatterCanonicalInteriorDenseTest a b index).1 space :=
    testEq
  rw [testRead]
  exact diracExteriorMatterEnergyPairing_symm _
    (fixedP506L0CauchySafeMatterWeakMassMatrix_posDef
      time space).isHermitian _ _

private theorem massCanonicalInteriorFirstJetL2Action_dense_inner_eq
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (index : ℕ)
    (time : Icc 0 timeEnd) :
    inner ℝ
        (massCanonicalInteriorFirstJetL2Action time.1 a b
          (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b
            (cauchySafeMatterCanonicalInteriorFirstJetDenseTest a b index)))
        (canonicalAffinePhysicalTimeL2Output
          timeEnd timeNonnegative a b boxOrder time) =
      canonicalAffinePhysicalTimeL2MassRead
        timeEnd timeNonnegative a b boxOrder index time := by
  calc
    _ = ∫ space,
        matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time.1 space)
          ((cauchySafeMatterCanonicalInteriorDenseTest a b index).1 space)
          ((canonicalAffinePhysicalTimeL2Output
            timeEnd timeNonnegative a b boxOrder time) space)
        ∂volume.restrict (Icc a b) :=
      massCanonicalInteriorFirstJetL2Read_eq_integral
        (cauchySafeMatterCanonicalInteriorFirstJetDenseTest a b index)
          time.1 _
    _ = fixedP506L0CauchySafeMatterSpatialMassRead time.1 a b
        (canonicalAffinePhysicalTimeL2Output
          timeEnd timeNonnegative a b boxOrder time) index :=
      canonicalInteriorDenseMassIntegral_eq_spatialMassRead
        time.1 a b index _
    _ = _ := (canonicalAffinePhysicalTimeL2MassRead_eq_spatialMassRead
      timeEnd timeNonnegative a b boxOrder index time).symm

def canonicalInteriorFirstJetWeightedActionValue
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (weight : ℝ → ℝ)
    (jet : CauchySafeMatterCanonicalInteriorFirstJetL2 a b) : ℝ :=
  ∫ time : Icc 0 timeEnd,
    inner ℝ
      (weightedCanonicalInteriorFirstJetL2Action time.1 a b weight jet)
      (canonicalAffinePhysicalTimeL2Output
        timeEnd timeNonnegative a b boxOrder time)
    ∂canonicalAffineTimeMeasure timeEnd

def canonicalInteriorFirstJetWeightedActionTimeL2
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    CauchySafeMatterCanonicalInteriorFirstJetL2 a b →L[ℝ]
      Lp (CauchySafeMatterSpatialL2 a b) 2
        (canonicalAffineTimeMeasure timeEnd) :=
  (BoundedContinuousFunction.toLp 2
    (canonicalAffineTimeMeasure timeEnd) ℝ).comp
      (boundedOperatorPathApply
        (weightedCanonicalInteriorFirstJetL2ActionBoundedPath
          timeEnd a b weight weightRegular))

/-- The generated Green operator as a continuous linear map into time-`L²`.
This is the native carrier for rate integrability; no constant-weight
reduction is required. -/
def greenRateCanonicalInteriorFirstJetL2ActionTimeL2
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    CauchySafeMatterCanonicalInteriorFirstJetL2 a b →L[ℝ]
      Lp (CauchySafeMatterSpatialL2 a b) 2
        (canonicalAffineTimeMeasure timeEnd) :=
  (BoundedContinuousFunction.toLp 2
    (canonicalAffineTimeMeasure timeEnd) ℝ).comp
      (boundedOperatorPathApply
        (greenRateCanonicalInteriorFirstJetL2ActionBoundedPath timeEnd a b))

theorem greenRateCanonicalInteriorFirstJetL2ActionTimeL2_coe_ae
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (jet : CauchySafeMatterCanonicalInteriorFirstJetL2 a b) :
    greenRateCanonicalInteriorFirstJetL2ActionTimeL2 timeEnd a b jet =ᵐ[
        canonicalAffineTimeMeasure timeEnd]
      fun time ↦ greenRateCanonicalInteriorFirstJetL2Action
        time.1 a b jet := by
  change BoundedContinuousFunction.toLp 2
        (canonicalAffineTimeMeasure timeEnd) ℝ
        (boundedOperatorPathApply
          (greenRateCanonicalInteriorFirstJetL2ActionBoundedPath
            timeEnd a b) jet) =ᵐ[
      canonicalAffineTimeMeasure timeEnd]
    fun time ↦ greenRateCanonicalInteriorFirstJetL2Action time.1 a b jet
  exact BoundedContinuousFunction.coeFn_toLp 2
    (canonicalAffineTimeMeasure timeEnd) ℝ _

theorem canonicalInteriorFirstJetWeightedActionTimeL2_coe_ae
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (jet : CauchySafeMatterCanonicalInteriorFirstJetL2 a b) :
    canonicalInteriorFirstJetWeightedActionTimeL2
          timeEnd a b weight weightRegular jet =ᵐ[
        canonicalAffineTimeMeasure timeEnd]
      fun time ↦ weightedCanonicalInteriorFirstJetL2Action
        time.1 a b weight jet := by
  change BoundedContinuousFunction.toLp 2
        (canonicalAffineTimeMeasure timeEnd) ℝ
        (boundedOperatorPathApply
          (weightedCanonicalInteriorFirstJetL2ActionBoundedPath
            timeEnd a b weight weightRegular) jet) =ᵐ[
      canonicalAffineTimeMeasure timeEnd]
    fun time ↦ weightedCanonicalInteriorFirstJetL2Action
      time.1 a b weight jet
  exact BoundedContinuousFunction.coeFn_toLp 2
    (canonicalAffineTimeMeasure timeEnd) ℝ _

private theorem timeL2_inner_eq_integral
    {T H : Type*}
    [MeasurableSpace T]
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    (μ : Measure T)
    (first second : Lp H 2 μ) :
    inner ℝ first second = ∫ point, inner ℝ (first point) (second point) ∂μ :=
  L2.inner_def first second

private theorem integral_inner_eq_inner_of_ae
    {T H : Type*}
    [MeasurableSpace T]
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    (μ : Measure T)
    (first second : Lp H 2 μ)
    (field : T → H)
    (firstRead : first =ᵐ[μ] field) :
    (∫ point, inner ℝ (field point) (second point) ∂μ) =
      inner ℝ first second := by
  calc
    _ = ∫ point, inner ℝ (first point) (second point) ∂μ := by
      apply integral_congr_ae
      filter_upwards [firstRead] with point pointRead
      rw [pointRead]
    _ = _ := (timeL2_inner_eq_integral μ first second).symm

private def canonicalInteriorFirstJetWeightedActionFunctional
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    CauchySafeMatterCanonicalInteriorFirstJetL2 a b →L[ℝ] ℝ :=
  ((innerSL ℝ).flip
    (canonicalAffinePhysicalTimeL2Output
      timeEnd timeNonnegative a b boxOrder)).comp
        (canonicalInteriorFirstJetWeightedActionTimeL2
          timeEnd a b weight weightRegular)

@[simp] private theorem canonicalInteriorFirstJetWeightedActionFunctional_apply
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (jet : CauchySafeMatterCanonicalInteriorFirstJetL2 a b) :
    canonicalInteriorFirstJetWeightedActionFunctional
        timeEnd timeNonnegative a b boxOrder weight weightRegular jet =
      inner ℝ
        (canonicalInteriorFirstJetWeightedActionTimeL2
          timeEnd a b weight weightRegular jet)
        (canonicalAffinePhysicalTimeL2Output
          timeEnd timeNonnegative a b boxOrder) :=
  rfl

private theorem canonicalInteriorFirstJetWeightedActionValue_eq_functional
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (jet : CauchySafeMatterCanonicalInteriorFirstJetL2 a b) :
    canonicalInteriorFirstJetWeightedActionValue
        timeEnd timeNonnegative a b boxOrder weight jet =
      canonicalInteriorFirstJetWeightedActionFunctional
        timeEnd timeNonnegative a b boxOrder weight weightRegular jet := by
  let actionTime : Lp (CauchySafeMatterSpatialL2 a b) 2
      (canonicalAffineTimeMeasure timeEnd) :=
    canonicalInteriorFirstJetWeightedActionTimeL2
      timeEnd a b weight weightRegular jet
  let output : Lp (CauchySafeMatterSpatialL2 a b) 2
      (canonicalAffineTimeMeasure timeEnd) :=
    canonicalAffinePhysicalTimeL2Output
      timeEnd timeNonnegative a b boxOrder
  have actionRead : actionTime =ᵐ[canonicalAffineTimeMeasure timeEnd]
      fun time ↦ weightedCanonicalInteriorFirstJetL2Action
        time.1 a b weight jet :=
    canonicalInteriorFirstJetWeightedActionTimeL2_coe_ae
      timeEnd a b weight weightRegular jet
  calc
    _ = ∫ time : Icc 0 timeEnd,
        inner ℝ
          (weightedCanonicalInteriorFirstJetL2Action time.1 a b weight jet)
          (canonicalAffinePhysicalTimeL2Output
            timeEnd timeNonnegative a b boxOrder time)
        ∂canonicalAffineTimeMeasure timeEnd := rfl
    _ = inner ℝ actionTime output :=
      integral_inner_eq_inner_of_ae
        (canonicalAffineTimeMeasure timeEnd) actionTime output
        (fun time ↦ weightedCanonicalInteriorFirstJetL2Action
          time.1 a b weight jet) actionRead
    _ = inner ℝ
        (canonicalInteriorFirstJetWeightedActionTimeL2
          timeEnd a b weight weightRegular jet)
        (canonicalAffinePhysicalTimeL2Output
          timeEnd timeNonnegative a b boxOrder) := rfl
    _ = _ := (canonicalInteriorFirstJetWeightedActionFunctional_apply
        timeEnd timeNonnegative a b boxOrder weight weightRegular jet).symm

theorem canonicalInteriorFirstJetWeightedActionValue_continuous
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    Continuous (fun jet : CauchySafeMatterCanonicalInteriorFirstJetL2 a b ↦
      canonicalInteriorFirstJetWeightedActionValue
        timeEnd timeNonnegative a b boxOrder weight jet) := by
  exact (canonicalInteriorFirstJetWeightedActionFunctional
    timeEnd timeNonnegative a b boxOrder weight weightRegular).continuous.congr
      (fun jet ↦
        (canonicalInteriorFirstJetWeightedActionValue_eq_functional
          timeEnd timeNonnegative a b boxOrder weight weightRegular jet).symm)

theorem canonicalInteriorFirstJetWeightedActionValue_dense_boundary
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (index : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (weightEndZero : weight timeEnd = 0) :
    canonicalInteriorFirstJetWeightedActionValue
        timeEnd timeNonnegative a b boxOrder weight
        (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b
          (cauchySafeMatterCanonicalInteriorFirstJetDenseTest a b index)) =
      -weight 0 * canonicalSourceLiftMassRead a b index 0 := by
  rw [canonicalInteriorFirstJetWeightedActionValue]
  calc
    _ = ∫ time : Icc 0 timeEnd,
        weight time.1 *
            canonicalAffinePhysicalTimeL2GreenRate
              timeEnd timeNonnegative a b boxOrder index time +
          deriv weight time.1 *
            canonicalAffinePhysicalTimeL2MassRead
              timeEnd timeNonnegative a b boxOrder index time
        ∂canonicalAffineTimeMeasure timeEnd := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun time ↦ by
        calc
          _ = weight time.1 *
                inner ℝ
                  (greenRateCanonicalInteriorFirstJetL2Action time.1 a b
                    (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b
                      (cauchySafeMatterCanonicalInteriorFirstJetDenseTest
                        a b index)))
                  (canonicalAffinePhysicalTimeL2Output
                    timeEnd timeNonnegative a b boxOrder time) +
              deriv weight time.1 *
                inner ℝ
                  (massCanonicalInteriorFirstJetL2Action time.1 a b
                    (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b
                      (cauchySafeMatterCanonicalInteriorFirstJetDenseTest
                        a b index)))
                  (canonicalAffinePhysicalTimeL2Output
                    timeEnd timeNonnegative a b boxOrder time) :=
            weightedCanonicalInteriorFirstJetL2Action_inner_eq
              time.1 a b weight _ _
          _ = _ := by
            exact congrArg₂ (· + ·)
              (congrArg (weight time.1 * ·)
                (greenRateCanonicalInteriorFirstJetL2Action_dense_inner_eq
                  timeEnd timeNonnegative a b boxOrder index time))
              (congrArg (deriv weight time.1 * ·)
                (massCanonicalInteriorFirstJetL2Action_dense_inner_eq
                  timeEnd timeNonnegative a b boxOrder index time))
    _ = _ := canonicalAffinePhysicalTimeL2Output_weightedIntegralActionLaw_of_endZero
      timeEnd timeNonnegative a b boxOrder index weight weightRegular
        weightEndZero

theorem canonicalAffinePhysicalTimeL2Output_weightedActionLaw_of_interiorSmoothTest
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : CauchySafeMatterCanonicalInteriorSmoothTest a b)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (weightZero : weight 0 = 0)
    (weightEndZero : weight timeEnd = 0) :
    canonicalInteriorFirstJetWeightedActionValue
        timeEnd timeNonnegative a b boxOrder weight
        (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test) = 0 := by
  let denseTest : ℕ →
      Set.range (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b) :=
    fun index ↦
      ⟨cauchySafeMatterCanonicalInteriorFirstJetToL2 a b
          (cauchySafeMatterCanonicalInteriorFirstJetDenseTest a b index),
        ⟨cauchySafeMatterCanonicalInteriorFirstJetDenseTest a b index, rfl⟩⟩
  let read : Set.range
      (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b) → ℝ :=
    fun jet ↦ canonicalInteriorFirstJetWeightedActionValue
      timeEnd timeNonnegative a b boxOrder weight jet.1
  have readContinuous : Continuous read :=
    (canonicalInteriorFirstJetWeightedActionValue_continuous
      timeEnd timeNonnegative a b boxOrder weight weightRegular).comp
        continuous_subtype_val
  have readDenseZero : read ∘ denseTest = (fun _ ↦ 0) ∘ denseTest := by
    funext index
    simpa only [Function.comp_apply, weightZero, neg_zero, zero_mul] using
      canonicalInteriorFirstJetWeightedActionValue_dense_boundary
        timeEnd timeNonnegative a b boxOrder index weight weightRegular
          weightEndZero
  have readEqZero :=
    (cauchySafeMatterCanonicalInteriorFirstJetDenseTest_denseRange a b
      ).equalizer readContinuous continuous_const readDenseZero
  exact congr_fun readEqZero
    ⟨cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test,
      ⟨test, rfl⟩⟩

end


end SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineInteriorFirstJetActionLaw
