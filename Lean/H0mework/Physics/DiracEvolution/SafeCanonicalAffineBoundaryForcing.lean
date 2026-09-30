import H0mework.Physics.DiracEvolution.SafeCanonicalAffineBoundaryStep
import H0mework.Physics.DiracEvolution.SafeCanonicalUniformTimeProjection

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineBoundaryForcing

open Filter MeasureTheory Metric Set
open DiracExteriorMatterAction
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineBoundaryStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalCrossLevelStability
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalDynamicMassProjection
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalMassProjectionConvergence
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalUniformTimeMassGeometry
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalUniformTimeProjection
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterFiniteL2MassRead
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyEstimate
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterGalerkinEvolution
open StageNineDiracMatterHermitianEnergy
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakGalerkinEvolution
open StageNineDiracMatterWeakGalerkinEnergy
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineDynamicBreakingVacuum
open StageNineHolonomicField
open scoped ComplexOrder

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000

private theorem boundaryLiftActionResponse_memLp
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    MemLp (fun space : DiracMatterSpatialCoordinates ↦
      boundaryLiftActionResponse (time, space))
      2 (volume.restrict (Icc a b)) := by
  letI : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    { measure_univ_lt_top := by simp [isCompact_Icc.measure_lt_top] }
  have responseContinuous := boundaryLiftActionResponse_continuous time
  obtain ⟨C, bound⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn
      responseContinuous.continuousOn
  apply MemLp.of_bound responseContinuous.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with space spaceMem
  exact bound space spaceMem

def boundaryLiftActionResponseL2
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    CauchySafeMatterSpatialL2 a b :=
  (boundaryLiftActionResponse_memLp time a b).toLp
    (fun space ↦ boundaryLiftActionResponse (time, space))

theorem boundaryLiftActionResponseL2_coe_ae
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    ∀ᵐ space ∂volume.restrict (Icc a b),
      boundaryLiftActionResponseL2 time a b space =
        boundaryLiftActionResponse (time, space) :=
  (boundaryLiftActionResponse_memLp time a b).coeFn_toLp

private theorem boundaryLiftActionResponseL2_norm_sub_sq
    (time referenceTime : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    ‖boundaryLiftActionResponseL2 time a b -
        boundaryLiftActionResponseL2 referenceTime a b‖ ^ 2 =
      ∫ space in Icc a b,
        ‖boundaryLiftActionResponse (time, space) -
          boundaryLiftActionResponse (referenceTime, space)‖ ^ 2 := by
  rw [cauchySafeMatterSpatialL2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [
    Lp.coeFn_sub
      (boundaryLiftActionResponseL2 time a b)
      (boundaryLiftActionResponseL2 referenceTime a b),
    boundaryLiftActionResponseL2_coe_ae time a b,
    boundaryLiftActionResponseL2_coe_ae referenceTime a b] with
      space subRead timeRead referenceRead
  rw [subRead]
  change
    ‖boundaryLiftActionResponseL2 time a b space -
        boundaryLiftActionResponseL2 referenceTime a b space‖ ^ 2 = _
  rw [timeRead, referenceRead]

theorem boundaryLiftActionResponseL2_continuous
    (a b : DiracMatterSpatialCoordinates) :
    Continuous fun time ↦ boundaryLiftActionResponseL2 time a b := by
  rw [continuous_iff_continuousAt]
  intro referenceTime
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have integrandJoint : Continuous fun input :
      ℝ × DiracMatterSpatialCoordinates ↦
      ‖boundaryLiftActionResponse (input.1, input.2) -
        boundaryLiftActionResponse (referenceTime, input.2)‖ ^ 2 := by
    apply Continuous.pow
    apply continuous_norm.comp
    exact boundaryLiftActionResponse_joint_continuous.sub
      ((boundaryLiftActionResponse_continuous referenceTime).comp
        continuous_snd)
  have integralContinuous : Continuous fun time ↦
      ∫ space in Icc a b,
        ‖boundaryLiftActionResponse (time, space) -
          boundaryLiftActionResponse (referenceTime, space)‖ ^ 2 := by
    apply continuous_parametric_integral_of_continuous
      (hs := isCompact_Icc)
    exact integrandJoint
  have integralAtReference :
      (∫ space in Icc a b,
        ‖boundaryLiftActionResponse (referenceTime, space) -
          boundaryLiftActionResponse (referenceTime, space)‖ ^ 2) = 0 := by
    simp
  have squareTendsto : Tendsto
      (fun time ↦
        ‖boundaryLiftActionResponseL2 time a b -
          boundaryLiftActionResponseL2 referenceTime a b‖ ^ 2)
      (nhds referenceTime) (nhds 0) := by
    have integralTendsto :=
      integralContinuous.continuousAt (x := referenceTime)
    change Tendsto _ (nhds referenceTime) (nhds
      ((fun time ↦
        ∫ space in Icc a b,
          ‖boundaryLiftActionResponse (time, space) -
            boundaryLiftActionResponse (referenceTime, space)‖ ^ 2)
        referenceTime)) at integralTendsto
    have endpointEq :
        ((fun time ↦
          ∫ space in Icc a b,
            ‖boundaryLiftActionResponse (time, space) -
              boundaryLiftActionResponse (referenceTime, space)‖ ^ 2)
          referenceTime) = 0 := by
      simp
    rw [endpointEq] at integralTendsto
    exact integralTendsto.congr'
      (Filter.Eventually.of_forall fun time ↦
        (boundaryLiftActionResponseL2_norm_sub_sq
          time referenceTime a b).symm)
  have sqrtTendsto :=
    Real.continuous_sqrt.continuousAt.tendsto.comp squareTendsto
  have sqrtTendstoZero : Tendsto
      ((fun value : ℝ ↦ √value) ∘ fun time ↦
        ‖boundaryLiftActionResponseL2 time a b -
          boundaryLiftActionResponseL2 referenceTime a b‖ ^ 2)
      (nhds referenceTime) (nhds 0) := by
    simpa only [Real.sqrt_zero] using sqrtTendsto
  exact sqrtTendstoZero.congr'
    (Filter.Eventually.of_forall fun time ↦ by
      simp [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)])

private theorem canonicalTrial_zero_outside_box
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (test : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b testCount)
    (space : DiracMatterSpatialCoordinates)
    (spaceOutside : space ∉ Icc a b) :
    diracMatterSpatialGalerkinSynthesis
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
          a b testCount)
        test space = 0 := by
  have outsideInterior : ¬ DiracMatterSpatialBoxInterior a b space := by
    intro spaceInterior
    apply spaceOutside
    exact ⟨fun direction ↦ (spaceInterior direction).1.le,
      fun direction ↦ (spaceInterior direction).2.le⟩
  apply matterCoordinateEquiv.injective
  simp [diracMatterSpatialGalerkinSynthesis_coordinates,
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_zeroOutside
      a b testCount _ space outsideInterior]

private theorem boundaryLiftActionResponse_integral_eq_restrict
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (test : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b testCount) :
    (∫ space,
      diracExteriorMatterEnergyPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
        (matterCoordinateEquiv.symm
          (boundaryLiftActionResponse (time, space)))
        (diracMatterSpatialGalerkinSynthesis
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount) test space)) =
      ∫ space,
        diracExteriorMatterEnergyPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
          (matterCoordinateEquiv.symm
            (boundaryLiftActionResponse (time, space)))
          (diracMatterSpatialGalerkinSynthesis
            (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
              a b testCount) test space)
        ∂volume.restrict (Icc a b) := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
  intro space outside
  rw [canonicalTrial_zero_outside_box a b testCount test space outside]
  simp [diracExteriorMatterEnergyPairing,
    diracExteriorMatterCoordinatePairing, dotProduct]

private theorem boundaryLiftActionResponse_restrictIntegral_eq_l2MassForm
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (testCount : ℕ)
    (test : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b testCount) :
    (∫ space,
      diracExteriorMatterEnergyPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
        (matterCoordinateEquiv.symm
          (boundaryLiftActionResponse (time, space)))
        (diracMatterSpatialGalerkinSynthesis
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount) test space)
      ∂volume.restrict (Icc a b)) =
      fixedP506L0CauchySafeMatterL2MassForm time a b C operatorBound
        (boundaryLiftActionResponseL2 time a b)
        (fixedP506L0CauchySafeMatterCanonicalSynthesis
          a b testCount test) := by
  rw [fixedP506L0CauchySafeMatterL2MassForm_eq_integral]
  have synthesisRead :
      ∀ᵐ space ∂volume.restrict (Icc a b),
        fixedP506L0CauchySafeMatterCanonicalSynthesis
            a b testCount test space =
          fixedMatterTrialCoordinates
            (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
              a b testCount)
            test space := by
    change ∀ᵐ space ∂volume.restrict (Icc a b),
      fixedMatterTrialL2
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount)
          (fun mode ↦
            (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
              a b testCount mode).continuous)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
            a b testCount)
          test a b space = _
    exact fixedMatterTrialL2_coe_ae
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
        a b testCount)
      (fun mode ↦
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
          a b testCount mode).continuous)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b testCount)
      test a b
  apply integral_congr_ae
  filter_upwards [
    boundaryLiftActionResponseL2_coe_ae time a b,
    synthesisRead] with space responseRead synthesisRead
  rw [responseRead, synthesisRead, matterFiberMassPairing_apply]
  unfold fixedMatterTrialCoordinates
  rw [matterCoordinateEquiv.symm_apply_apply]

theorem boundaryLiftStiffnessFunctional_eq_l2MassForm
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (testCount : ℕ)
    (test : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b testCount) :
    boundaryLiftStiffnessFunctional a b testCount time test =
      fixedP506L0CauchySafeMatterL2MassForm time a b C operatorBound
        (-boundaryLiftActionResponseL2 time a b)
        (fixedP506L0CauchySafeMatterCanonicalSynthesis
          a b testCount test) := by
  let reverse := fun space : DiracMatterSpatialCoordinates ↦
    diracExteriorMatterEnergyPairing
      (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
      (diracMatterSpatialGalerkinSynthesis
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
          a b testCount) test space)
      (matterCoordinateEquiv.symm
        (boundaryLiftActionResponse (time, space)))
  let forward := fun space : DiracMatterSpatialCoordinates ↦
    diracExteriorMatterEnergyPairing
      (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
      (matterCoordinateEquiv.symm
        (boundaryLiftActionResponse (time, space)))
      (diracMatterSpatialGalerkinSynthesis
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
          a b testCount) test space)
  have pairingSymm : (∫ space, reverse space) = ∫ space, forward space := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun space ↦
      diracExteriorMatterEnergyPairing_symm _
        (fixedP506L0CauchySafeMatterWeakMassMatrix_posDef
          time space).isHermitian _ _
  have forwardRead :
      (∫ space, forward space) =
        fixedP506L0CauchySafeMatterL2MassForm time a b C operatorBound
          (boundaryLiftActionResponseL2 time a b)
          (fixedP506L0CauchySafeMatterCanonicalSynthesis
            a b testCount test) := by
    exact (boundaryLiftActionResponse_integral_eq_restrict
      time a b testCount test).trans
        (boundaryLiftActionResponse_restrictIntegral_eq_l2MassForm
          time a b C operatorBound testCount test)
  change (∫ space, -reverse space) = _
  calc
    (∫ space, -reverse space) = -(∫ space, reverse space) := integral_neg _
    _ = -(∫ space, forward space) := congrArg Neg.neg pairingSymm
    _ = -fixedP506L0CauchySafeMatterL2MassForm
        time a b C operatorBound
          (boundaryLiftActionResponseL2 time a b)
          (fixedP506L0CauchySafeMatterCanonicalSynthesis
            a b testCount test) := congrArg Neg.neg forwardRead
    _ = fixedP506L0CauchySafeMatterL2MassForm
        time a b C operatorBound
          (-boundaryLiftActionResponseL2 time a b)
          (fixedP506L0CauchySafeMatterCanonicalSynthesis
            a b testCount test) := by simp

def boundaryLiftMassProjectionCoefficient
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (testCount : ℕ) :
    FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount :=
  canonicalPhysicalMassProjectionCoefficient
    time a b C operatorBound testCount
      (boundaryLiftActionResponseL2 time a b)

def boundaryLiftMassProjection
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (testCount : ℕ) : CauchySafeMatterSpatialL2 a b :=
  canonicalPhysicalMassProjection time a b C operatorBound testCount
    (boundaryLiftActionResponseL2 time a b)

def boundaryLiftGeneratedCoefficient
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount :=
  boundaryLiftForcing a b testCount time

def boundaryLiftGeneratedSynthesis
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) : CauchySafeMatterSpatialL2 a b :=
  fixedP506L0CauchySafeMatterCanonicalSynthesis a b testCount
    (boundaryLiftGeneratedCoefficient time a b testCount)

theorem boundaryLiftGeneratedCoefficient_massEquation
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    galerkinWeakMassOperator
          (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount)
          time (boundaryLiftGeneratedCoefficient time a b testCount) +
        boundaryLiftStiffnessRiesz a b testCount time = 0 := by
  exact boundaryLiftForcing_massEquation a b testCount time

theorem boundaryLiftMassProjectionCoefficient_massLaw
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (testCount : ℕ)
    (test : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b testCount) :
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount time
        (boundaryLiftMassProjectionCoefficient
          time a b C operatorBound testCount) test =
      fixedP506L0CauchySafeMatterL2MassForm time a b C operatorBound
        (boundaryLiftActionResponseL2 time a b)
        (fixedP506L0CauchySafeMatterCanonicalSynthesis
          a b testCount test) := by
  exact canonicalPhysicalMassProjectionCoefficient_massLaw
    time a b C operatorBound testCount
      (boundaryLiftActionResponseL2 time a b) test

theorem boundaryLiftGeneratedCoefficient_massLaw
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (testCount : ℕ)
    (test : FixedP506L0CauchySafeMatterCanonicalCoefficient
      a b testCount) :
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount time
        (boundaryLiftGeneratedCoefficient time a b testCount) test =
      fixedP506L0CauchySafeMatterL2MassForm time a b C operatorBound
        (boundaryLiftActionResponseL2 time a b)
        (fixedP506L0CauchySafeMatterCanonicalSynthesis
          a b testCount test) := by
  have forcingEquation := boundaryLiftGeneratedCoefficient_massEquation
    time a b testCount
  have tested := congrArg (fun value ↦ inner ℝ value test) forcingEquation
  rw [inner_add_left, inner_zero_left,
    real_inner_galerkinWeakMassOperator,
    boundaryLiftStiffnessRiesz_pairing] at tested
  rw [boundaryLiftStiffnessFunctional_eq_l2MassForm
    time a b C operatorBound testCount test] at tested
  simp only [map_neg, neg_apply] at tested
  linarith

theorem boundaryLiftGeneratedCoefficient_eq_massProjectionCoefficient
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (testCount : ℕ) :
    boundaryLiftGeneratedCoefficient time a b testCount =
      boundaryLiftMassProjectionCoefficient
        time a b C operatorBound testCount := by
  have massInvertible :
      (galerkinWeakMassOperator
        (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount)
        time).IsInvertible :=
    fixedP506L0CauchySafeMatterWeakMassOperator_isInvertible
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
      (fun mode ↦
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
          a b testCount mode).continuous)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b testCount)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinSynthesis_faithful
        a b testCount)
      time
  apply massInvertible.injective
  apply ext_inner_right ℝ
  intro test
  rw [real_inner_galerkinWeakMassOperator,
    real_inner_galerkinWeakMassOperator]
  exact (boundaryLiftGeneratedCoefficient_massLaw
    time a b C operatorBound testCount test).trans
      (boundaryLiftMassProjectionCoefficient_massLaw
        time a b C operatorBound testCount test).symm

theorem boundaryLiftGeneratedCoefficient_synthesis_eq_massProjection
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (testCount : ℕ) :
    fixedP506L0CauchySafeMatterCanonicalSynthesis a b testCount
        (boundaryLiftGeneratedCoefficient time a b testCount) =
      boundaryLiftMassProjection time a b C operatorBound testCount := by
  unfold boundaryLiftMassProjection canonicalPhysicalMassProjection
  rw [boundaryLiftGeneratedCoefficient_eq_massProjectionCoefficient]
  rfl

theorem boundaryLiftGeneratedSynthesis_eq_massProjection
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time space‖ ≤ C)
    (testCount : ℕ) :
    boundaryLiftGeneratedSynthesis time a b testCount =
      boundaryLiftMassProjection time a b C operatorBound testCount := by
  exact boundaryLiftGeneratedCoefficient_synthesis_eq_massProjection
    time a b C operatorBound testCount

theorem boundaryLiftMassProjection_tendstoUniformlyOn
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (operatorBound : ∀ time ∈ Icc timeStart timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          time space‖ ≤ C) :
    TendstoUniformly
      (fun testCount (time : Icc timeStart timeEnd) ↦
        boundaryLiftMassProjection time.1 a b C
          (operatorBound time.1 time.2) testCount)
      (fun time ↦ boundaryLiftActionResponseL2 time.1 a b)
      atTop := by
  exact canonicalPhysicalMassProjection_tendstoUniformlyOn_of_continuous
    timeStart timeEnd timeOrder a b boxOrder C CNonnegative operatorBound
      (fun time ↦ boundaryLiftActionResponseL2 time a b)
      (boundaryLiftActionResponseL2_continuous a b)

/-- One source-owned bound controls the generated boundary forcing at every
canonical prefix and every time in the fixed Cauchy interval. -/
theorem exists_boundaryLiftGeneratedSynthesis_uniform_bound
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    ∃ δ : ℝ, 0 ≤ δ ∧ ∀ testCount : ℕ, ∀ time ∈ Icc 0 timeEnd,
      ‖boundaryLiftGeneratedSynthesis time a b testCount‖ ≤ δ := by
  obtain ⟨C, CNonnegative, operatorBound⟩ :=
    exists_fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateBoundOnBox
      0 timeEnd a b
  obtain ⟨κ, κPositive, pointwiseCoercivity⟩ :=
    exists_fixedP506L0CauchySafeMatterFiberMassCoercivityOnTimeSpaceBox
      0 timeEnd timeNonnegative a b boxOrder
  obtain ⟨R, responseBound⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn
      (boundaryLiftActionResponseL2_continuous a b).continuousOn
  have RNonnegative : 0 ≤ R := by
    exact (norm_nonneg (boundaryLiftActionResponseL2 0 a b)).trans
      (responseBound 0 (left_mem_Icc.mpr timeNonnegative))
  let δ :=
    (‖matterFiberMassRieszCoordinateBilinear‖ * C * R) / κ
  have δNonnegative : 0 ≤ δ := by
    unfold δ
    positivity
  refine ⟨δ, δNonnegative, ?_⟩
  intro testCount time timeMem
  have projectionBound := canonicalPhysicalMassProjection_norm_stable
    time a b C CNonnegative (operatorBound time timeMem) κ
      (pointwiseCoercivity time timeMem) testCount
      (boundaryLiftActionResponseL2 time a b)
  have responseNormBound :
      ‖boundaryLiftActionResponseL2 time a b‖ ≤ R :=
    responseBound time timeMem
  rw [boundaryLiftGeneratedSynthesis_eq_massProjection
    time a b C (operatorBound time timeMem) testCount]
  apply (le_div_iff₀ κPositive).2
  calc
    ‖canonicalPhysicalMassProjection
        time a b C (operatorBound time timeMem) testCount
        (boundaryLiftActionResponseL2 time a b)‖ * κ =
      κ * ‖canonicalPhysicalMassProjection
        time a b C (operatorBound time timeMem) testCount
        (boundaryLiftActionResponseL2 time a b)‖ := by ring
    _ ≤ ‖matterFiberMassRieszCoordinateBilinear‖ * C *
        ‖boundaryLiftActionResponseL2 time a b‖ := projectionBound
    _ ≤ ‖matterFiberMassRieszCoordinateBilinear‖ * C * R := by
      gcongr

theorem exists_boundaryLiftGeneratedSynthesis_uniform_crossLevel_bound
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (operatorBound : ∀ time ∈ Icc timeStart timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          time space‖ ≤ C)
    (epsilon : ℝ)
    (epsilonPositive : 0 < epsilon) :
    ∃ entry : ℕ, ∀ firstCount secondCount : ℕ,
      entry ≤ firstCount → firstCount ≤ secondCount →
      ∀ time : Icc timeStart timeEnd,
        ‖boundaryLiftGeneratedSynthesis time.1 a b firstCount -
            boundaryLiftGeneratedSynthesis time.1 a b secondCount‖ <
          epsilon := by
  have halfPositive : 0 < epsilon / 2 := half_pos epsilonPositive
  have convergence := boundaryLiftMassProjection_tendstoUniformlyOn
    timeStart timeEnd timeOrder a b boxOrder C CNonnegative operatorBound
  have eventuallyClose : ∀ᶠ testCount in atTop,
      ∀ time : Icc timeStart timeEnd,
        dist (boundaryLiftActionResponseL2 time.1 a b)
          (boundaryLiftMassProjection time.1 a b C
            (operatorBound time.1 time.2) testCount) < epsilon / 2 :=
    (Metric.tendstoUniformly_iff.mp convergence)
      (epsilon / 2) halfPositive
  obtain ⟨entry, close⟩ := eventually_atTop.1 eventuallyClose
  refine ⟨entry, ?_⟩
  intro firstCount secondCount entryFirst firstSecond time
  have entrySecond : entry ≤ secondCount := entryFirst.trans firstSecond
  have firstClose := close firstCount entryFirst time
  have secondClose := close secondCount entrySecond time
  rw [boundaryLiftGeneratedSynthesis_eq_massProjection
      time.1 a b C (operatorBound time.1 time.2) firstCount,
    boundaryLiftGeneratedSynthesis_eq_massProjection
      time.1 a b C (operatorBound time.1 time.2) secondCount]
  rw [← dist_eq_norm]
  calc
    dist
        (boundaryLiftMassProjection time.1 a b C
          (operatorBound time.1 time.2) firstCount)
        (boundaryLiftMassProjection time.1 a b C
          (operatorBound time.1 time.2) secondCount) ≤
      dist
          (boundaryLiftMassProjection time.1 a b C
            (operatorBound time.1 time.2) firstCount)
          (boundaryLiftActionResponseL2 time.1 a b) +
        dist (boundaryLiftActionResponseL2 time.1 a b)
          (boundaryLiftMassProjection time.1 a b C
            (operatorBound time.1 time.2) secondCount) :=
      dist_triangle _ _ _
    _ < epsilon / 2 + epsilon / 2 :=
      add_lt_add (by simpa only [dist_comm] using firstClose) secondClose
    _ = epsilon := by ring

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineBoundaryForcing
