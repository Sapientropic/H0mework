import H0mework.Physics.DiracEvolution.SafeCanonicalAffineUniformEnergy
import H0mework.Physics.DiracEvolution.SafeCanonicalSameSourceGalerkinFamily
import H0mework.Physics.DiracEvolution.CountableWeakPairingCompactness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Fixed P506/L0 canonical affine weak-limit occurrence

The source-owned affine correction history supplies its own finite action
paths.  Uniform physical `L²` control and exact tested action laws generate a
single common weak-limit occurrence for the canonical dense test family.
No approximation family, target limit, residual, or convergence certificate
is supplied to the producer.
-/

namespace SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineWeakLimitOccurrence

open MeasureTheory Set
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineBoundaryForcing
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineBoundaryStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineUniformEnergy
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalSameSourceGalerkinFamily
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterFiniteL2MassRead
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyEstimate
open StageNineDiracMatterGalerkinEvolution
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakGalerkinEnergy
open StageNineDiracMatterWeakGalerkinEvolution
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineHolonomicField
open StageNineCountableWeakPairingCompactness
open scoped BoundedContinuousFunction Interval

noncomputable section

set_option autoImplicit false

/-- A fixed affine forcing leg changes only the tested rate of the standard
Galerkin mass pairing. -/
theorem galerkinWeakTestPairing_hasDerivWithinAt_of_affineEquation
    {H : Type*}
    [NormedAddCommGroup H]
    [NormedSpace ℝ H]
    (massForm massDerivative : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (stiffnessForm : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (affineForcing : ℝ → H →L[ℝ] ℝ)
    (coefficient : ℝ → H)
    (velocity test : H)
    (carrier : Set ℝ)
    (time : ℝ)
    (massHasDeriv :
      HasDerivWithinAt massForm (massDerivative time) carrier time)
    (coefficientHasDeriv :
      HasDerivWithinAt coefficient velocity carrier time)
    (weakEquation :
      massForm time velocity test +
          stiffnessForm time (coefficient time) test +
          affineForcing time test = 0) :
    HasDerivWithinAt
      (galerkinWeakTestPairing massForm coefficient test)
      (galerkinWeakTestPairingRate massDerivative stiffnessForm coefficient
          test time - affineForcing time test)
      carrier time := by
  have testHasDeriv : HasDerivWithinAt
      (fun _candidateTime : ℝ ↦ test) 0 carrier time :=
    (hasDerivAt_const time test).hasDerivWithinAt
  have fullDerivative :=
    (massHasDeriv.clm_apply coefficientHasDeriv).clm_apply testHasDeriv
  have velocityPairing :
      massForm time velocity test =
        -stiffnessForm time (coefficient time) test -
          affineForcing time test := by
    linarith
  change HasDerivWithinAt
    (fun candidateTime ↦
      massForm candidateTime (coefficient candidateTime) test)
    _ carrier time
  apply fullDerivative.congr_deriv
  simp only [add_apply, map_zero, add_zero]
  rw [velocityPairing]
  unfold galerkinWeakTestPairingRate
  ring

structure CanonicalAffineWeakPairingPath (timeEnd : ℝ) where
  pairing : ℝ → ℝ
  rate : ℝ → ℝ
  derivative : ∀ time ∈ Icc 0 timeEnd,
    HasDerivWithinAt pairing (rate time) (Icc 0 timeEnd) time
  rateContinuousOn : ContinuousOn rate (Icc 0 timeEnd)

theorem CanonicalAffineWeakPairingPath.pairingContinuousOn
    {timeEnd : ℝ}
    (path : CanonicalAffineWeakPairingPath timeEnd) :
    ContinuousOn path.pairing (Icc 0 timeEnd) := by
  intro time timeMem
  exact (path.derivative time timeMem).continuousWithinAt

theorem CanonicalAffineWeakPairingPath.integral_rate
    {timeEnd : ℝ}
    (path : CanonicalAffineWeakPairingPath timeEnd)
    (time : ℝ)
    (timeMem : time ∈ Icc 0 timeEnd) :
    (∫ candidateTime in 0..time, path.rate candidateTime) =
      path.pairing time - path.pairing 0 := by
  have pairingDerivative : ∀ candidateTime ∈ Ioo 0 time,
      HasDerivAt path.pairing (path.rate candidateTime) candidateTime := by
    intro candidateTime candidateTimeMem
    have candidateTimeFull : candidateTime ∈ Icc 0 timeEnd :=
      ⟨candidateTimeMem.1.le, candidateTimeMem.2.le.trans timeMem.2⟩
    exact (path.derivative candidateTime candidateTimeFull).hasDerivAt
      (Icc_mem_nhds candidateTimeMem.1
        (candidateTimeMem.2.trans_le timeMem.2))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le timeMem.1
    (path.pairingContinuousOn.mono (Icc_subset_Icc le_rfl timeMem.2))
    pairingDerivative
    ((path.rateContinuousOn.mono (Icc_subset_Icc le_rfl timeMem.2)
      ).intervalIntegrable_of_Icc timeMem.1)

theorem CanonicalAffineWeakPairingPath.weighted_integral_rate
    {timeEnd : ℝ}
    (path : CanonicalAffineWeakPairingPath timeEnd)
    (timeNonnegative : 0 ≤ timeEnd)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    (∫ candidateTime in 0..timeEnd,
        weight candidateTime * path.rate candidateTime) =
      weight timeEnd * path.pairing timeEnd -
        weight 0 * path.pairing 0 -
        ∫ candidateTime in 0..timeEnd,
          deriv weight candidateTime * path.pairing candidateTime := by
  have pairingDerivative : ∀ candidateTime ∈ [[0, timeEnd]],
      HasDerivWithinAt path.pairing (path.rate candidateTime)
        [[0, timeEnd]] candidateTime := by
    intro candidateTime candidateTimeMem
    rw [uIcc_of_le timeNonnegative] at candidateTimeMem ⊢
    exact path.derivative candidateTime candidateTimeMem
  have weightDerivative : ∀ candidateTime ∈ [[0, timeEnd]],
      HasDerivWithinAt weight (deriv weight candidateTime)
        [[0, timeEnd]] candidateTime := by
    intro candidateTime _
    exact (weightRegular.differentiable (by norm_num)
      candidateTime).hasDerivAt.hasDerivWithinAt
  have derivWeightIntegrable : IntervalIntegrable (deriv weight) volume
      0 timeEnd :=
    weightRegular.continuous_deriv le_rfl |>.continuousOn
      |>.intervalIntegrable_of_Icc timeNonnegative
  have rateIntegrable : IntervalIntegrable path.rate volume 0 timeEnd :=
    path.rateContinuousOn.intervalIntegrable_of_Icc timeNonnegative
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    weightDerivative pairingDerivative derivWeightIntegrable rateIntegrable

def canonicalAffineCorrectionPairingPath
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount test : ℕ) :
    CanonicalAffineWeakPairingPath timeEnd where
  pairing := galerkinWeakTestPairing
    (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount)
    (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
      timeEnd timeNonnegative a b testCount)
    (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
      a b testCount test)
  rate := fun time ↦
    galerkinWeakTestPairingRate
        (fixedP506L0CauchySafeMatterWeakMassFormDerivative
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
            a b testCount)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
            a b testCount))
        (fixedP506L0CauchySafeMatterWeakStiffnessForm
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
            a b testCount)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
            a b testCount))
        (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
          timeEnd timeNonnegative a b testCount)
        (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
          a b testCount test)
        time -
      boundaryLiftStiffnessFunctional a b testCount time
        (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
          a b testCount test)
  derivative := by
    intro time timeMem
    let basis := cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount
    let basisRegular := cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular a b testCount
    let basisCompact := cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact a b testCount
    let coefficient := fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
      timeEnd timeNonnegative a b testCount
    let testCoefficient := fixedP506L0CauchySafeMatterCanonicalTestCoefficient
      a b testCount test
    have massAt : HasDerivAt
        (fixedP506L0CauchySafeMatterWeakMassForm basis
          (fun mode ↦ (basisRegular mode).continuous) basisCompact)
        (fixedP506L0CauchySafeMatterWeakMassFormDerivative
          basis basisRegular basisCompact time)
        time :=
      fixedP506L0CauchySafeMatterWeakMassForm_hasDerivAt
        basis basisRegular basisCompact time
    have massWithin : HasDerivWithinAt
        (fixedP506L0CauchySafeMatterWeakMassForm basis
          (fun mode ↦ (basisRegular mode).continuous) basisCompact)
        (fixedP506L0CauchySafeMatterWeakMassFormDerivative
          basis basisRegular basisCompact time)
        (Icc 0 timeEnd) time := by
      simpa using massAt.hasFDerivAt.hasFDerivWithinAt.hasDerivWithinAt
    have coefficientWithin : HasDerivWithinAt coefficient
        (boundaryLiftForcing a b testCount time +
          fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
            a b testCount time (coefficient time))
        (Icc 0 timeEnd) time :=
      fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve_evolution
        timeEnd timeNonnegative a b testCount time timeMem
    have weakEquation :
        fixedP506L0CauchySafeMatterWeakMassForm basis
              (fun mode ↦ (basisRegular mode).continuous) basisCompact time
              (boundaryLiftForcing a b testCount time +
                fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
                  a b testCount time (coefficient time)) testCoefficient +
            fixedP506L0CauchySafeMatterWeakStiffnessForm
              basis basisRegular basisCompact time
              (coefficient time) testCoefficient +
            boundaryLiftStiffnessFunctional
              a b testCount time testCoefficient = 0 := by
      exact fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve_weakEquation
        timeEnd timeNonnegative a b testCount time timeMem testCoefficient
    have generated := galerkinWeakTestPairing_hasDerivWithinAt_of_affineEquation
      (H := FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount)
      (fixedP506L0CauchySafeMatterWeakMassForm basis
        (fun mode ↦ (basisRegular mode).continuous) basisCompact)
      (fixedP506L0CauchySafeMatterWeakMassFormDerivative
        basis basisRegular basisCompact)
      (fixedP506L0CauchySafeMatterWeakStiffnessForm
        basis basisRegular basisCompact)
      (boundaryLiftStiffnessFunctional a b testCount)
      coefficient
      (boundaryLiftForcing a b testCount time +
        fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
          a b testCount time (coefficient time))
      testCoefficient (Icc 0 timeEnd) time massWithin coefficientWithin
      weakEquation
    exact generated
  rateContinuousOn := by
    let basis := cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount
    let basisRegular := cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular a b testCount
    let basisCompact := cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact a b testCount
    let coefficient := fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
      timeEnd timeNonnegative a b testCount
    let testCoefficient := fixedP506L0CauchySafeMatterCanonicalTestCoefficient
      a b testCount test
    have coefficientContinuousOn : ContinuousOn coefficient (Icc 0 timeEnd) := by
      intro time timeMem
      exact (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve_evolution
        timeEnd timeNonnegative a b testCount time timeMem).continuousWithinAt
    have massDerivativeContinuous : Continuous
        (fixedP506L0CauchySafeMatterWeakMassFormDerivative
          basis basisRegular basisCompact) :=
      (fixedP506L0CauchySafeMatterWeakMassForm_contDiff_one
        basis basisRegular basisCompact).continuous_deriv le_rfl
    have stiffnessContinuous : Continuous
        (fixedP506L0CauchySafeMatterWeakStiffnessForm
          basis basisRegular basisCompact) :=
      fixedP506L0CauchySafeMatterWeakStiffnessForm_continuous
        basis basisRegular basisCompact
    exact (((massDerivativeContinuous.continuousOn.clm_apply
      coefficientContinuousOn).clm_apply continuousOn_const).sub
      ((stiffnessContinuous.continuousOn.clm_apply coefficientContinuousOn
        ).clm_apply continuousOn_const)).sub
      ((boundaryLiftStiffnessFunctional_continuous
        a b testCount).continuousOn.clm_apply continuousOn_const)

theorem exists_canonicalAffineCorrectionPairing_uniform_bound
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ testCount : ℕ,
      cauchySafeMatterCanonicalInteriorTestEntry test ≤ testCount →
        ∀ time ∈ Icc 0 timeEnd,
          ‖(canonicalAffineCorrectionPairingPath
            timeEnd timeNonnegative a b testCount test).pairing time‖ ≤ B := by
  obtain ⟨C, CNonnegative, operatorBound⟩ :=
    exists_fixedMassPairingOperatorBoundOnBox
      0 timeEnd a b timeNonnegative boxOrder
  obtain ⟨R, RNonnegative, correctionBound⟩ :=
    exists_fixedP506L0CauchySafeMatterCanonicalAffineCorrection_uniform_bound
      timeEnd timeNonnegative a b boxOrder
  let denseTest := cauchySafeMatterCanonicalInteriorDenseTest a b test
  let testL2 := cauchySafeMatterSmoothCompactTestToL2 a b denseTest
  refine ⟨C * R * ‖testL2‖, by positivity, ?_⟩
  intro testCount entered time timeMem
  let basis := cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount
  let basisRegular := cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular a b testCount
  let basisCompact := cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact a b testCount
  let coefficient := fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
    timeEnd timeNonnegative a b testCount
  let testCoefficient := fixedP506L0CauchySafeMatterCanonicalTestCoefficient
    a b testCount test
  have testRepresentation : ∀ space,
      fixedMatterTrialCoordinates basis testCoefficient space =
        (denseTest : DiracMatterSpatialCoordinates → MatterCoordinateCarrier) space := by
    intro space
    unfold fixedMatterTrialCoordinates
    simp only [testCoefficient,
      fixedP506L0CauchySafeMatterCanonicalTestCoefficient, dif_pos entered]
    exact Classical.choose_spec
      (cauchySafeMatterCanonicalInteriorTest_eventualRepresentation
        a b testCount test entered) space
  have readEq := fixedMatterFiniteMassRead_eq_galerkinWeakTestPairing
    C basis (fun mode ↦ (basisRegular mode).continuous) basisCompact
    a b
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_zeroOutside
      a b testCount)
    coefficient testCoefficient time (operatorBound time timeMem)
    denseTest testRepresentation
  have readBound := fixedMatterFiniteMassRead_bound
    C basis (fun mode ↦ (basisRegular mode).continuous) basisCompact
    (coefficient time) time a b (operatorBound time timeMem) denseTest
  have coefficientBound :
      ‖fixedMatterTrialL2 basis (fun mode ↦ (basisRegular mode).continuous)
        basisCompact (coefficient time) a b‖ ≤ R := by
    have bound := correctionBound testCount time timeMem
    change ‖fixedMatterTrialL2 basis
      (fun mode ↦ (basisRegular mode).continuous) basisCompact
      (coefficient time) a b‖ ≤ R at bound
    exact bound
  change ‖galerkinWeakTestPairing
      (fixedP506L0CauchySafeMatterWeakMassForm basis
        (fun mode ↦ (basisRegular mode).continuous) basisCompact)
      coefficient testCoefficient time‖ ≤ C * R * ‖testL2‖
  rw [← readEq]
  exact readBound.trans (by
    change C * ‖fixedMatterTrialL2 basis
        (fun mode ↦ (basisRegular mode).continuous) basisCompact
        (coefficient time) a b‖ * ‖testL2‖ ≤ C * R * ‖testL2‖
    gcongr)

theorem exists_canonicalAffineCorrectionPairing_rate_uniform_bound
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ testCount : ℕ,
      cauchySafeMatterCanonicalInteriorTestEntry test ≤ testCount →
        ∀ time ∈ Icc 0 timeEnd,
          ‖(canonicalAffineCorrectionPairingPath
            timeEnd timeNonnegative a b testCount test).rate time‖ ≤ L := by
  let testCoordinates :=
    cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test
  obtain ⟨K, KNonnegative, standardRateBound⟩ :=
    exists_fixedModeUniformGalerkinWeakTestPairingRateBoundOnBox
      testCoordinates
      (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
        a b test)
      0 timeEnd a b timeNonnegative boxOrder
  obtain ⟨R, RNonnegative, correctionBound⟩ :=
    exists_fixedP506L0CauchySafeMatterCanonicalAffineCorrection_uniform_bound
      timeEnd timeNonnegative a b boxOrder
  obtain ⟨C, CNonnegative, operatorBound⟩ :=
    exists_fixedMassPairingOperatorBoundOnBox
      0 timeEnd a b timeNonnegative boxOrder
  obtain ⟨D, DNonnegative, forcingBound⟩ :=
    exists_boundaryLiftGeneratedSynthesis_uniform_bound
      timeEnd timeNonnegative a b boxOrder
  let denseTest := cauchySafeMatterCanonicalInteriorDenseTest a b test
  let testL2 := cauchySafeMatterSmoothCompactTestToL2 a b denseTest
  let L := K * (R ^ 2 + volume.real (Icc a b)) + C * D * ‖testL2‖
  have LNonnegative : 0 ≤ L := by
    unfold L
    positivity
  refine ⟨L, LNonnegative, ?_⟩
  intro testCount entered time timeMem
  let basis := cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount
  let basisRegular := cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular a b testCount
  let basisCompact := cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact a b testCount
  let coefficient := fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
    timeEnd timeNonnegative a b testCount
  let testCoefficient := fixedP506L0CauchySafeMatterCanonicalTestCoefficient
    a b testCount test
  have coefficientBound :
      ‖fixedMatterTrialL2 basis (fun mode ↦ (basisRegular mode).continuous)
        basisCompact (coefficient time) a b‖ ≤ R := by
    have bound := correctionBound testCount time timeMem
    change ‖fixedMatterTrialL2 basis
      (fun mode ↦ (basisRegular mode).continuous) basisCompact
      (coefficient time) a b‖ ≤ R at bound
    exact bound
  have coefficientSquareBound :
      (∫ space in Icc a b,
        ‖matterCoordinateEquiv
          (diracMatterSpatialGalerkinSynthesis basis (coefficient time)
            space)‖ ^ 2) ≤ R ^ 2 := by
    change (∫ space in Icc a b,
      ‖fixedMatterTrialCoordinates basis (coefficient time) space‖ ^ 2) ≤
        R ^ 2
    rw [← fixedMatterTrialL2_norm_sq basis
      (fun mode ↦ (basisRegular mode).continuous) basisCompact
      (coefficient time) a b]
    exact (sq_le_sq₀ (norm_nonneg _) RNonnegative).2 coefficientBound
  have standardBound := standardRateBound
    (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount a b testCount)
    basis basisRegular basisCompact
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_zeroOutside
      a b testCount)
    coefficient testCoefficient
    (fixedP506L0CauchySafeMatterCanonicalTestCoefficient_representation
      a b testCount test entered)
    time timeMem
  have standardBound' :
      ‖galerkinWeakTestPairingRate
        (fixedP506L0CauchySafeMatterWeakMassFormDerivative
          basis basisRegular basisCompact)
        (fixedP506L0CauchySafeMatterWeakStiffnessForm
          basis basisRegular basisCompact)
        coefficient testCoefficient time‖ ≤
        K * (R ^ 2 + volume.real (Icc a b)) := by
    have sumBound :
        (∫ space in Icc a b,
            ‖matterCoordinateEquiv
              (diracMatterSpatialGalerkinSynthesis basis (coefficient time)
                space)‖ ^ 2) + volume.real (Icc a b) ≤
          R ^ 2 + volume.real (Icc a b) := by
      simpa [add_comm] using
        add_le_add_right coefficientSquareBound (volume.real (Icc a b))
    exact standardBound.trans
      (mul_le_mul_of_nonneg_left sumBound KNonnegative)
  have testRepresentation : ∀ space,
      fixedMatterTrialCoordinates basis testCoefficient space =
        (denseTest : DiracMatterSpatialCoordinates → MatterCoordinateCarrier) space := by
    intro space
    unfold fixedMatterTrialCoordinates
    simp only [testCoefficient,
      fixedP506L0CauchySafeMatterCanonicalTestCoefficient, dif_pos entered]
    exact Classical.choose_spec
      (cauchySafeMatterCanonicalInteriorTest_eventualRepresentation
        a b testCount test entered) space
  have forcingReadEq := fixedMatterFiniteMassRead_eq_galerkinWeakTestPairing
    C basis (fun mode ↦ (basisRegular mode).continuous) basisCompact
    a b
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_zeroOutside
      a b testCount)
    (boundaryLiftForcing a b testCount) testCoefficient time
    (operatorBound time timeMem) denseTest testRepresentation
  have forcingReadBound := fixedMatterFiniteMassRead_bound
    C basis (fun mode ↦ (basisRegular mode).continuous) basisCompact
    (boundaryLiftForcing a b testCount time) time a b
    (operatorBound time timeMem) denseTest
  have forcingCoefficientBound :
      ‖fixedMatterTrialL2 basis (fun mode ↦ (basisRegular mode).continuous)
        basisCompact (boundaryLiftForcing a b testCount time) a b‖ ≤ D := by
    have bound := forcingBound testCount time timeMem
    change ‖fixedMatterTrialL2 basis
      (fun mode ↦ (basisRegular mode).continuous) basisCompact
      (boundaryLiftForcing a b testCount time) a b‖ ≤ D at bound
    exact bound
  have forcingPairingBound :
      ‖fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount time
        (boundaryLiftForcing a b testCount time) testCoefficient‖ ≤
        C * D * ‖testL2‖ := by
    change ‖galerkinWeakTestPairing
      (fixedP506L0CauchySafeMatterWeakMassForm basis
        (fun mode ↦ (basisRegular mode).continuous) basisCompact)
      (boundaryLiftForcing a b testCount) testCoefficient time‖ ≤ _
    rw [← forcingReadEq]
    exact forcingReadBound.trans (by
      change C * ‖fixedMatterTrialL2 basis
          (fun mode ↦ (basisRegular mode).continuous) basisCompact
          (boundaryLiftForcing a b testCount time) a b‖ * ‖testL2‖ ≤
        C * D * ‖testL2‖
      gcongr)
  have forcingEquation := boundaryLiftForcing_massEquation a b testCount time
  have forcingTested :=
    congrArg (fun value ↦ inner ℝ value testCoefficient) forcingEquation
  rw [inner_add_left, inner_zero_left,
    StageNineDiracMatterWeakGalerkinEvolution.real_inner_galerkinWeakMassOperator,
    boundaryLiftStiffnessRiesz_pairing] at forcingTested
  have affineForcingBound :
      ‖boundaryLiftStiffnessFunctional a b testCount time testCoefficient‖ ≤
        C * D * ‖testL2‖ := by
    have forcingEq :
        boundaryLiftStiffnessFunctional a b testCount time testCoefficient =
          -fixedP506L0CauchySafeMatterCanonicalWeakMassForm
            a b testCount time
            (boundaryLiftForcing a b testCount time) testCoefficient := by
      linarith
    rw [forcingEq, norm_neg]
    exact forcingPairingBound
  change ‖galerkinWeakTestPairingRate
      (fixedP506L0CauchySafeMatterWeakMassFormDerivative
        basis basisRegular basisCompact)
      (fixedP506L0CauchySafeMatterWeakStiffnessForm
        basis basisRegular basisCompact)
      coefficient testCoefficient time -
    boundaryLiftStiffnessFunctional a b testCount time testCoefficient‖ ≤ L
  calc
    _ ≤ ‖galerkinWeakTestPairingRate
          (fixedP506L0CauchySafeMatterWeakMassFormDerivative
            basis basisRegular basisCompact)
          (fixedP506L0CauchySafeMatterWeakStiffnessForm
            basis basisRegular basisCompact)
          coefficient testCoefficient time‖ +
        ‖boundaryLiftStiffnessFunctional
          a b testCount time testCoefficient‖ := norm_sub_le _ _
    _ ≤ K * (R ^ 2 + volume.real (Icc a b)) +
        C * D * ‖testL2‖ := add_le_add standardBound' affineForcingBound
    _ = L := rfl

def canonicalAffineCorrectionBoundedPairing
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount test : ℕ) :
    (Icc 0 timeEnd : Set ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun time ↦
      (canonicalAffineCorrectionPairingPath
        timeEnd timeNonnegative a b testCount test).pairing time.1,
      continuousOn_iff_continuous_restrict.mp
        (canonicalAffineCorrectionPairingPath
          timeEnd timeNonnegative a b testCount test).pairingContinuousOn⟩

@[simp] theorem canonicalAffineCorrectionBoundedPairing_apply
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount test : ℕ)
    (time : Icc 0 timeEnd) :
    canonicalAffineCorrectionBoundedPairing
        timeEnd timeNonnegative a b testCount test time =
      (canonicalAffineCorrectionPairingPath
        timeEnd timeNonnegative a b testCount test).pairing time.1 :=
  rfl

/-- The fixed source-owned affine correction history emits one common weak
limit occurrence for all canonical dense tests.  The occurrence records the
finite endpoint and weighted action laws; it does not accept a supplied
approximation family or limit. -/
theorem nonempty_canonicalAffineCorrectionWeakLimitOccurrence
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    Nonempty
      (CountableWeightedWeakLimitOccurrence timeNonnegative
        (canonicalAffineCorrectionBoundedPairing
          timeEnd timeNonnegative a b)
        (fun testCount test ↦
          (canonicalAffineCorrectionPairingPath
            timeEnd timeNonnegative a b testCount test).rate)
        cauchySafeMatterCanonicalInteriorTestEntry) := by
  have pairingBounds := fun test ↦
    exists_canonicalAffineCorrectionPairing_uniform_bound
      timeEnd timeNonnegative a b boxOrder test
  choose B BNonnegative pairingBound using pairingBounds
  have rateBounds := fun test ↦
    exists_canonicalAffineCorrectionPairing_rate_uniform_bound
      timeEnd timeNonnegative a b boxOrder test
  choose L LNonnegative rateBound using rateBounds
  have pairingLipschitz : ∀ testCount test,
      cauchySafeMatterCanonicalInteriorTestEntry test ≤ testCount →
        LipschitzWith (Real.toNNReal (L test))
          (canonicalAffineCorrectionBoundedPairing
            timeEnd timeNonnegative a b testCount test) := by
    intro testCount test entered
    apply LipschitzWith.of_dist_le_mul
    intro firstTime secondTime
    let path := canonicalAffineCorrectionPairingPath
      timeEnd timeNonnegative a b testCount test
    have differenceBound :=
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        path.derivative
        (rateBound test testCount entered)
        (convex_Icc (0 : ℝ) timeEnd)
        secondTime.2 firstTime.2
    rw [canonicalAffineCorrectionBoundedPairing_apply,
      canonicalAffineCorrectionBoundedPairing_apply]
    change dist (path.pairing firstTime.1) (path.pairing secondTime.1) ≤
      (Real.toNNReal (L test) : ℝ) * dist firstTime.1 secondTime.1
    simpa [Real.dist_eq,
      Real.coe_toNNReal (L test) (LNonnegative test)] using differenceBound
  have pairingBounded : ∀ testCount test,
      cauchySafeMatterCanonicalInteriorTestEntry test ≤ testCount →
        ∀ time,
          ‖canonicalAffineCorrectionBoundedPairing
            timeEnd timeNonnegative a b testCount test time‖ ≤ B test := by
    intro testCount test entered time
    exact pairingBound test testCount entered time.1 time.2
  apply exists_countableWeightedWeakLimitOccurrence_of_eventually_lipschitz
    timeNonnegative
    (canonicalAffineCorrectionBoundedPairing
      timeEnd timeNonnegative a b)
    (fun testCount test ↦
      (canonicalAffineCorrectionPairingPath
        timeEnd timeNonnegative a b testCount test).rate)
    cauchySafeMatterCanonicalInteriorTestEntry
    (fun test ↦ Real.toNNReal (L test)) B
    pairingLipschitz pairingBounded
  · intro testCount test time timeMem
    let path := canonicalAffineCorrectionPairingPath
      timeEnd timeNonnegative a b testCount test
    change (∫ candidateTime in 0..time, path.rate candidateTime) =
      canonicalAffineCorrectionBoundedPairing
          timeEnd timeNonnegative a b testCount test ⟨time, timeMem⟩ -
        canonicalAffineCorrectionBoundedPairing
          timeEnd timeNonnegative a b testCount test
            ⟨0, left_mem_Icc.mpr timeNonnegative⟩
    calc
      _ = path.pairing time - path.pairing 0 :=
        path.integral_rate time timeMem
      _ = _ := rfl
  · intro testCount test weight weightRegular
    let path := canonicalAffineCorrectionPairingPath
      timeEnd timeNonnegative a b testCount test
    have projectedIntegral :
        (∫ candidateTime in 0..timeEnd,
            deriv weight candidateTime * path.pairing candidateTime) =
          ∫ candidateTime in 0..timeEnd,
            deriv weight candidateTime *
              canonicalAffineCorrectionBoundedPairing
                timeEnd timeNonnegative a b testCount test
                (projIcc 0 timeEnd timeNonnegative candidateTime) := by
      apply intervalIntegral.integral_congr
      intro candidateTime candidateTimeMem
      rw [uIcc_of_le timeNonnegative] at candidateTimeMem
      apply congrArg (fun value : ℝ ↦ deriv weight candidateTime * value)
      rw [canonicalAffineCorrectionBoundedPairing_apply,
        projIcc_of_mem timeNonnegative candidateTimeMem]
    change (∫ candidateTime in 0..timeEnd,
        weight candidateTime * path.rate candidateTime) = _
    calc
      _ = weight timeEnd * path.pairing timeEnd -
          weight 0 * path.pairing 0 -
          ∫ candidateTime in 0..timeEnd,
            deriv weight candidateTime * path.pairing candidateTime :=
        path.weighted_integral_rate timeNonnegative weight weightRegular
      _ = _ := by
        rw [projectedIntegral]
        rfl

end

end SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineWeakLimitOccurrence
