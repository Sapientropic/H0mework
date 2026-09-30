import H0mework.Physics.DiracEvolution.SafeCanonicalAffineGreenAssembly
import H0mework.Physics.DiracEvolution.SafeGreenRateGeneratedLimitRecognition

/-!
# Fixed P506/L0 canonical affine Green generated-limit recognition

The source-generated canonical affine subsequence converges under every
physical Green-rate read to the same mass-actualized affine output.  On the
canonical dense tests this identifies the emitted correction rate with the
physical affine Green read after removing the fixed lift mass rate.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineGreenGeneratedLimitRecognition

open Filter MeasureTheory Set
open ProofFreeRicherAnholonomicSource
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineBoundaryStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineGreenAssembly
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineRieszActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineWeakLimitOccurrence
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterFiniteL2MassRead
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGreenRateL2Read
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterSpatialEnergyBalance
open StageNineGeneratedWeakLimitActualization
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

private theorem denseTestFunctionalExtension_apply
    {Test Hilbert : Type*}
    [AddCommGroup Test]
    [Module ℝ Test]
    [NormedAddCommGroup Hilbert]
    [InnerProductSpace ℝ Hilbert]
    [CompleteSpace Hilbert]
    (testEmbedding : Test →ₗ[ℝ] Hilbert)
    (functional : Test →ₗ[ℝ] ℝ)
    (testDense : DenseRange testEmbedding)
    (bound : ℝ)
    (functionalBound : ∀ test,
      ‖functional test‖ ≤ bound * ‖testEmbedding test‖)
    (test : Test) :
    denseTestFunctionalExtension testEmbedding functional
        (testEmbedding test) = functional test := by
  exact LinearMap.extendOfNorm_eq testDense ⟨bound, functionalBound⟩ test

def canonicalAffineCorrectionAllL2MassRead
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C)
    (testCount : ℕ)
    (time : Icc 0 timeEnd) :
    CauchySafeMatterSpatialL2 a b →L[ℝ] ℝ :=
  denseTestFunctionalExtension
    (cauchySafeMatterSmoothCompactTestToL2 a b)
    (canonicalAffineCorrectionFiniteMassRead
      timeEnd timeNonnegative a b C operatorBound testCount time)

theorem canonicalAffineCorrectionAllL2MassRead_weakConvergence
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b)
    (time : Icc 0 timeEnd)
    (test : CauchySafeMatterSpatialL2 a b) :
    Tendsto
      (fun sequenceIndex ↦
        canonicalAffineCorrectionAllL2MassRead
          timeEnd timeNonnegative a b occurrence.C occurrence.operatorBound
          (occurrence.weakLimit.subsequence sequenceIndex) time test)
      atTop
      (nhds (inner ℝ (occurrence.correctionMassRepresentative time) test)) := by
  obtain ⟨B, BNonnegative, finiteReadBound⟩ :=
    exists_canonicalAffineCorrectionFiniteMassRead_uniform_bound
      timeEnd timeNonnegative a b boxOrder occurrence.C
      occurrence.CNonnegative occurrence.operatorBound
  have functionalBound : ∀ sequenceIndex,
      ‖canonicalAffineCorrectionAllL2MassRead
          timeEnd timeNonnegative a b occurrence.C occurrence.operatorBound
          (occurrence.weakLimit.subsequence sequenceIndex) time‖ ≤ B := by
    intro sequenceIndex
    exact LinearMap.opNorm_extendOfNorm_le
      (cauchySafeMatterSmoothCompactTestToL2_denseRange a b)
      BNonnegative
      (finiteReadBound
        (occurrence.weakLimit.subsequence sequenceIndex) time)
  have generatorConvergence : ∀ generatorIndex,
      Tendsto
        (fun sequenceIndex ↦
          canonicalAffineCorrectionAllL2MassRead
            timeEnd timeNonnegative a b occurrence.C occurrence.operatorBound
            (occurrence.weakLimit.subsequence sequenceIndex) time
            (cauchySafeMatterSmoothCompactTestToL2 a b
              (cauchySafeMatterCanonicalInteriorDenseTest
                a b generatorIndex)))
        atTop
        (nhds (inner ℝ (occurrence.correctionMassRepresentative time)
          (cauchySafeMatterSmoothCompactTestToL2 a b
            (cauchySafeMatterCanonicalInteriorDenseTest
              a b generatorIndex)))) := by
    intro generatorIndex
    have raw := canonicalAffineCorrectionFiniteMassRead_generatorConvergence
      timeEnd timeNonnegative a b occurrence.C occurrence.operatorBound
      occurrence.weakLimit time generatorIndex
    have limitEq : occurrence.weakLimit.limit generatorIndex time =
        inner ℝ (occurrence.correctionMassRepresentative time)
          (cauchySafeMatterSmoothCompactTestToL2 a b
            (cauchySafeMatterCanonicalInteriorDenseTest
              a b generatorIndex)) :=
      (occurrence.correctionMassRepresentative_generatorPairing
        time generatorIndex).symm
    have rawAtPhysical : Tendsto
        (fun sequenceIndex ↦
          canonicalAffineCorrectionFiniteMassRead
            timeEnd timeNonnegative a b occurrence.C occurrence.operatorBound
            (occurrence.weakLimit.subsequence sequenceIndex) time
            (cauchySafeMatterCanonicalInteriorDenseTest
              a b generatorIndex))
        atTop
        (nhds (inner ℝ (occurrence.correctionMassRepresentative time)
          (cauchySafeMatterSmoothCompactTestToL2 a b
            (cauchySafeMatterCanonicalInteriorDenseTest
              a b generatorIndex)))) :=
      (congrArg nhds limitEq) ▸ raw
    apply rawAtPhysical.congr'
    exact Filter.Eventually.of_forall fun sequenceIndex ↦ by
      exact (denseTestFunctionalExtension_apply
        (cauchySafeMatterSmoothCompactTestToL2 a b)
        (canonicalAffineCorrectionFiniteMassRead
          timeEnd timeNonnegative a b occurrence.C occurrence.operatorBound
          (occurrence.weakLimit.subsequence sequenceIndex) time)
        (cauchySafeMatterSmoothCompactTestToL2_denseRange a b)
        B (finiteReadBound
          (occurrence.weakLimit.subsequence sequenceIndex) time)
        (cauchySafeMatterCanonicalInteriorDenseTest a b generatorIndex)).symm
  exact tendsto_apply_of_dense_generator_of_uniform_opNorm_bound
    (fun generatorIndex ↦
      cauchySafeMatterSmoothCompactTestToL2 a b
        (cauchySafeMatterCanonicalInteriorDenseTest a b generatorIndex))
    (cauchySafeMatterCanonicalInteriorDenseTest_denseRange a b)
    (fun testCount ↦ canonicalAffineCorrectionAllL2MassRead
      timeEnd timeNonnegative a b occurrence.C occurrence.operatorBound
      testCount time)
    occurrence.weakLimit.subsequence
    (innerSL ℝ (occurrence.correctionMassRepresentative time))
    B BNonnegative functionalBound generatorConvergence test

theorem canonicalAffineCorrectionAllL2MassRead_eq_massForm
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (operatorBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C)
    (testCount : ℕ)
    (time : Icc 0 timeEnd)
    (D : ℝ)
    (matrixBound : ∀ space ∈ Icc a b,
      ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        time.1 space‖ ≤ D) :
    canonicalAffineCorrectionAllL2MassRead
        timeEnd timeNonnegative a b C operatorBound testCount time =
      fixedP506L0CauchySafeMatterL2MassForm
        time.1 a b D matrixBound
        (canonicalAffineCorrectionL2
          timeEnd timeNonnegative a b testCount time.1) := by
  have boundData : ∃ B : ℝ, 0 ≤ B ∧ ∀ candidateCount
      (candidateTime : Icc 0 timeEnd) candidateTest,
      ‖canonicalAffineCorrectionFiniteMassRead
          timeEnd timeNonnegative a b C operatorBound
          candidateCount candidateTime candidateTest‖ ≤
        B * ‖cauchySafeMatterSmoothCompactTestToL2 a b candidateTest‖ :=
    exists_canonicalAffineCorrectionFiniteMassRead_uniform_bound
      timeEnd timeNonnegative a b boxOrder C CNonnegative operatorBound
  obtain ⟨B, _BNonnegative, finiteReadBound⟩ := boundData
  apply ContinuousLinearMap.ext
  intro ambientTest
  have functionEq :
      (canonicalAffineCorrectionAllL2MassRead
        timeEnd timeNonnegative a b C operatorBound testCount time :
          CauchySafeMatterSpatialL2 a b → ℝ) =
      (fixedP506L0CauchySafeMatterL2MassForm
        time.1 a b D matrixBound
        (canonicalAffineCorrectionL2
          timeEnd timeNonnegative a b testCount time.1) :
          CauchySafeMatterSpatialL2 a b → ℝ) := by
    apply (cauchySafeMatterSmoothCompactTestToL2_denseRange a b).equalizer
      (canonicalAffineCorrectionAllL2MassRead
        timeEnd timeNonnegative a b C operatorBound testCount time).continuous
      (fixedP506L0CauchySafeMatterL2MassForm
        time.1 a b D matrixBound
        (canonicalAffineCorrectionL2
          timeEnd timeNonnegative a b testCount time.1)).continuous
    funext test
    have massFormEq :=
      fixedP506L0CauchySafeMatterL2MassForm_eq_integral
        time.1 a b D matrixBound
        (canonicalAffineCorrectionL2
          timeEnd timeNonnegative a b testCount time.1)
        (cauchySafeMatterSmoothCompactTestToL2 a b test)
    calc
      canonicalAffineCorrectionAllL2MassRead
          timeEnd timeNonnegative a b C operatorBound testCount time
          (cauchySafeMatterSmoothCompactTestToL2 a b test) =
        canonicalAffineCorrectionFiniteMassRead
          timeEnd timeNonnegative a b C operatorBound testCount time test := by
            exact denseTestFunctionalExtension_apply
              (cauchySafeMatterSmoothCompactTestToL2 a b)
              (canonicalAffineCorrectionFiniteMassRead
                timeEnd timeNonnegative a b C operatorBound testCount time)
              (cauchySafeMatterSmoothCompactTestToL2_denseRange a b)
              B (finiteReadBound testCount time)
              test
      _ = ∫ space in Icc a b,
          matterFiberMassPairing
            (fixedP506L0CauchySafeMatterWeakMassMatrix time.1 space)
            (fixedMatterTrialCoordinates
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                a b testCount)
              (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
                timeEnd timeNonnegative a b testCount time.1)
              space)
            ((test : DiracMatterSpatialCoordinates → MatterCoordinateCarrier)
              space) := by
            exact fixedMatterFiniteMassRead_eq_integral C
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                a b testCount)
              (fun mode ↦
                (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
                  a b testCount mode).continuous)
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
                a b testCount)
              (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
                timeEnd timeNonnegative a b testCount time.1)
              time.1 a b (operatorBound time.1 time.2) test
      _ = ∫ space,
          matterFiberMassPairing
            (fixedP506L0CauchySafeMatterWeakMassMatrix time.1 space)
            (canonicalAffineCorrectionL2
              timeEnd timeNonnegative a b testCount time.1 space)
            ((cauchySafeMatterSmoothCompactTestToL2 a b test) space)
          ∂volume.restrict (Icc a b) := by
            apply integral_congr_ae
            filter_upwards [
              fixedMatterTrialL2_coe_ae
                (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                  a b testCount)
                (fun mode ↦
                  (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
                    a b testCount mode).continuous)
                (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
                  a b testCount)
                (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
                  timeEnd timeNonnegative a b testCount time.1)
                a b,
              (cauchySafeMatterSmoothCompactTest_memLp a b test).coeFn_toLp]
                with space trialEq testEq
            rw [show canonicalAffineCorrectionL2
                timeEnd timeNonnegative a b testCount time.1 space =
                fixedMatterTrialCoordinates
                  (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                    a b testCount)
                  (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
                    timeEnd timeNonnegative a b testCount time.1) space by
              exact trialEq]
            change _ = matterFiberMassPairing _ _
              (((cauchySafeMatterSmoothCompactTest_memLp a b test).toLp
                (test : DiracMatterSpatialCoordinates → MatterCoordinateCarrier))
                space)
            rw [testEq]
      _ = fixedP506L0CauchySafeMatterL2MassForm
          time.1 a b D matrixBound
          (canonicalAffineCorrectionL2
            timeEnd timeNonnegative a b testCount time.1)
          (cauchySafeMatterSmoothCompactTestToL2 a b test) := massFormEq.symm
  exact congrFun functionEq ambientTest

theorem canonicalAffineCorrectionGreenRate_weakConvergence
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b)
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (time : Icc 0 timeEnd) :
    Tendsto
      (fun sequenceIndex ↦
        fixedP506L0CauchySafeMatterGreenRateL2Read
          testCoordinates testRegular time.1 a b
          (canonicalAffineCorrectionL2
            timeEnd timeNonnegative a b
            (occurrence.weakLimit.subsequence sequenceIndex) time.1))
      atTop
      (nhds (fixedP506L0CauchySafeMatterGreenRateL2Read
        testCoordinates testRegular time.1 a b
        (occurrence.correctionPhysicalActualization.physicalField time))) := by
  let boundExistence :=
    exists_fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateBoundOnBox
      0 timeEnd a b
  let D := Classical.choose boundExistence
  have matrixBound : ∀ candidateTime ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          candidateTime space‖ ≤ D :=
    (Classical.choose_spec boundExistence).2
  let massTest := fixedP506L0CauchySafeMatterGreenRateMassTest
    testCoordinates testRegular time.1 a b boxOrder D
      (matrixBound time.1 time.2)
  let massReadSequence : ℕ → ℝ := fun sequenceIndex ↦
    canonicalAffineCorrectionAllL2MassRead
      timeEnd timeNonnegative a b occurrence.C occurrence.operatorBound
      (occurrence.weakLimit.subsequence sequenceIndex) time massTest
  have convergence : Tendsto massReadSequence atTop
      (nhds (inner ℝ (occurrence.correctionMassRepresentative time)
        massTest)) := by
    exact canonicalAffineCorrectionAllL2MassRead_weakConvergence
      timeEnd timeNonnegative a b boxOrder occurrence time massTest
  let greenLimit := fixedP506L0CauchySafeMatterGreenRateL2Read
    testCoordinates testRegular time.1 a b
    (occurrence.correctionPhysicalActualization.physicalField time)
  have limitEq :
      inner ℝ (occurrence.correctionMassRepresentative time) massTest =
        greenLimit := by
    calc
      inner ℝ (occurrence.correctionMassRepresentative time) massTest =
          ∫ space,
            matterFiberMassPairing
              (fixedP506L0CauchySafeMatterWeakMassMatrix time.1 space)
              (occurrence.correctionPhysicalActualization.physicalField
                time space)
              (massTest space)
            ∂volume.restrict (Icc a b) :=
        (occurrence.correctionPhysicalActualization.massLaw time massTest).symm
      _ = fixedP506L0CauchySafeMatterL2MassForm
          time.1 a b D (matrixBound time.1 time.2)
          (occurrence.correctionPhysicalActualization.physicalField time)
          massTest :=
        (fixedP506L0CauchySafeMatterL2MassForm_eq_integral
          time.1 a b D (matrixBound time.1 time.2)
          (occurrence.correctionPhysicalActualization.physicalField time)
          massTest).symm
      _ = greenLimit :=
        fixedP506L0CauchySafeMatterL2MassForm_greenRateMassTest
          testCoordinates testRegular time.1 a b boxOrder D
          (matrixBound time.1 time.2)
          (occurrence.correctionPhysicalActualization.physicalField time)
  have convergenceToGreen : Tendsto massReadSequence atTop
      (nhds greenLimit) :=
    (congrArg nhds limitEq) ▸ convergence
  have sequenceEq : massReadSequence = fun sequenceIndex ↦
      fixedP506L0CauchySafeMatterGreenRateL2Read
        testCoordinates testRegular time.1 a b
        (canonicalAffineCorrectionL2
          timeEnd timeNonnegative a b
          (occurrence.weakLimit.subsequence sequenceIndex) time.1) := by
    funext sequenceIndex
    have finiteReadEq := congrArg
      (fun read : CauchySafeMatterSpatialL2 a b →L[ℝ] ℝ ↦ read massTest)
      (canonicalAffineCorrectionAllL2MassRead_eq_massForm
        timeEnd timeNonnegative a b boxOrder occurrence.C
        occurrence.CNonnegative occurrence.operatorBound
        (occurrence.weakLimit.subsequence sequenceIndex) time D
        (matrixBound time.1 time.2))
    calc
      massReadSequence sequenceIndex =
          fixedP506L0CauchySafeMatterL2MassForm
            time.1 a b D (matrixBound time.1 time.2)
            (canonicalAffineCorrectionL2
              timeEnd timeNonnegative a b
              (occurrence.weakLimit.subsequence sequenceIndex) time.1)
            massTest := finiteReadEq
      _ = fixedP506L0CauchySafeMatterGreenRateL2Read
          testCoordinates testRegular time.1 a b
          (canonicalAffineCorrectionL2
            timeEnd timeNonnegative a b
            (occurrence.weakLimit.subsequence sequenceIndex) time.1) :=
        fixedP506L0CauchySafeMatterL2MassForm_greenRateMassTest
          testCoordinates testRegular time.1 a b boxOrder D
          (matrixBound time.1 time.2) _
  have tendstoEq := congrArg
    (fun sequence : ℕ → ℝ ↦ Tendsto sequence atTop (nhds greenLimit))
    sequenceEq
  exact tendstoEq ▸ convergenceToGreen

theorem canonicalAffineFiniteGreenRate_weakConvergence
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b)
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (time : Icc 0 timeEnd) :
    Tendsto
      (fun sequenceIndex ↦
        fixedP506L0CauchySafeMatterGreenRateL2Read
          testCoordinates testRegular time.1 a b
          (canonicalAffineFiniteMatterL2
            timeEnd timeNonnegative a b
            (occurrence.weakLimit.subsequence sequenceIndex) time.1))
      atTop
      (nhds (fixedP506L0CauchySafeMatterGreenRateL2Read
        testCoordinates testRegular time.1 a b
        (occurrence.affinePhysicalField time))) := by
  have correctionConvergence :=
    canonicalAffineCorrectionGreenRate_weakConvergence
      timeEnd timeNonnegative a b boxOrder occurrence
      testCoordinates testRegular time
  have withLift := correctionConvergence.const_add
    (fixedP506L0CauchySafeMatterGreenRateL2Read
      testCoordinates testRegular time.1 a b
      (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b))
  simpa [canonicalAffineFiniteMatterL2,
    FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence.affinePhysicalField,
    map_add] using withLift

theorem canonicalAffineCorrectionRate_weakConvergence_to_physicalGreen
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b)
    (test : ℕ)
    (time : Icc 0 timeEnd) :
    Tendsto
      (fun sequenceIndex ↦
        (canonicalAffineCorrectionPairingPath
          timeEnd timeNonnegative a b
          (occurrence.weakLimit.subsequence sequenceIndex) test).rate time.1)
      atTop
      (nhds (fixedP506L0CauchySafeMatterGreenRateL2Read
          (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
          (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
            a b test)
          time.1 a b (occurrence.affinePhysicalField time) -
        canonicalSourceLiftMassRate a b test time.1)) := by
  have greenConvergence := canonicalAffineFiniteGreenRate_weakConvergence
    timeEnd timeNonnegative a b boxOrder occurrence
    (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
    (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one a b test)
    time
  have shifted := greenConvergence.sub_const
    (canonicalSourceLiftMassRate a b test time.1)
  apply shifted.congr'
  have eventuallyEntered : ∀ᶠ sequenceIndex : ℕ in atTop,
      cauchySafeMatterCanonicalInteriorTestEntry test ≤
        occurrence.weakLimit.subsequence sequenceIndex :=
    occurrence.weakLimit.subsequenceStrict.tendsto_atTop
      (eventually_ge_atTop
        (cauchySafeMatterCanonicalInteriorTestEntry test))
  filter_upwards [eventuallyEntered] with sequenceIndex entered
  have finiteGreen := canonicalAffineFiniteMatterL2_greenRate
    timeEnd timeNonnegative a b boxOrder
    (occurrence.weakLimit.subsequence sequenceIndex) test entered time.1
  linarith

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineGreenGeneratedLimitRecognition
