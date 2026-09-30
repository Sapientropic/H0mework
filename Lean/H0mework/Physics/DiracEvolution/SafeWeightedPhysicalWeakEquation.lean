import H0mework.Physics.DiracEvolution.SafeGreenRateGeneratedLimitRecognition
import H0mework.Physics.DiracEvolution.SafeWeakPairingCompactness
import H0mework.Physics.DiracEvolution.SafeCanonicalGalerkinBasis
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Fixed P506 weighted physical weak equation

The exact finite action rates converge along the generated common subsequence
to the Green-rate read of the uniquely mass-actualized physical field.  The
mode-uniform energy estimate supplies the dominator, so the inherited finite
weighted law becomes the physical distributional law on the same occurrence.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeightedPhysicalWeakEquation

open Filter MeasureTheory Set
open ProofFreeRicherAnholonomicSource
open StageNineCauchySafeMatterCountableDenseTestCarrier
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGeneratedLimitOccurrence
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGreenRateGeneratedLimitRecognition
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGreenRateL2Read
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterMassActualizedGeneratedLimitOccurrence
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyEstimate
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakPairingCompactness
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakGalerkinEnergy
open StageNineHolonomicField
open scoped Interval

noncomputable section

set_option autoImplicit false

def fixedP506L0CauchySafeMatterGalerkinRateSubsequence
    {timeStart timeEnd energyCap : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {timeOrder : timeStart ≤ timeEnd}
    {approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap}
    {testEntry : ℕ → ℕ}
    {testCoefficient : ∀ approximationIndex (_test : ℕ),
      DiracMatterGalerkinCoefficient
        (approximation approximationIndex).modeCount}
    (occurrence :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder approximation testEntry
        testCoefficient)
    (test sequenceIndex : ℕ)
    (time : ℝ) : ℝ :=
  let finite := approximation
    (occurrence.generatedLimit.subsequence sequenceIndex)
  galerkinWeakTestPairingRate
    (fixedP506L0CauchySafeMatterWeakMassFormDerivative finite.basis
      finite.basisRegular finite.basisCompact)
    (fixedP506L0CauchySafeMatterWeakStiffnessForm finite.basis
      finite.basisRegular finite.basisCompact)
    finite.coefficient
    (testCoefficient (occurrence.generatedLimit.subsequence sequenceIndex) test)
    time

def fixedP506L0CauchySafeMatterPhysicalGreenRate
    {timeStart timeEnd energyCap : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {timeOrder : timeStart ≤ timeEnd}
    {approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap}
    {testEntry : ℕ → ℕ}
    {testCoefficient : ∀ approximationIndex (_test : ℕ),
      DiracMatterGalerkinCoefficient
        (approximation approximationIndex).modeCount}
    (occurrence :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder approximation testEntry
        testCoefficient)
    (test : ℕ)
    (time : ℝ) : ℝ :=
  fixedP506L0CauchySafeMatterGreenRatePhysicalRead occurrence
    (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
    (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one a b test)
    (projIcc timeStart timeEnd timeOrder time)

def fixedP506L0CauchySafeMatterPhysicalMassRead
    {timeStart timeEnd energyCap : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {timeOrder : timeStart ≤ timeEnd}
    {approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap}
    {testEntry : ℕ → ℕ}
    {testCoefficient : ∀ approximationIndex (_test : ℕ),
      DiracMatterGalerkinCoefficient
        (approximation approximationIndex).modeCount}
    (occurrence :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder approximation testEntry
        testCoefficient)
    (test : ℕ)
    (time : Icc timeStart timeEnd) : ℝ :=
  ∫ space,
    matterFiberMassPairing
      (fixedP506L0CauchySafeMatterWeakMassMatrix time.1 space)
      (occurrence.physicalActualization.physicalField time space)
      ((cauchySafeMatterSmoothCompactTestToL2 a b
        (cauchySafeMatterCanonicalInteriorDenseTest a b test)) space)
    ∂volume.restrict (Icc a b)

theorem fixedP506L0CauchySafeMatterPhysicalMassRead_eq_commonLimit
    {timeStart timeEnd energyCap : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {timeOrder : timeStart ≤ timeEnd}
    {approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap}
    {testEntry : ℕ → ℕ}
    {testCoefficient : ∀ approximationIndex (_test : ℕ),
      DiracMatterGalerkinCoefficient
        (approximation approximationIndex).modeCount}
    (occurrence :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder approximation testEntry
        testCoefficient)
    (test : ℕ)
    (time : Icc timeStart timeEnd) :
    fixedP506L0CauchySafeMatterPhysicalMassRead occurrence test time =
      occurrence.generatedLimit.commonLimit test time := by
  unfold fixedP506L0CauchySafeMatterPhysicalMassRead
  rw [occurrence.physicalActualization.massLaw]
  exact occurrence.generatedLimit.generatorPairing time test

theorem fixedP506L0CauchySafeMatterGalerkinRateSubsequence_continuousOn
    {timeStart timeEnd energyCap : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {timeOrder : timeStart ≤ timeEnd}
    {approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap}
    {testEntry : ℕ → ℕ}
    {testCoefficient : ∀ approximationIndex (_test : ℕ),
      DiracMatterGalerkinCoefficient
        (approximation approximationIndex).modeCount}
    (occurrence :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder approximation testEntry
        testCoefficient)
    (test sequenceIndex : ℕ) :
    ContinuousOn
      (fixedP506L0CauchySafeMatterGalerkinRateSubsequence occurrence test
        sequenceIndex)
      (Icc timeStart timeEnd) := by
  exact (approximation
    (occurrence.generatedLimit.subsequence sequenceIndex)
    ).weakPairingRate_continuousOn
      (testCoefficient
        (occurrence.generatedLimit.subsequence sequenceIndex) test)

theorem fixedP506L0CauchySafeMatterGalerkinRateSubsequence_tendsto_physical
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b)
    (energyCap : ℝ)
    (energyCapNonnegative : 0 ≤ energyCap)
    (approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap)
    (testEntry : ℕ → ℕ)
    (testCoefficient : ∀ approximationIndex (_test : ℕ),
      DiracMatterGalerkinCoefficient
        (approximation approximationIndex).modeCount)
    (testRepresentation : ∀ approximationIndex test,
      testEntry test ≤ approximationIndex →
      cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test = fun point ↦
        matterCoordinateEquiv
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate
            (approximation approximationIndex).basis
            (testCoefficient approximationIndex test) point))
    (occurrence :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder approximation testEntry
        testCoefficient)
    (test : ℕ)
    (time : Icc timeStart timeEnd) :
    Tendsto
      (fun sequenceIndex ↦
        fixedP506L0CauchySafeMatterGalerkinRateSubsequence occurrence test
          sequenceIndex time.1)
      atTop
      (nhds (fixedP506L0CauchySafeMatterPhysicalGreenRate occurrence test
        time.1)) := by
  have greenConvergence :=
    fixedP506L0CauchySafeMatterGreenRateL2Read_weakConvergence_physicalField
      timeStart timeEnd a b timeOrder boxOrder energyCap energyCapNonnegative
      approximation testEntry testCoefficient testRepresentation occurrence
      (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
      (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one a b test) time
  have physicalEq :
      fixedP506L0CauchySafeMatterPhysicalGreenRate occurrence test time.1 =
        fixedP506L0CauchySafeMatterGreenRatePhysicalRead occurrence
          (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
          (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one a b test)
          time := by
    unfold fixedP506L0CauchySafeMatterPhysicalGreenRate
    rw [projIcc_of_mem timeOrder time.2]
  have greenConvergence' :
      Tendsto
        (fixedP506L0CauchySafeMatterGreenRateSubsequenceRead occurrence
          (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
          (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one a b test)
          time)
        atTop
        (nhds (fixedP506L0CauchySafeMatterPhysicalGreenRate occurrence test
          time.1)) :=
    (congrArg nhds physicalEq).symm ▸ greenConvergence
  apply greenConvergence'.congr'
  have eventuallyEntered : ∀ᶠ sequenceIndex : ℕ in atTop,
      testEntry test ≤ occurrence.generatedLimit.subsequence sequenceIndex :=
    occurrence.generatedLimit.subsequenceStrict.tendsto_atTop
      (eventually_ge_atTop (testEntry test))
  filter_upwards [eventuallyEntered] with sequenceIndex entered
  change fixedP506L0CauchySafeMatterGreenRateL2Read
      (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
      (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one a b test)
      time.1 a b
      (fixedP506L0CauchySafeMatterApproximationTrialL2
        (approximation
          (occurrence.generatedLimit.subsequence sequenceIndex)) time.1) =
    galerkinWeakTestPairingRate
      (fixedP506L0CauchySafeMatterWeakMassFormDerivative
        (approximation
          (occurrence.generatedLimit.subsequence sequenceIndex)).basis
        (approximation
          (occurrence.generatedLimit.subsequence sequenceIndex)).basisRegular
        (approximation
          (occurrence.generatedLimit.subsequence sequenceIndex)).basisCompact)
      (fixedP506L0CauchySafeMatterWeakStiffnessForm
        (approximation
          (occurrence.generatedLimit.subsequence sequenceIndex)).basis
        (approximation
          (occurrence.generatedLimit.subsequence sequenceIndex)).basisRegular
        (approximation
          (occurrence.generatedLimit.subsequence sequenceIndex)).basisCompact)
      (approximation
        (occurrence.generatedLimit.subsequence sequenceIndex)).coefficient
      (testCoefficient
        (occurrence.generatedLimit.subsequence sequenceIndex) test) time.1
  exact fixedP506L0CauchySafeMatterGreenRateL2Read_fixedTrial
    (approximation
      (occurrence.generatedLimit.subsequence sequenceIndex)).basis
    (approximation
      (occurrence.generatedLimit.subsequence sequenceIndex)).basisRegular
    (approximation
      (occurrence.generatedLimit.subsequence sequenceIndex)).basisCompact
    (approximation
      (occurrence.generatedLimit.subsequence sequenceIndex)).coefficient
    (testCoefficient
      (occurrence.generatedLimit.subsequence sequenceIndex) test)
    (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
    (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one a b test)
    (testRepresentation
      (occurrence.generatedLimit.subsequence sequenceIndex) test entered)
    time.1 a b boxOrder
    (approximation
      (occurrence.generatedLimit.subsequence sequenceIndex)).basisZeroOutside

theorem fixedP506L0CauchySafeMatterGalerkinRateSubsequence_eventually_uniformBound
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b)
    (energyCap : ℝ)
    (energyCapNonnegative : 0 ≤ energyCap)
    (approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap)
    (testEntry : ℕ → ℕ)
    (testCoefficient : ∀ approximationIndex (_test : ℕ),
      DiracMatterGalerkinCoefficient
        (approximation approximationIndex).modeCount)
    (testRepresentation : ∀ approximationIndex test,
      testEntry test ≤ approximationIndex →
      cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test = fun point ↦
        matterCoordinateEquiv
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate
            (approximation approximationIndex).basis
            (testCoefficient approximationIndex test) point))
    (occurrence :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder approximation testEntry
        testCoefficient)
    (test : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ sequenceIndex : ℕ in atTop,
      ∀ time ∈ Icc timeStart timeEnd,
        ‖fixedP506L0CauchySafeMatterGalerkinRateSubsequence occurrence test
          sequenceIndex time‖ ≤ L := by
  obtain ⟨L, LNonnegative, rateBound⟩ :=
    exists_fixedModeUniformGalerkinWeakTestPairingRateUniformBoundOnBox
      (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
      (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one a b test)
      timeStart timeEnd a b timeOrder boxOrder energyCap energyCapNonnegative
  refine ⟨L, LNonnegative, ?_⟩
  have eventuallyEntered : ∀ᶠ sequenceIndex : ℕ in atTop,
      testEntry test ≤ occurrence.generatedLimit.subsequence sequenceIndex :=
    occurrence.generatedLimit.subsequenceStrict.tendsto_atTop
      (eventually_ge_atTop (testEntry test))
  filter_upwards [eventuallyEntered] with sequenceIndex entered
  intro time timeMem
  exact rateBound
    (approximation
      (occurrence.generatedLimit.subsequence sequenceIndex)).modeCount
    (approximation
      (occurrence.generatedLimit.subsequence sequenceIndex)).basis
    (approximation
      (occurrence.generatedLimit.subsequence sequenceIndex)).basisRegular
    (approximation
      (occurrence.generatedLimit.subsequence sequenceIndex)).basisCompact
    (approximation
      (occurrence.generatedLimit.subsequence sequenceIndex)).basisZeroOutside
    (approximation
      (occurrence.generatedLimit.subsequence sequenceIndex)).coefficient
    (approximation
      (occurrence.generatedLimit.subsequence sequenceIndex)).velocity
    (testCoefficient
      (occurrence.generatedLimit.subsequence sequenceIndex) test)
    (approximation
      (occurrence.generatedLimit.subsequence sequenceIndex)).evolution
    (approximation
      (occurrence.generatedLimit.subsequence sequenceIndex)).weakEquation
    (testRepresentation
      (occurrence.generatedLimit.subsequence sequenceIndex) test entered)
    (approximation
      (occurrence.generatedLimit.subsequence sequenceIndex)).initialEnergyBound
    time timeMem

/-- On every source-anchored initial segment, the finite generated rates
converge to the Green read of the same physical occurrence. -/
theorem fixedP506L0CauchySafeMatterEndpointRate_tendsto_physicalGreenIntegral
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b)
    (energyCap : ℝ)
    (energyCapNonnegative : 0 ≤ energyCap)
    (approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap)
    (testEntry : ℕ → ℕ)
    (testCoefficient : ∀ approximationIndex (_test : ℕ),
      DiracMatterGalerkinCoefficient
        (approximation approximationIndex).modeCount)
    (testRepresentation : ∀ approximationIndex test,
      testEntry test ≤ approximationIndex →
      cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test = fun point ↦
        matterCoordinateEquiv
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate
            (approximation approximationIndex).basis
            (testCoefficient approximationIndex test) point))
    (occurrence :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder approximation testEntry
        testCoefficient)
    (test : ℕ)
    (time : ℝ)
    (timeMem : time ∈ Icc timeStart timeEnd) :
    Tendsto
      (fun sequenceIndex ↦ ∫ candidateTime in timeStart..time,
        fixedP506L0CauchySafeMatterGalerkinRateSubsequence occurrence test
          sequenceIndex candidateTime)
      atTop
      (nhds (∫ candidateTime in timeStart..time,
        fixedP506L0CauchySafeMatterPhysicalGreenRate occurrence test
          candidateTime)) := by
  obtain ⟨L, LNonnegative, eventualRateBound⟩ :=
    fixedP506L0CauchySafeMatterGalerkinRateSubsequence_eventually_uniformBound
      timeStart timeEnd a b timeOrder boxOrder energyCap energyCapNonnegative
      approximation testEntry testCoefficient testRepresentation occurrence test
  have intervalSubset : Ι timeStart time ⊆ Icc timeStart timeEnd := by
    intro candidateTime candidateTimeMem
    have endpointMem : candidateTime ∈ Icc timeStart time := by
      rw [← uIcc_of_le timeMem.1]
      exact uIoc_subset_uIcc candidateTimeMem
    exact ⟨endpointMem.1, endpointMem.2.trans timeMem.2⟩
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _candidateTime ↦ L)
  · exact Filter.Eventually.of_forall fun sequenceIndex ↦
      (fixedP506L0CauchySafeMatterGalerkinRateSubsequence_continuousOn
        occurrence test sequenceIndex).mono intervalSubset
        |>.aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [eventualRateBound] with sequenceIndex rateBound
    exact Filter.Eventually.of_forall fun candidateTime candidateTimeMem ↦ by
      exact rateBound candidateTime (intervalSubset candidateTimeMem)
  · exact continuous_const.continuousOn.intervalIntegrable_of_Icc timeMem.1
  · exact Filter.Eventually.of_forall fun candidateTime candidateTimeMem ↦ by
      let physicalTime : Icc timeStart timeEnd :=
        ⟨candidateTime, intervalSubset candidateTimeMem⟩
      exact fixedP506L0CauchySafeMatterGalerkinRateSubsequence_tendsto_physical
        timeStart timeEnd a b timeOrder boxOrder energyCap
        energyCapNonnegative approximation testEntry testCoefficient
        testRepresentation occurrence test physicalTime

/-- The Green-rate read of the generated physical field is integrable on
every source-anchored canonical initial segment. -/
theorem fixedP506L0CauchySafeMatterPhysicalGreenRate_intervalIntegrable
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b)
    (energyCap : ℝ)
    (energyCapNonnegative : 0 ≤ energyCap)
    (approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap)
    (testEntry : ℕ → ℕ)
    (testCoefficient : ∀ approximationIndex (_test : ℕ),
      DiracMatterGalerkinCoefficient
        (approximation approximationIndex).modeCount)
    (testRepresentation : ∀ approximationIndex test,
      testEntry test ≤ approximationIndex →
      cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test = fun point ↦
        matterCoordinateEquiv
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate
            (approximation approximationIndex).basis
            (testCoefficient approximationIndex test) point))
    (occurrence :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder approximation testEntry
        testCoefficient)
    (test : ℕ)
    (time : ℝ)
    (timeMem : time ∈ Icc timeStart timeEnd) :
    IntervalIntegrable
      (fixedP506L0CauchySafeMatterPhysicalGreenRate occurrence test)
      volume timeStart time := by
  obtain ⟨L, _LNonnegative, eventualRateBound⟩ :=
    fixedP506L0CauchySafeMatterGalerkinRateSubsequence_eventually_uniformBound
      timeStart timeEnd a b timeOrder boxOrder energyCap energyCapNonnegative
      approximation testEntry testCoefficient testRepresentation occurrence test
  have intervalSubset : Ioc timeStart time ⊆ Icc timeStart timeEnd := by
    intro candidateTime candidateTimeMem
    exact ⟨candidateTimeMem.1.le, candidateTimeMem.2.trans timeMem.2⟩
  rw [intervalIntegrable_iff, uIoc_of_le timeMem.1]
  apply Integrable.mono'
    ((continuous_const : Continuous (fun _candidateTime : ℝ ↦ L)).continuousOn
      |>.intervalIntegrable_of_Icc timeMem.1 |>.1)
  · apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter ℕ)
    · intro sequenceIndex
      exact
        (fixedP506L0CauchySafeMatterGalerkinRateSubsequence_continuousOn
          occurrence test sequenceIndex).mono intervalSubset
          |>.aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with candidateTime candidateTimeMem
      exact fixedP506L0CauchySafeMatterGalerkinRateSubsequence_tendsto_physical
        timeStart timeEnd a b timeOrder boxOrder energyCap
        energyCapNonnegative approximation testEntry testCoefficient
        testRepresentation occurrence test
        ⟨candidateTime, intervalSubset candidateTimeMem⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with candidateTime candidateTimeMem
    have convergence :=
      fixedP506L0CauchySafeMatterGalerkinRateSubsequence_tendsto_physical
        timeStart timeEnd a b timeOrder boxOrder energyCap
        energyCapNonnegative approximation testEntry testCoefficient
        testRepresentation occurrence test
        ⟨candidateTime, intervalSubset candidateTimeMem⟩
    apply le_of_tendsto convergence.norm
    filter_upwards [eventualRateBound] with sequenceIndex rateBound
    exact rateBound candidateTime (intervalSubset candidateTimeMem)

/-- The generated physical field inherits the finite Volterra endpoint law
on the same lower occurrence. -/
theorem fixedP506L0CauchySafeMatterPhysicalEndpointWeakEquation
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b)
    (energyCap : ℝ)
    (energyCapNonnegative : 0 ≤ energyCap)
    (approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap)
    (testEntry : ℕ → ℕ)
    (testCoefficient : ∀ approximationIndex (_test : ℕ),
      DiracMatterGalerkinCoefficient
        (approximation approximationIndex).modeCount)
    (testRepresentation : ∀ approximationIndex test,
      testEntry test ≤ approximationIndex →
      cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test = fun point ↦
        matterCoordinateEquiv
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate
            (approximation approximationIndex).basis
            (testCoefficient approximationIndex test) point))
    (occurrence :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder approximation testEntry
        testCoefficient)
    (test : ℕ)
    (time : ℝ)
    (timeMem : time ∈ Icc timeStart timeEnd) :
    (∫ candidateTime in timeStart..time,
        fixedP506L0CauchySafeMatterPhysicalGreenRate occurrence test
          candidateTime) =
      fixedP506L0CauchySafeMatterPhysicalMassRead occurrence test
          ⟨time, timeMem⟩ -
        fixedP506L0CauchySafeMatterPhysicalMassRead occurrence test
          ⟨timeStart, left_mem_Icc.mpr timeOrder⟩ := by
  have physicalConvergence :=
    fixedP506L0CauchySafeMatterEndpointRate_tendsto_physicalGreenIntegral
      timeStart timeEnd a b timeOrder boxOrder energyCap energyCapNonnegative
      approximation testEntry testCoefficient testRepresentation occurrence
      test time timeMem
  have generatedConvergence :=
    occurrence.generatedLimit.endpointRateConvergence test time timeMem
  have endpointEq := tendsto_nhds_unique physicalConvergence generatedConvergence
  simpa only [fixedP506L0CauchySafeMatterPhysicalMassRead_eq_commonLimit]
    using endpointEq

theorem fixedP506L0CauchySafeMatterWeightedRate_tendsto_physicalGreenIntegral
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b)
    (energyCap : ℝ)
    (energyCapNonnegative : 0 ≤ energyCap)
    (approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap)
    (testEntry : ℕ → ℕ)
    (testCoefficient : ∀ approximationIndex (_test : ℕ),
      DiracMatterGalerkinCoefficient
        (approximation approximationIndex).modeCount)
    (testRepresentation : ∀ approximationIndex test,
      testEntry test ≤ approximationIndex →
      cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test = fun point ↦
        matterCoordinateEquiv
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate
            (approximation approximationIndex).basis
            (testCoefficient approximationIndex test) point))
    (occurrence :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder approximation testEntry
        testCoefficient)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    Tendsto
      (fun sequenceIndex ↦ ∫ time in timeStart..timeEnd,
        weight time *
          fixedP506L0CauchySafeMatterGalerkinRateSubsequence occurrence test
            sequenceIndex time)
      atTop
      (nhds (∫ time in timeStart..timeEnd,
        weight time *
          fixedP506L0CauchySafeMatterPhysicalGreenRate occurrence test time)) := by
  obtain ⟨L, LNonnegative, eventualRateBound⟩ :=
    fixedP506L0CauchySafeMatterGalerkinRateSubsequence_eventually_uniformBound
      timeStart timeEnd a b timeOrder boxOrder energyCap energyCapNonnegative
      approximation testEntry testCoefficient testRepresentation occurrence test
  have intervalSubset : Ι timeStart timeEnd ⊆ Icc timeStart timeEnd := by
    rw [← uIcc_of_le timeOrder]
    exact uIoc_subset_uIcc
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun time ↦ ‖weight time‖ * L)
  · exact Filter.Eventually.of_forall fun sequenceIndex ↦
      (((weightRegular.continuous.continuousOn).mul
        (fixedP506L0CauchySafeMatterGalerkinRateSubsequence_continuousOn
          occurrence test sequenceIndex)).mono intervalSubset
        ).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [eventualRateBound] with sequenceIndex rateBound
    exact Filter.Eventually.of_forall fun time timeMem ↦ by
      simpa only [norm_mul] using
        mul_le_mul_of_nonneg_left (rateBound time (intervalSubset timeMem))
          (norm_nonneg (weight time))
  · exact (weightRegular.continuous.norm.mul continuous_const).continuousOn
      |>.intervalIntegrable_of_Icc timeOrder
  · exact Filter.Eventually.of_forall fun time timeMem ↦ by
      let physicalTime : Icc timeStart timeEnd :=
        ⟨time, intervalSubset timeMem⟩
      exact tendsto_const_nhds.mul
        (fixedP506L0CauchySafeMatterGalerkinRateSubsequence_tendsto_physical
          timeStart timeEnd a b timeOrder boxOrder energyCap
          energyCapNonnegative approximation testEntry testCoefficient
          testRepresentation occurrence test physicalTime)

theorem fixedP506L0CauchySafeMatterWeightedWeakEquation_commonLimit
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b)
    (energyCap : ℝ)
    (energyCapNonnegative : 0 ≤ energyCap)
    (approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap)
    (testEntry : ℕ → ℕ)
    (testCoefficient : ∀ approximationIndex (_test : ℕ),
      DiracMatterGalerkinCoefficient
        (approximation approximationIndex).modeCount)
    (testRepresentation : ∀ approximationIndex test,
      testEntry test ≤ approximationIndex →
      cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test = fun point ↦
        matterCoordinateEquiv
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate
            (approximation approximationIndex).basis
            (testCoefficient approximationIndex test) point))
    (occurrence :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder approximation testEntry
        testCoefficient)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    (∫ time in timeStart..timeEnd,
        weight time *
          fixedP506L0CauchySafeMatterPhysicalGreenRate occurrence test time) =
      weight timeEnd * occurrence.generatedLimit.commonLimit test
          ⟨timeEnd, right_mem_Icc.mpr timeOrder⟩ -
        weight timeStart * occurrence.generatedLimit.commonLimit test
          ⟨timeStart, left_mem_Icc.mpr timeOrder⟩ -
        ∫ time in timeStart..timeEnd,
          deriv weight time * occurrence.generatedLimit.commonLimit test
            (projIcc timeStart timeEnd timeOrder time) := by
  have physicalConvergence :=
    fixedP506L0CauchySafeMatterWeightedRate_tendsto_physicalGreenIntegral
      timeStart timeEnd a b timeOrder boxOrder energyCap energyCapNonnegative
      approximation testEntry testCoefficient testRepresentation occurrence
      test weight weightRegular
  have generatedConvergence :=
    occurrence.generatedLimit.weightedRateConvergence test weight weightRegular
  exact tendsto_nhds_unique physicalConvergence generatedConvergence

theorem fixedP506L0CauchySafeMatterWeightedPhysicalWeakEquation
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b)
    (energyCap : ℝ)
    (energyCapNonnegative : 0 ≤ energyCap)
    (approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap)
    (testEntry : ℕ → ℕ)
    (testCoefficient : ∀ approximationIndex (_test : ℕ),
      DiracMatterGalerkinCoefficient
        (approximation approximationIndex).modeCount)
    (testRepresentation : ∀ approximationIndex test,
      testEntry test ≤ approximationIndex →
      cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test = fun point ↦
        matterCoordinateEquiv
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate
            (approximation approximationIndex).basis
            (testCoefficient approximationIndex test) point))
    (occurrence :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder approximation testEntry
        testCoefficient)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    (∫ time in timeStart..timeEnd,
        weight time *
          fixedP506L0CauchySafeMatterPhysicalGreenRate occurrence test time) =
      weight timeEnd * fixedP506L0CauchySafeMatterPhysicalMassRead occurrence
          test ⟨timeEnd, right_mem_Icc.mpr timeOrder⟩ -
        weight timeStart * fixedP506L0CauchySafeMatterPhysicalMassRead
          occurrence test ⟨timeStart, left_mem_Icc.mpr timeOrder⟩ -
        ∫ time in timeStart..timeEnd,
          deriv weight time * fixedP506L0CauchySafeMatterPhysicalMassRead
            occurrence test (projIcc timeStart timeEnd timeOrder time) := by
  simpa only [fixedP506L0CauchySafeMatterPhysicalMassRead_eq_commonLimit]
    using fixedP506L0CauchySafeMatterWeightedWeakEquation_commonLimit
      timeStart timeEnd a b timeOrder boxOrder energyCap energyCapNonnegative
      approximation testEntry testCoefficient testRepresentation occurrence
      test weight weightRegular

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeightedPhysicalWeakEquation
