import H0mework.Physics.DiracEvolution.SafeGreenRateL2Read
import H0mework.Physics.DiracEvolution.SafeCanonicalGalerkinBasis

/-!
# Fixed P506 Green-rate generated-limit recognition

The exact common subsequence converges under the action-owned Green-rate read
to the same read of the uniquely mass-actualized physical field.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterGreenRateGeneratedLimitRecognition

open Filter MeasureTheory Set
open ProofFreeRicherAnholonomicSource
open StageNineCauchySafeMatterCountableDenseTestCarrier
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterAllL2MassRead
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterFiniteL2MassRead
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGeneratedLimitOccurrence
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGreenRateL2Read
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterMassActualizedGeneratedLimitOccurrence
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakPairingCompactness
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterSpatialEnergyBalance
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

def fixedP506L0CauchySafeMatterGreenRateSubsequenceRead
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
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (time : Icc timeStart timeEnd)
    (sequenceIndex : ℕ) : ℝ :=
  fixedP506L0CauchySafeMatterGreenRateL2Value testCoordinates testRegular
    time.1 a b
    (fixedP506L0CauchySafeMatterApproximationTrialL2
      (approximation (occurrence.generatedLimit.subsequence sequenceIndex))
      time.1)

def fixedP506L0CauchySafeMatterGreenRatePhysicalRead
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
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (time : Icc timeStart timeEnd) : ℝ :=
  fixedP506L0CauchySafeMatterGreenRateL2Value testCoordinates testRegular
    time.1 a b (occurrence.physicalActualization.physicalField time)

theorem fixedP506L0CauchySafeMatterGreenRateL2Read_weakConvergence_physicalField
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
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (time : Icc timeStart timeEnd) :
    Tendsto
      (fixedP506L0CauchySafeMatterGreenRateSubsequenceRead occurrence
        testCoordinates testRegular time)
      atTop
      (nhds (fixedP506L0CauchySafeMatterGreenRatePhysicalRead occurrence
        testCoordinates testRegular time)) := by
  let boundExistence :=
    exists_fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateBoundOnBox
      timeStart timeEnd a b
  let C := Classical.choose boundExistence
  have operatorBound : ∀ candidateTime ∈ Icc timeStart timeEnd,
      ∀ space ∈ Icc a b,
        ‖fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
          candidateTime space‖ ≤ C :=
    (Classical.choose_spec boundExistence).2
  let massTest := fixedP506L0CauchySafeMatterGreenRateMassTest
    testCoordinates testRegular time.1 a b boxOrder C
      (operatorBound time.1 time.2)
  let massReadSequence : ℕ → ℝ := fun sequenceIndex ↦
    fixedP506L0CauchySafeAllL2MassRead timeStart timeEnd a b timeOrder
      boxOrder energyCap energyCapNonnegative approximation
      (occurrence.generatedLimit.subsequence sequenceIndex) time massTest
  have convergence : Tendsto massReadSequence atTop
      (nhds (∫ space,
        matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time.1 space)
          (occurrence.physicalActualization.physicalField time space)
          (massTest space)
        ∂volume.restrict (Icc a b))) := by
    exact fixedP506L0CauchySafeAllL2MassRead_weakConvergence_physicalMass
      timeStart timeEnd a b timeOrder boxOrder energyCap energyCapNonnegative
      approximation testEntry testCoefficient testRepresentation occurrence
      time massTest
  let greenLimit :=
    fixedP506L0CauchySafeMatterGreenRateL2Read testCoordinates testRegular
      time.1 a b (occurrence.physicalActualization.physicalField time)
  have limitEq :
      (∫ space,
        matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time.1 space)
          (occurrence.physicalActualization.physicalField time space)
          (massTest space)
        ∂volume.restrict (Icc a b)) =
      greenLimit := by
    rw [← fixedP506L0CauchySafeMatterL2MassForm_eq_integral]
    exact fixedP506L0CauchySafeMatterL2MassForm_greenRateMassTest
      testCoordinates testRegular time.1 a b boxOrder C
        (operatorBound time.1 time.2)
        (occurrence.physicalActualization.physicalField time)
  have convergenceToGreen :
      Tendsto massReadSequence atTop (nhds greenLimit) :=
    (congrArg nhds limitEq) ▸ convergence
  have sequenceEq :
      massReadSequence =
        fixedP506L0CauchySafeMatterGreenRateSubsequenceRead occurrence
          testCoordinates testRegular time := by
    funext sequenceIndex
    change fixedP506L0CauchySafeAllL2MassRead timeStart timeEnd a b timeOrder
        boxOrder energyCap energyCapNonnegative approximation
          (occurrence.generatedLimit.subsequence sequenceIndex) time massTest =
      fixedP506L0CauchySafeMatterGreenRateL2Read testCoordinates testRegular
        time.1 a b
        (fixedP506L0CauchySafeMatterApproximationTrialL2
          (approximation
            (occurrence.generatedLimit.subsequence sequenceIndex)) time.1)
    have finiteReadEq := congrArg
      (fun read : CauchySafeMatterSpatialL2 a b →L[ℝ] ℝ ↦ read massTest)
      (fixedP506L0CauchySafeAllL2MassRead_eq_massForm
        timeStart timeEnd a b timeOrder boxOrder energyCap energyCapNonnegative
        approximation (occurrence.generatedLimit.subsequence sequenceIndex)
        time C (operatorBound time.1 time.2))
    calc
      _ = fixedP506L0CauchySafeMatterL2MassForm time.1 a b C
          (operatorBound time.1 time.2)
          (fixedMatterTrialL2
            (approximation
              (occurrence.generatedLimit.subsequence sequenceIndex)).basis
            (fun mode ↦
              ((approximation
                (occurrence.generatedLimit.subsequence sequenceIndex)
                ).basisRegular mode).continuous)
            (approximation
              (occurrence.generatedLimit.subsequence sequenceIndex)
              ).basisCompact
            ((approximation
              (occurrence.generatedLimit.subsequence sequenceIndex)
              ).coefficient time.1) a b)
          massTest := finiteReadEq
      _ = fixedP506L0CauchySafeMatterGreenRateL2Read testCoordinates testRegular
          time.1 a b
          (fixedMatterTrialL2
            (approximation
              (occurrence.generatedLimit.subsequence sequenceIndex)).basis
            (fun mode ↦
              ((approximation
                (occurrence.generatedLimit.subsequence sequenceIndex)
                ).basisRegular mode).continuous)
            (approximation
              (occurrence.generatedLimit.subsequence sequenceIndex)
              ).basisCompact
            ((approximation
              (occurrence.generatedLimit.subsequence sequenceIndex)
              ).coefficient time.1) a b) :=
        fixedP506L0CauchySafeMatterL2MassForm_greenRateMassTest
          testCoordinates testRegular time.1 a b boxOrder C
            (operatorBound time.1 time.2) _
      _ = _ := rfl
  have tendstoEq := congrArg
    (fun sequence : ℕ → ℝ ↦ Tendsto sequence atTop (nhds greenLimit)) sequenceEq
  exact tendstoEq ▸ convergenceToGreen

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterGreenRateGeneratedLimitRecognition
