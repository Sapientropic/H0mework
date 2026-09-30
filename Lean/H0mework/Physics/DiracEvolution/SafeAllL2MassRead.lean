import H0mework.Physics.DiracEvolution.SafeMassActualizedGeneratedLimitOccurrence
import H0mework.Physics.DiracEvolution.SafeCanonicalGalerkinBasis

/-!
# Fixed P506 all-`L²` matter mass reads

The finite mother-action mass read extends uniquely from smooth compact tests
to every spatial `L²` test.  Uniform energy bounds promote common-subsequence
convergence on the countable generators to weak convergence on the full
Hilbert carrier, and the limit is recognized as the mass pairing of the
already actualized physical field.  This is a read transporter on the exact
generated-limit occurrence, not a new physical actual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterAllL2MassRead

open Filter MeasureTheory Set
open StageNineCauchySafeMatterCountableDenseTestCarrier
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCountableDenseActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterFiniteL2MassRead
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGeneratedLimitOccurrence
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterMassActualizedGeneratedLimitOccurrence
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakPairingCompactness
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterSpatialEnergyBalance
open StageNineGeneratedWeakLimitActualization
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

private structure FixedApproximationMassReadBoundData
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (energyCap : ℝ)
    (approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap) where
  C : ℝ
  operatorBound : ∀ time ∈ Icc timeStart timeEnd,
    ∀ space ∈ Icc a b,
      ‖matterFiberMassPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C
  B : ℝ
  BNonnegative : 0 ≤ B
  finiteReadBound : ∀ approximationIndex (time : Icc timeStart timeEnd) test,
    ‖fixedMatterFiniteMassRead C
        (approximation approximationIndex).basis
        (fun mode ↦
          ((approximation approximationIndex).basisRegular mode).continuous)
        (approximation approximationIndex).basisCompact
        ((approximation approximationIndex).coefficient time.1)
        time.1 a b (operatorBound time.1 time.2) test‖ ≤
      B * ‖cauchySafeMatterSmoothCompactTestToL2 a b test‖

private def fixedApproximationMassReadBoundData
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b)
    (energyCap : ℝ)
    (energyCapNonnegative : 0 ≤ energyCap)
    (approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap) :
    FixedApproximationMassReadBoundData
      timeStart timeEnd a b energyCap approximation := by
  let boundExistence := exists_fixedModeUniformFiniteMassReadBoundOnBox
    timeStart timeEnd a b timeOrder boxOrder energyCap energyCapNonnegative
  let C := Classical.choose boundExistence
  have CSpec := Classical.choose_spec boundExistence
  let operatorBound := Classical.choose CSpec.2
  have operatorBoundSpec := Classical.choose_spec CSpec.2
  let B := Classical.choose operatorBoundSpec
  have BSpec := Classical.choose_spec operatorBoundSpec
  exact {
    C := C
    operatorBound := operatorBound
    B := B
    BNonnegative := BSpec.1
    finiteReadBound := by
      intro approximationIndex time test
      exact BSpec.2
        (approximation approximationIndex).modeCount
        (approximation approximationIndex).basis
        (approximation approximationIndex).basisRegular
        (approximation approximationIndex).basisCompact
        (approximation approximationIndex).basisZeroOutside
        (approximation approximationIndex).coefficient
        (approximation approximationIndex).velocity
        (approximation approximationIndex).evolution
        (fun candidateTime candidateTimeMem ↦
          (approximation approximationIndex).weakEquation candidateTime
            candidateTimeMem
            ((approximation approximationIndex).coefficient candidateTime))
        (approximation approximationIndex).initialEnergyBound
        time.1 time.2 test }

def fixedP506L0CauchySafeAllL2MassRead
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b)
    (energyCap : ℝ)
    (energyCapNonnegative : 0 ≤ energyCap)
    (approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap)
    :
    ℕ → Icc timeStart timeEnd →
      CauchySafeMatterSpatialL2 a b →L[ℝ] ℝ :=
  let bound := fixedApproximationMassReadBoundData timeStart timeEnd a b
    timeOrder boxOrder energyCap energyCapNonnegative approximation
  fun approximationIndex time ↦
    denseTestFunctionalExtension
      (cauchySafeMatterSmoothCompactTestToL2 a b)
      (fixedMatterFiniteMassRead bound.C
        (approximation approximationIndex).basis
        (fun mode ↦
          ((approximation approximationIndex).basisRegular mode).continuous)
        (approximation approximationIndex).basisCompact
        ((approximation approximationIndex).coefficient time.1)
        time.1 a b (bound.operatorBound time.1 time.2))

theorem fixedP506L0CauchySafeAllL2MassRead_actionLaw
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b)
    (energyCap : ℝ)
    (energyCapNonnegative : 0 ≤ energyCap)
    (approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap)
    (approximationIndex : ℕ)
    (time : Icc timeStart timeEnd)
    (test : CauchySafeMatterSmoothCompactTest) :
    fixedP506L0CauchySafeAllL2MassRead timeStart timeEnd a b timeOrder
        boxOrder energyCap energyCapNonnegative approximation
        approximationIndex time
        (cauchySafeMatterSmoothCompactTestToL2 a b test) =
      ∫ space in Icc a b,
        matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time.1 space)
          (fixedMatterTrialCoordinates
            (approximation approximationIndex).basis
            ((approximation approximationIndex).coefficient time.1) space)
          ((test : DiracMatterSpatialCoordinates → MatterCoordinateCarrier)
            space) := by
  let bound := fixedApproximationMassReadBoundData timeStart timeEnd a b
    timeOrder boxOrder energyCap energyCapNonnegative approximation
  calc
    _ = fixedMatterFiniteMassRead bound.C
          (approximation approximationIndex).basis
          (fun mode ↦
            ((approximation approximationIndex).basisRegular mode).continuous)
          (approximation approximationIndex).basisCompact
          ((approximation approximationIndex).coefficient time.1)
          time.1 a b (bound.operatorBound time.1 time.2) test := by
        exact LinearMap.extendOfNorm_eq
          (cauchySafeMatterSmoothCompactTestToL2_denseRange a b)
          ⟨bound.B, bound.finiteReadBound approximationIndex time⟩ test
    _ = _ := fixedMatterFiniteMassRead_eq_integral bound.C
      (approximation approximationIndex).basis
      (fun mode ↦
        ((approximation approximationIndex).basisRegular mode).continuous)
      (approximation approximationIndex).basisCompact
      ((approximation approximationIndex).coefficient time.1)
      time.1 a b (bound.operatorBound time.1 time.2) test

theorem fixedP506L0CauchySafeAllL2MassRead_weakConvergence
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
    (generatedLimit :
      FixedP506L0CauchySafeCountableDenseGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder approximation testEntry
        testCoefficient)
    (time : Icc timeStart timeEnd)
    (test : CauchySafeMatterSpatialL2 a b) :
    Tendsto
      (fun sequenceIndex ↦
        fixedP506L0CauchySafeAllL2MassRead timeStart timeEnd a b timeOrder
          boxOrder energyCap energyCapNonnegative approximation
          (generatedLimit.subsequence sequenceIndex) time test)
      atTop
      (nhds (inner ℝ (generatedLimit.representative time) test)) := by
  let bound := fixedApproximationMassReadBoundData timeStart timeEnd a b
    timeOrder boxOrder energyCap energyCapNonnegative approximation
  have finiteReadNorm : ∀ approximationIndex candidateTime,
      ‖fixedP506L0CauchySafeAllL2MassRead timeStart timeEnd a b timeOrder
          boxOrder energyCap energyCapNonnegative approximation
          approximationIndex candidateTime‖ ≤ bound.B := by
    intro approximationIndex time
    exact LinearMap.opNorm_extendOfNorm_le
      (cauchySafeMatterSmoothCompactTestToL2_denseRange a b)
      bound.BNonnegative (bound.finiteReadBound approximationIndex time)
  have generatorConvergence : ∀ candidateTime generatorIndex,
      Tendsto
        (fun sequenceIndex ↦
          fixedP506L0CauchySafeAllL2MassRead timeStart timeEnd a b timeOrder
            boxOrder energyCap energyCapNonnegative approximation
            (generatedLimit.subsequence sequenceIndex) candidateTime
            (cauchySafeMatterSmoothCompactTestToL2 a b
              (cauchySafeMatterCanonicalInteriorDenseTest a b generatorIndex)))
        atTop
        (nhds (inner ℝ (generatedLimit.representative candidateTime)
          (cauchySafeMatterSmoothCompactTestToL2 a b
            (cauchySafeMatterCanonicalInteriorDenseTest a b generatorIndex)))) := by
    intro candidateTime generatorIndex
    have raw := fixedP506L0CauchySafeFiniteMassRead_generatorConvergence
      approximation testEntry testCoefficient testRepresentation bound.C
      bound.operatorBound generatedLimit.commonLimit
      generatedLimit.subsequence
      generatedLimit.subsequenceStrict
      generatedLimit.pairingConvergence
      candidateTime.1 candidateTime.2 generatorIndex
    rw [generatedLimit.generatorPairing candidateTime generatorIndex]
    apply raw.congr'
    exact Filter.Eventually.of_forall fun sequenceIndex ↦
      ((fixedP506L0CauchySafeAllL2MassRead_actionLaw timeStart timeEnd a b
        timeOrder boxOrder energyCap energyCapNonnegative approximation
        (generatedLimit.subsequence sequenceIndex) candidateTime
        (cauchySafeMatterCanonicalInteriorDenseTest a b generatorIndex)).trans
        (fixedMatterFiniteMassRead_eq_integral bound.C
          (approximation (generatedLimit.subsequence sequenceIndex)).basis
          (fun mode ↦
            ((approximation
              (generatedLimit.subsequence sequenceIndex)).basisRegular mode
              ).continuous)
          (approximation
            (generatedLimit.subsequence sequenceIndex)).basisCompact
          ((approximation
            (generatedLimit.subsequence sequenceIndex)).coefficient
              candidateTime.1)
          candidateTime.1 a b
          (bound.operatorBound candidateTime.1 candidateTime.2)
          (cauchySafeMatterCanonicalInteriorDenseTest a b generatorIndex)).symm).symm
  exact tendsto_apply_of_dense_generator_of_uniform_opNorm_bound
    (fun index ↦ cauchySafeMatterSmoothCompactTestToL2 a b
      (cauchySafeMatterCanonicalInteriorDenseTest a b index))
    (cauchySafeMatterCanonicalInteriorDenseTest_denseRange a b)
    (fun approximationIndex ↦
      fixedP506L0CauchySafeAllL2MassRead timeStart timeEnd a b timeOrder
        boxOrder energyCap energyCapNonnegative approximation
        approximationIndex time)
    generatedLimit.subsequence
    (innerSL ℝ (generatedLimit.representative time))
    bound.B bound.BNonnegative
    (fun index ↦ finiteReadNorm (generatedLimit.subsequence index) time)
    (generatorConvergence time) test

/-- The action law on the exact dense test carrier determines each finite
`L²` read uniquely.  Auxiliary norm bounds therefore cannot change the
authoritative output. -/
theorem fixedP506L0CauchySafeAllL2MassRead_eq_of_actionLaw
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b)
    (energyCap : ℝ)
    (energyCapNonnegative : 0 ≤ energyCap)
    (approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap)
    (approximationIndex : ℕ)
    (time : Icc timeStart timeEnd)
    (candidate : CauchySafeMatterSpatialL2 a b →L[ℝ] ℝ)
    (candidateActionLaw : ∀ test,
      candidate (cauchySafeMatterSmoothCompactTestToL2 a b test) =
        ∫ space in Icc a b,
          matterFiberMassPairing
            (fixedP506L0CauchySafeMatterWeakMassMatrix time.1 space)
            (fixedMatterTrialCoordinates
              (approximation approximationIndex).basis
              ((approximation approximationIndex).coefficient time.1) space)
            ((test : DiracMatterSpatialCoordinates →
              MatterCoordinateCarrier) space)) :
    candidate =
      fixedP506L0CauchySafeAllL2MassRead timeStart timeEnd a b timeOrder
        boxOrder energyCap energyCapNonnegative approximation
        approximationIndex time := by
  apply ContinuousLinearMap.ext
  intro ambientTest
  have functionEq : (candidate : CauchySafeMatterSpatialL2 a b → ℝ) =
      (fixedP506L0CauchySafeAllL2MassRead timeStart timeEnd a b timeOrder
        boxOrder energyCap energyCapNonnegative approximation
        approximationIndex time : CauchySafeMatterSpatialL2 a b → ℝ) := by
    apply (cauchySafeMatterSmoothCompactTestToL2_denseRange a b).equalizer
      candidate.continuous
      (fixedP506L0CauchySafeAllL2MassRead timeStart timeEnd a b timeOrder
        boxOrder energyCap energyCapNonnegative approximation
        approximationIndex time).continuous
    funext test
    exact (candidateActionLaw test).trans
      (fixedP506L0CauchySafeAllL2MassRead_actionLaw timeStart timeEnd a b
        timeOrder boxOrder energyCap energyCapNonnegative approximation
        approximationIndex time test).symm
  exact congrFun functionEq ambientTest

/-- The all-`L²` finite reads converge to the exact action-owned mass pairing
of the already actualized physical field. -/
theorem fixedP506L0CauchySafeAllL2MassRead_weakConvergence_physicalMass
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
    (time : Icc timeStart timeEnd)
    (test : CauchySafeMatterSpatialL2 a b) :
    Tendsto
      (fun sequenceIndex ↦
        fixedP506L0CauchySafeAllL2MassRead timeStart timeEnd a b timeOrder
          boxOrder energyCap energyCapNonnegative approximation
          (occurrence.generatedLimit.subsequence sequenceIndex) time test)
      atTop
      (nhds (∫ space,
        matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time.1 space)
          (occurrence.physicalActualization.physicalField time space)
          (test space)
        ∂volume.restrict (Icc a b))) := by
  rw [occurrence.physicalActualization.massLaw time test]
  exact fixedP506L0CauchySafeAllL2MassRead_weakConvergence
    timeStart timeEnd a b timeOrder boxOrder energyCap energyCapNonnegative
    approximation testEntry testCoefficient testRepresentation
    occurrence.generatedLimit time test

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterAllL2MassRead
