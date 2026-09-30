import H0mework.Physics.DiracEvolution.SafeCountableDenseActualization
import H0mework.Physics.DiracEvolution.SafeCanonicalGalerkinBasis

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterGeneratedLimitOccurrence

open Filter MeasureTheory Set
open StageNineCauchySafeMatterCountableDenseTestCarrier
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCountableDenseActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterFiniteL2MassRead
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakPairingCompactness
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakGalerkinEnergy
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineGeneratedWeakLimitActualization
open StageNineHolonomicField
open StageNineCountableWeakPairingCompactness
open scoped BoundedContinuousFunction Interval

noncomputable section

set_option autoImplicit false

/-- Exact lower occurrence generated from one approximation history: it keeps
the common subsequence and distributional action laws together with the
canonical time-indexed `L²` representative and its independence receipt. -/
structure FixedP506L0CauchySafeCountableDenseGeneratedLimitOccurrence
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (energyCap : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap)
    (_testEntry : ℕ → ℕ)
    (testCoefficient : ∀ approximationIndex (_test : ℕ),
      DiracMatterGalerkinCoefficient
        (approximation approximationIndex).modeCount) where
  commonLimit : ℕ → (Icc timeStart timeEnd : Set ℝ) →ᵇ ℝ
  subsequence : ℕ → ℕ
  subsequenceStrict : StrictMono subsequence
  pairingConvergence : ∀ test,
    TendstoUniformly
      (fun sequenceIndex (time : Icc timeStart timeEnd) ↦
        galerkinWeakTestPairing
          (fixedP506L0CauchySafeMatterWeakMassForm
            (approximation (subsequence sequenceIndex)).basis
            (fun mode ↦
              ((approximation (subsequence sequenceIndex)).basisRegular mode
                ).continuous)
            (approximation (subsequence sequenceIndex)).basisCompact)
          (approximation (subsequence sequenceIndex)).coefficient
          (testCoefficient (subsequence sequenceIndex) test) time.1)
        (commonLimit test) atTop
  endpointRateConvergence : ∀ test time
      (timeMem : time ∈ Icc timeStart timeEnd),
    Tendsto
      (fun sequenceIndex ↦
        ∫ candidateTime in timeStart..time,
          galerkinWeakTestPairingRate
            (fixedP506L0CauchySafeMatterWeakMassFormDerivative
              (approximation (subsequence sequenceIndex)).basis
              (approximation (subsequence sequenceIndex)).basisRegular
              (approximation (subsequence sequenceIndex)).basisCompact)
            (fixedP506L0CauchySafeMatterWeakStiffnessForm
              (approximation (subsequence sequenceIndex)).basis
              (approximation (subsequence sequenceIndex)).basisRegular
              (approximation (subsequence sequenceIndex)).basisCompact)
            (approximation (subsequence sequenceIndex)).coefficient
            (testCoefficient (subsequence sequenceIndex) test)
            candidateTime)
      atTop
      (nhds (commonLimit test ⟨time, timeMem⟩ -
        commonLimit test ⟨timeStart, left_mem_Icc.mpr timeOrder⟩))
  weightedRateConvergence : ∀ test (weight : ℝ → ℝ),
    ContDiff ℝ 1 weight →
      Tendsto
        (fun sequenceIndex ↦
          ∫ candidateTime in timeStart..timeEnd,
            weight candidateTime *
              galerkinWeakTestPairingRate
                (fixedP506L0CauchySafeMatterWeakMassFormDerivative
                  (approximation (subsequence sequenceIndex)).basis
                  (approximation (subsequence sequenceIndex)).basisRegular
                  (approximation (subsequence sequenceIndex)).basisCompact)
                (fixedP506L0CauchySafeMatterWeakStiffnessForm
                  (approximation (subsequence sequenceIndex)).basis
                  (approximation (subsequence sequenceIndex)).basisRegular
                  (approximation (subsequence sequenceIndex)).basisCompact)
                (approximation (subsequence sequenceIndex)).coefficient
                (testCoefficient (subsequence sequenceIndex) test)
                candidateTime)
        atTop
        (nhds (weight timeEnd *
            commonLimit test ⟨timeEnd, right_mem_Icc.mpr timeOrder⟩ -
          weight timeStart *
            commonLimit test ⟨timeStart, left_mem_Icc.mpr timeOrder⟩ -
          ∫ candidateTime in timeStart..timeEnd,
            deriv weight candidateTime *
              commonLimit test
                (projIcc timeStart timeEnd timeOrder candidateTime)))
  representative :
    Icc timeStart timeEnd → CauchySafeMatterSpatialL2 a b
  generatorPairing : ∀ time test,
    inner ℝ (representative time)
        (cauchySafeMatterSmoothCompactTestToL2 a b
          (cauchySafeMatterCanonicalInteriorDenseTest a b test)) =
      commonLimit test time
  representativeUnique : ∀ time candidate,
    (∀ test,
      inner ℝ candidate
          (cauchySafeMatterSmoothCompactTestToL2 a b
            (cauchySafeMatterCanonicalInteriorDenseTest a b test)) =
        commonLimit test time) →
      candidate = representative time

/-- The mother-action approximation history, eventual dense-test
representation, and uniform energy cap generate the complete lower limit
occurrence. -/
theorem nonempty_fixedP506L0CauchySafeCountableDenseGeneratedLimitOccurrence
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
            (testCoefficient approximationIndex test) point)) :
    Nonempty
      (FixedP506L0CauchySafeCountableDenseGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder approximation testEntry
        testCoefficient) := by
  obtain ⟨C, CNonnegative, operatorBound, B, BNonnegative, finiteReadBound⟩ :=
    exists_fixedModeUniformFiniteMassReadBoundOnBox timeStart timeEnd a b
      timeOrder boxOrder energyCap energyCapNonnegative
  obtain ⟨commonLimit, subsequence, subsequenceStrict, commonConvergence⟩ :=
    exists_fixedP506L0CauchySafeCommonWeakPairingSubsequence
      (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b)
      (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one a b)
      timeStart timeEnd a b timeOrder boxOrder energyCap energyCapNonnegative
      approximation testEntry testCoefficient testRepresentation
  have existsRepresentative (time : Icc timeStart timeEnd) :
      ∃ representative : CauchySafeMatterSpatialL2 a b,
        (∀ test,
          inner ℝ representative
              (cauchySafeMatterSmoothCompactTestToL2 a b
                (cauchySafeMatterCanonicalInteriorDenseTest a b test)) =
            commonLimit test time) ∧
          ∀ candidate : CauchySafeMatterSpatialL2 a b,
            (∀ test,
              inner ℝ candidate
                  (cauchySafeMatterSmoothCompactTestToL2 a b
                    (cauchySafeMatterCanonicalInteriorDenseTest a b test)) =
                commonLimit test time) →
              candidate = representative := by
    have fixedFiniteReadBound : ∀ approximationIndex test,
        ‖fixedP506L0CauchySafeCountableDenseFiniteMassRead C operatorBound
            approximation time.1 time.2 approximationIndex test‖ ≤
          B * ‖cauchySafeMatterSmoothCompactTestToL2 a b test‖ := by
      intro approximationIndex test
      exact finiteReadBound
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
        time.1 time.2 test
    obtain ⟨spanLimit, spanConvergence, spanPairing, spanUnique,
        generatorRecognition⟩ :=
      exists_fixedP506L0CauchySafeCountableDenseRieszActualizationAt
        approximation testEntry testCoefficient testRepresentation C
        operatorBound time.1 time.2 B fixedFiniteReadBound commonLimit
        subsequence subsequenceStrict (fun test ↦ (commonConvergence test).1)
    let spanFunctional : ℕ →
        CauchySafeMatterCanonicalInteriorTestSpan a b →ₗ[ℝ] ℝ :=
      fun approximationIndex ↦
        (fixedP506L0CauchySafeCountableDenseFiniteMassRead C operatorBound
          approximation time.1 time.2 approximationIndex).comp
          (Submodule.subtype (CauchySafeMatterCanonicalInteriorTestSpan a b))
    let representative := pointwiseLimitRieszActualization
      (cauchySafeMatterCanonicalInteriorTestSpanToL2 a b) spanFunctional
      subsequence spanLimit spanConvergence
    have generatorPairing : ∀ test,
        inner ℝ representative
            (cauchySafeMatterSmoothCompactTestToL2 a b
              (cauchySafeMatterCanonicalInteriorDenseTest a b test)) =
          commonLimit test time := by
      intro test
      calc
        _ = spanLimit
            ⟨cauchySafeMatterCanonicalInteriorDenseTest a b test,
              Submodule.subset_span (Set.mem_range_self test)⟩ :=
          spanPairing _
        _ = commonLimit test time := generatorRecognition test
    refine ⟨representative, generatorPairing, ?_⟩
    intro candidate candidatePairing
    apply (cauchySafeMatterCanonicalInteriorDenseTest_denseRange a b
      ).eq_of_inner_left ℝ
    intro test
    calc
      inner ℝ candidate
          (cauchySafeMatterSmoothCompactTestToL2 a b
            (cauchySafeMatterCanonicalInteriorDenseTest a b test)) =
          commonLimit test time := candidatePairing test
      _ = inner ℝ representative
          (cauchySafeMatterSmoothCompactTestToL2 a b
            (cauchySafeMatterCanonicalInteriorDenseTest a b test)) :=
        (generatorPairing test).symm
  choose representative generatorPairing representativeUnique using
    existsRepresentative
  refine ⟨{
    commonLimit := commonLimit
    subsequence := subsequence
    subsequenceStrict := subsequenceStrict
    pairingConvergence := fun test ↦ (commonConvergence test).1
    endpointRateConvergence := fun test ↦ (commonConvergence test).2.1
    weightedRateConvergence := fun test ↦ (commonConvergence test).2.2
    representative := representative
    generatorPairing := generatorPairing
    representativeUnique := representativeUnique }⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterGeneratedLimitOccurrence
