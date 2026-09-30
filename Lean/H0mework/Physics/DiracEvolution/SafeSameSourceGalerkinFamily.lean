import H0mework.Physics.DiracEvolution.SafeGeneratedInitialTraceRecognition
import H0mework.Physics.DiracEvolution.SafeCanonicalGalerkinBasis

/-!
# Fixed P506 same-source weak Galerkin family

The fixed action-owned Galerkin approximations, their eventual dense-test
representations, and their exact source initial reads form one Type-valued
history.  Every generated common-limit occurrence therefore inherits the
same physical initial field.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSameSourceGalerkinFamily

open Filter MeasureTheory Set
open ProofFreeRicherAnholonomicSource
open StageNineCauchySafeMatterCountableDenseTestCarrier
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGeneratedInitialTraceRecognition
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGreenRateGeneratedLimitRecognition
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGreenRateL2Read
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterMassActualizedGeneratedLimitOccurrence
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakPairingCompactness
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeightedPhysicalWeakEquation
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterSpatialEnergyBalance
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

@[irreducible] def fixedP506L0CauchySafeMatterSpatialMassRead
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (field : CauchySafeMatterSpatialL2 a b)
    (test : ℕ) : ℝ :=
  ∫ space,
    matterFiberMassPairing
      (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
      (field space)
      ((cauchySafeMatterSmoothCompactTestToL2 a b
        (cauchySafeMatterCanonicalInteriorDenseTest a b test)) space)
    ∂volume.restrict (Icc a b)

/-- One fixed P506 Galerkin history with eventual exact test representation
and exact reads of a common physical initial field. -/
structure FixedP506L0CauchySafeSameSourceWeakGalerkinFamily
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (energyCap : ℝ) where
  approximation : ℕ →
    FixedP506L0CauchySafeWeakGalerkinApproximation
      timeStart timeEnd a b energyCap
  testEntry : ℕ → ℕ
  testCoefficient : ∀ approximationIndex (_test : ℕ),
    DiracMatterGalerkinCoefficient
      (approximation approximationIndex).modeCount
  testRepresentation : ∀ approximationIndex test,
    testEntry test ≤ approximationIndex →
    cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test = fun point ↦
      matterCoordinateEquiv
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate
          (approximation approximationIndex).basis
          (testCoefficient approximationIndex test) point)
  initialField : CauchySafeMatterSpatialL2 a b
  initialReadExact : ∀ approximationIndex test,
    testEntry test ≤ approximationIndex →
      fixedP506L0CauchySafeMatterGalerkinInitialMassRead
        approximation testCoefficient test approximationIndex =
        fixedP506L0CauchySafeMatterSpatialMassRead
          timeStart a b initialField test

/-- Exact source reads make the full initial Galerkin history converge. -/
theorem FixedP506L0CauchySafeSameSourceWeakGalerkinFamily.initialRead_tendsto
    {timeStart timeEnd energyCap : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    (family : FixedP506L0CauchySafeSameSourceWeakGalerkinFamily
      timeStart timeEnd a b energyCap)
    (test : ℕ) :
    Tendsto (fixedP506L0CauchySafeMatterGalerkinInitialMassRead
      family.approximation family.testCoefficient test) atTop
      (nhds (fixedP506L0CauchySafeMatterSpatialMassRead
        timeStart a b family.initialField test)) := by
  exact
    fixedP506L0CauchySafeMatterGalerkinInitialMassRead_tendsto_of_eventually_exact
      family.approximation family.testEntry family.testCoefficient
      (fixedP506L0CauchySafeMatterSpatialMassRead
        timeStart a b family.initialField) family.initialReadExact test

/-- The same-source family generates the existing mass-actualized lower
occurrence. -/
theorem FixedP506L0CauchySafeSameSourceWeakGalerkinFamily.nonemptyOccurrence
    {timeStart timeEnd energyCap : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b)
    (energyCapNonnegative : 0 ≤ energyCap)
    (family : FixedP506L0CauchySafeSameSourceWeakGalerkinFamily
      timeStart timeEnd a b energyCap) :
    Nonempty
      (FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder family.approximation
        family.testEntry family.testCoefficient) := by
  exact
    nonempty_fixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
      timeStart timeEnd a b timeOrder boxOrder energyCap energyCapNonnegative
      family.approximation family.testEntry family.testCoefficient
      family.testRepresentation

/-- Every generated occurrence reads the source initial mass pairing. -/
theorem FixedP506L0CauchySafeSameSourceWeakGalerkinFamily.physicalInitialRead
    {timeStart timeEnd energyCap : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {timeOrder : timeStart ≤ timeEnd}
    (family : FixedP506L0CauchySafeSameSourceWeakGalerkinFamily
      timeStart timeEnd a b energyCap)
    (occurrence :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder family.approximation
        family.testEntry family.testCoefficient)
    (test : ℕ) :
    fixedP506L0CauchySafeMatterPhysicalMassRead occurrence test
        ⟨timeStart, left_mem_Icc.mpr timeOrder⟩ =
      fixedP506L0CauchySafeMatterSpatialMassRead
        timeStart a b family.initialField test := by
  exact
    fixedP506L0CauchySafeMatterPhysicalMassRead_initial_eq_of_history_tendsto
      timeStart timeEnd a b timeOrder energyCap family.approximation
      family.testEntry family.testCoefficient occurrence _
      family.initialRead_tendsto test

theorem fixedP506L0CauchySafeMatterSpatialMassRead_injective
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (first second : CauchySafeMatterSpatialL2 a b)
    (readEq : ∀ test,
      fixedP506L0CauchySafeMatterSpatialMassRead time a b first test =
        fixedP506L0CauchySafeMatterSpatialMassRead time a b second test) :
    first = second := by
  obtain ⟨C, _, operatorBound⟩ :=
    exists_fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateBoundOnBox
      time time a b
  have timeMem : time ∈ Icc time time := ⟨le_rfl, le_rfl⟩
  let initialOperatorBound := operatorBound time timeMem
  let massEquiv := fixedP506L0CauchySafeMatterL2MassEquiv
    time a b boxOrder C initialOperatorBound
  have imageEq : massEquiv first = massEquiv second := by
    apply (cauchySafeMatterCanonicalInteriorDenseTest_denseRange a b).eq_of_inner_left ℝ
    intro test
    let testL2 := cauchySafeMatterSmoothCompactTestToL2 a b
      (cauchySafeMatterCanonicalInteriorDenseTest a b test)
    calc
      inner ℝ (massEquiv first) testL2 =
          fixedP506L0CauchySafeMatterL2MassForm
            time a b C initialOperatorBound first testL2 :=
        fixedP506L0CauchySafeMatterL2MassEquiv_pairing
          time a b boxOrder C initialOperatorBound first testL2
      _ = fixedP506L0CauchySafeMatterSpatialMassRead
          time a b first test := by
        simpa only [fixedP506L0CauchySafeMatterSpatialMassRead] using
          fixedP506L0CauchySafeMatterL2MassForm_eq_integral
            time a b C initialOperatorBound first testL2
      _ = fixedP506L0CauchySafeMatterSpatialMassRead
          time a b second test := readEq test
      _ = fixedP506L0CauchySafeMatterL2MassForm
          time a b C initialOperatorBound second testL2 := by
        simpa only [fixedP506L0CauchySafeMatterSpatialMassRead] using
          (fixedP506L0CauchySafeMatterL2MassForm_eq_integral
            time a b C initialOperatorBound second testL2).symm
      _ = inner ℝ (massEquiv second) testL2 :=
        (fixedP506L0CauchySafeMatterL2MassEquiv_pairing
          time a b boxOrder C initialOperatorBound second testL2).symm
  exact massEquiv.injective imageEq

/-- The generated physical field has exactly the source initial slice. -/
theorem FixedP506L0CauchySafeSameSourceWeakGalerkinFamily.physicalInitialField
    {timeStart timeEnd energyCap : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {timeOrder : timeStart ≤ timeEnd}
    {boxOrder : a ≤ b}
    (family : FixedP506L0CauchySafeSameSourceWeakGalerkinFamily
      timeStart timeEnd a b energyCap)
    (occurrence :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder family.approximation
        family.testEntry family.testCoefficient) :
    occurrence.physicalActualization.physicalField
        ⟨timeStart, left_mem_Icc.mpr timeOrder⟩ =
      family.initialField := by
  apply fixedP506L0CauchySafeMatterSpatialMassRead_injective
    timeStart a b boxOrder
  intro test
  simpa only [fixedP506L0CauchySafeMatterPhysicalMassRead,
    fixedP506L0CauchySafeMatterSpatialMassRead] using
      family.physicalInitialRead occurrence test

/-- The generated physical field satisfies the weighted mother-action law
with the source initial read in the boundary term. -/
theorem FixedP506L0CauchySafeSameSourceWeakGalerkinFamily.weightedPhysicalWeakEquation
    {timeStart timeEnd energyCap : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {timeOrder : timeStart ≤ timeEnd}
    {boxOrder : a ≤ b}
    {energyCapNonnegative : 0 ≤ energyCap}
    (family : FixedP506L0CauchySafeSameSourceWeakGalerkinFamily
      timeStart timeEnd a b energyCap)
    (occurrence :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder family.approximation
        family.testEntry family.testCoefficient)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    (∫ time in timeStart..timeEnd,
        weight time *
          fixedP506L0CauchySafeMatterPhysicalGreenRate occurrence test time) =
      weight timeEnd * fixedP506L0CauchySafeMatterPhysicalMassRead occurrence
          test ⟨timeEnd, right_mem_Icc.mpr timeOrder⟩ -
        weight timeStart * fixedP506L0CauchySafeMatterSpatialMassRead
          timeStart a b family.initialField test -
        ∫ time in timeStart..timeEnd,
          deriv weight time * fixedP506L0CauchySafeMatterPhysicalMassRead
            occurrence test (projIcc timeStart timeEnd timeOrder time) := by
  rw [fixedP506L0CauchySafeMatterWeightedPhysicalWeakEquation
    timeStart timeEnd a b timeOrder boxOrder energyCap energyCapNonnegative
    family.approximation family.testEntry family.testCoefficient
    family.testRepresentation occurrence test weight weightRegular]
  rw [family.physicalInitialRead occurrence test]

/-- The same-source physical occurrence satisfies the Volterra endpoint law
with the generated source field as its initial read. -/
theorem FixedP506L0CauchySafeSameSourceWeakGalerkinFamily.physicalEndpointWeakEquation
    {timeStart timeEnd energyCap : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {timeOrder : timeStart ≤ timeEnd}
    {boxOrder : a ≤ b}
    {energyCapNonnegative : 0 ≤ energyCap}
    (family : FixedP506L0CauchySafeSameSourceWeakGalerkinFamily
      timeStart timeEnd a b energyCap)
    (occurrence :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder family.approximation
        family.testEntry family.testCoefficient)
    (test : ℕ)
    (time : ℝ)
    (timeMem : time ∈ Icc timeStart timeEnd) :
    (∫ candidateTime in timeStart..time,
        fixedP506L0CauchySafeMatterPhysicalGreenRate occurrence test
          candidateTime) =
      fixedP506L0CauchySafeMatterPhysicalMassRead occurrence test
          ⟨time, timeMem⟩ -
        fixedP506L0CauchySafeMatterSpatialMassRead
          timeStart a b family.initialField test := by
  rw [fixedP506L0CauchySafeMatterPhysicalEndpointWeakEquation
    timeStart timeEnd a b timeOrder boxOrder energyCap energyCapNonnegative
    family.approximation family.testEntry family.testCoefficient
    family.testRepresentation occurrence test time timeMem]
  rw [family.physicalInitialRead occurrence test]

/-- Two generated occurrences from the same history have the same physical
initial slice. -/
theorem FixedP506L0CauchySafeSameSourceWeakGalerkinFamily.physicalInitialField_eq
    {timeStart timeEnd energyCap : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {timeOrder : timeStart ≤ timeEnd}
    {boxOrder : a ≤ b}
    (family : FixedP506L0CauchySafeSameSourceWeakGalerkinFamily
      timeStart timeEnd a b energyCap)
    (first second :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder family.approximation
        family.testEntry family.testCoefficient) :
    first.physicalActualization.physicalField
        ⟨timeStart, left_mem_Icc.mpr timeOrder⟩ =
      second.physicalActualization.physicalField
        ⟨timeStart, left_mem_Icc.mpr timeOrder⟩ := by
  exact (family.physicalInitialField (boxOrder := boxOrder) first).trans
    (family.physicalInitialField (boxOrder := boxOrder) second).symm

/-- The physical difference of two common-limit occurrences from one
Galerkin history. -/
def FixedP506L0CauchySafeSameSourceWeakGalerkinFamily.physicalDifference
    {timeStart timeEnd energyCap : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {timeOrder : timeStart ≤ timeEnd}
    (family : FixedP506L0CauchySafeSameSourceWeakGalerkinFamily
      timeStart timeEnd a b energyCap)
    (first second :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder family.approximation
        family.testEntry family.testCoefficient)
    (time : Icc timeStart timeEnd) : CauchySafeMatterSpatialL2 a b :=
  first.physicalActualization.physicalField time -
    second.physicalActualization.physicalField time

/-- The same-history physical difference has zero initial data. -/
theorem FixedP506L0CauchySafeSameSourceWeakGalerkinFamily.physicalDifference_initial_eq_zero
    {timeStart timeEnd energyCap : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {timeOrder : timeStart ≤ timeEnd}
    {boxOrder : a ≤ b}
    (family : FixedP506L0CauchySafeSameSourceWeakGalerkinFamily
      timeStart timeEnd a b energyCap)
    (first second :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder family.approximation
        family.testEntry family.testCoefficient) :
    family.physicalDifference first second
        ⟨timeStart, left_mem_Icc.mpr timeOrder⟩ = 0 := by
  exact sub_eq_zero.mpr
    (family.physicalInitialField_eq (boxOrder := boxOrder) first second)

private theorem fixedP506L0CauchySafeMatterGreenRateL2Value_sub
    (testCoordinates : BasePoint → MatterCoordinateCarrier)
    (testRegular : ContDiff ℝ 1 testCoordinates)
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (first second : CauchySafeMatterSpatialL2 a b) :
    fixedP506L0CauchySafeMatterGreenRateL2Value
        testCoordinates testRegular time a b (first - second) =
      fixedP506L0CauchySafeMatterGreenRateL2Value
          testCoordinates testRegular time a b first -
        fixedP506L0CauchySafeMatterGreenRateL2Value
          testCoordinates testRegular time a b second := by
  exact map_sub
    (fixedP506L0CauchySafeMatterGreenRateL2Read
      testCoordinates testRegular time a b) first second

/-- The Green-rate read of the physical difference is the difference of the
two occurrence reads. -/
theorem FixedP506L0CauchySafeSameSourceWeakGalerkinFamily.physicalGreenRate_difference
    {timeStart timeEnd energyCap : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {timeOrder : timeStart ≤ timeEnd}
    (family : FixedP506L0CauchySafeSameSourceWeakGalerkinFamily
      timeStart timeEnd a b energyCap)
    (first second :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder family.approximation
        family.testEntry family.testCoefficient)
    (test : ℕ)
    (time : ℝ) :
    fixedP506L0CauchySafeMatterGreenRateL2Value
        (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
        (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one a b test)
        (projIcc timeStart timeEnd timeOrder time).1 a b
        (family.physicalDifference first second
          (projIcc timeStart timeEnd timeOrder time)) =
      fixedP506L0CauchySafeMatterPhysicalGreenRate first test time -
        fixedP506L0CauchySafeMatterPhysicalGreenRate second test time := by
  unfold fixedP506L0CauchySafeMatterPhysicalGreenRate
  unfold fixedP506L0CauchySafeMatterGreenRatePhysicalRead
  unfold FixedP506L0CauchySafeSameSourceWeakGalerkinFamily.physicalDifference
  rw [fixedP506L0CauchySafeMatterGreenRateL2Value_sub]

/-- The endpoint laws of two occurrences from one history subtract to a
source-free Volterra identity. -/
theorem FixedP506L0CauchySafeSameSourceWeakGalerkinFamily.physicalEndpointWeakEquation_difference
    {timeStart timeEnd energyCap : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {timeOrder : timeStart ≤ timeEnd}
    {boxOrder : a ≤ b}
    {energyCapNonnegative : 0 ≤ energyCap}
    (family : FixedP506L0CauchySafeSameSourceWeakGalerkinFamily
      timeStart timeEnd a b energyCap)
    (first second :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder family.approximation
        family.testEntry family.testCoefficient)
    (test : ℕ)
    (time : ℝ)
    (timeMem : time ∈ Icc timeStart timeEnd) :
    (∫ candidateTime in timeStart..time,
        fixedP506L0CauchySafeMatterPhysicalGreenRate first test
          candidateTime) -
      (∫ candidateTime in timeStart..time,
        fixedP506L0CauchySafeMatterPhysicalGreenRate second test
          candidateTime) =
      fixedP506L0CauchySafeMatterPhysicalMassRead first test ⟨time, timeMem⟩ -
        fixedP506L0CauchySafeMatterPhysicalMassRead second test
          ⟨time, timeMem⟩ := by
  have firstLaw := family.physicalEndpointWeakEquation
    (boxOrder := boxOrder)
    (energyCapNonnegative := energyCapNonnegative)
    first test time timeMem
  have secondLaw := family.physicalEndpointWeakEquation
    (boxOrder := boxOrder)
    (energyCapNonnegative := energyCapNonnegative)
    second test time timeMem
  rw [firstLaw, secondLaw]
  ring

/-- The same-history physical difference itself satisfies one source-free
Volterra endpoint equation. -/
theorem FixedP506L0CauchySafeSameSourceWeakGalerkinFamily.physicalDifference_endpointWeakEquation
    {timeStart timeEnd energyCap : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {timeOrder : timeStart ≤ timeEnd}
    {boxOrder : a ≤ b}
    {energyCapNonnegative : 0 ≤ energyCap}
    (family : FixedP506L0CauchySafeSameSourceWeakGalerkinFamily
      timeStart timeEnd a b energyCap)
    (first second :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder family.approximation
        family.testEntry family.testCoefficient)
    (test : ℕ)
    (time : ℝ)
    (timeMem : time ∈ Icc timeStart timeEnd) :
    (∫ candidateTime in timeStart..time,
        fixedP506L0CauchySafeMatterGreenRateL2Value
          (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
          (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one a b test)
          (projIcc timeStart timeEnd timeOrder candidateTime).1 a b
          (family.physicalDifference first second
            (projIcc timeStart timeEnd timeOrder candidateTime))) =
      fixedP506L0CauchySafeMatterPhysicalMassRead first test ⟨time, timeMem⟩ -
        fixedP506L0CauchySafeMatterPhysicalMassRead second test
          ⟨time, timeMem⟩ := by
  have firstIntegrable :=
    fixedP506L0CauchySafeMatterPhysicalGreenRate_intervalIntegrable
      timeStart timeEnd a b timeOrder boxOrder energyCap energyCapNonnegative
      family.approximation family.testEntry family.testCoefficient
      family.testRepresentation first test time timeMem
  have secondIntegrable :=
    fixedP506L0CauchySafeMatterPhysicalGreenRate_intervalIntegrable
      timeStart timeEnd a b timeOrder boxOrder energyCap energyCapNonnegative
      family.approximation family.testEntry family.testCoefficient
      family.testRepresentation second test time timeMem
  calc
    _ = ∫ candidateTime in timeStart..time,
        (fixedP506L0CauchySafeMatterPhysicalGreenRate first test candidateTime -
          fixedP506L0CauchySafeMatterPhysicalGreenRate second test candidateTime) := by
      apply intervalIntegral.integral_congr
      intro candidateTime _candidateTimeMem
      exact family.physicalGreenRate_difference first second test candidateTime
    _ = (∫ candidateTime in timeStart..time,
          fixedP506L0CauchySafeMatterPhysicalGreenRate first test candidateTime) -
        (∫ candidateTime in timeStart..time,
          fixedP506L0CauchySafeMatterPhysicalGreenRate second test candidateTime) :=
      intervalIntegral.integral_sub firstIntegrable secondIntegrable
    _ = fixedP506L0CauchySafeMatterPhysicalMassRead first test ⟨time, timeMem⟩ -
        fixedP506L0CauchySafeMatterPhysicalMassRead second test
          ⟨time, timeMem⟩ :=
      family.physicalEndpointWeakEquation_difference
        (boxOrder := boxOrder)
        (energyCapNonnegative := energyCapNonnegative)
        first second test time timeMem

/-- Subtracting two generated weighted laws from the same history cancels
the source boundary term exactly. -/
theorem FixedP506L0CauchySafeSameSourceWeakGalerkinFamily.weightedPhysicalWeakEquation_difference
    {timeStart timeEnd energyCap : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    {timeOrder : timeStart ≤ timeEnd}
    {boxOrder : a ≤ b}
    {energyCapNonnegative : 0 ≤ energyCap}
    (family : FixedP506L0CauchySafeSameSourceWeakGalerkinFamily
      timeStart timeEnd a b energyCap)
    (first second :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder family.approximation
        family.testEntry family.testCoefficient)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    (∫ time in timeStart..timeEnd,
        weight time *
          fixedP506L0CauchySafeMatterPhysicalGreenRate first test time) -
      (∫ time in timeStart..timeEnd,
        weight time *
          fixedP506L0CauchySafeMatterPhysicalGreenRate second test time) =
      weight timeEnd *
          (fixedP506L0CauchySafeMatterPhysicalMassRead first test
              ⟨timeEnd, right_mem_Icc.mpr timeOrder⟩ -
            fixedP506L0CauchySafeMatterPhysicalMassRead second test
              ⟨timeEnd, right_mem_Icc.mpr timeOrder⟩) -
        (∫ time in timeStart..timeEnd,
          deriv weight time * fixedP506L0CauchySafeMatterPhysicalMassRead
            first test (projIcc timeStart timeEnd timeOrder time)) +
        (∫ time in timeStart..timeEnd,
          deriv weight time * fixedP506L0CauchySafeMatterPhysicalMassRead
            second test (projIcc timeStart timeEnd timeOrder time)) := by
  have firstLaw := family.weightedPhysicalWeakEquation
    (boxOrder := boxOrder)
    (energyCapNonnegative := energyCapNonnegative)
    first test weight weightRegular
  have secondLaw := family.weightedPhysicalWeakEquation
    (boxOrder := boxOrder)
    (energyCapNonnegative := energyCapNonnegative)
    second test weight weightRegular
  rw [firstLaw, secondLaw]
  ring

end


end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSameSourceGalerkinFamily
