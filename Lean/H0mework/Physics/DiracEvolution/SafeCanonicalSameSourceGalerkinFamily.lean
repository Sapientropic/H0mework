import H0mework.Physics.DiracEvolution.SafeCanonicalCrossLevelStability
import H0mework.Physics.DiracEvolution.SafeCanonicalFinitePropagator
import H0mework.Physics.DiracEvolution.SafeSameSourceGalerkinFamily

/-!
# Fixed P506 canonical same-source Galerkin family

The fixed source, canonical nested interior bases, exact mass projections, and
global finite action evolutions generate the entire approximation history.
No approximation family, target weak limit, residual, or convergence
certificate is supplied to this constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalSameSourceGalerkinFamily

open MeasureTheory Set
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalCrossLevelStability
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFinitePropagator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterFiniteL2MassRead
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGeneratedInitialTraceRecognition
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterMassActualizedGeneratedLimitOccurrence
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterSameSourceGalerkinFamily
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyEstimate
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakPairingCompactness
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterWeakGalerkinEnergy
open StageNineDiracMatterWeakGalerkinEvolution
open StageNineDiracMatterWeakSpatialGalerkinStiffness
open StageNineHolonomicField
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

noncomputable section

set_option autoImplicit false

/-- The finite curve selected from the source-owned global action evolution. -/
def fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    ℝ → FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount :=
  Classical.choose
    (exists_fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_on_Icc
      timeStart timeEnd timeOrder a b testCount)

theorem fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_initial
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    fixedP506L0CauchySafeMatterCanonicalCoefficientCurve timeStart timeEnd timeOrder a b testCount
        timeStart =
      fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
        timeStart a b testCount :=
  (Classical.choose_spec
    (exists_fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_on_Icc
      timeStart timeEnd timeOrder a b testCount)).1

theorem fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_evolution
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (time : ℝ)
    (timeMem : time ∈ Icc timeStart timeEnd) :
    HasDerivWithinAt
      (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve timeStart timeEnd timeOrder a b testCount)
      (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
        a b testCount time
        (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
          timeStart timeEnd timeOrder a b testCount time))
      (Icc timeStart timeEnd) time :=
  ((Classical.choose_spec
    (exists_fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_on_Icc
      timeStart timeEnd timeOrder a b testCount)).2 time timeMem).1

theorem fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_operatorEquation
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (time : ℝ)
    (timeMem : time ∈ Icc timeStart timeEnd) :
    galerkinWeakMassOperator
          (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount)
          time
          (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
            a b testCount time
            (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
              timeStart timeEnd timeOrder a b testCount time)) +
        fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator
          a b testCount time
          (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
            timeStart timeEnd timeOrder a b testCount time) = 0 :=
  ((Classical.choose_spec
    (exists_fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_on_Icc
      timeStart timeEnd timeOrder a b testCount)).2 time timeMem).2

/-- Any other finite curve generated by the same source action and initial
projection agrees with the selected curve throughout the source interval. -/
theorem fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_eqOn
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (other : ℝ →
      FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount)
    (otherInitial : other timeStart =
      fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
        timeStart a b testCount)
    (otherEvolution : ∀ time ∈ Icc timeStart timeEnd,
      HasDerivWithinAt other
        (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
          a b testCount time (other time))
        (Icc timeStart timeEnd) time) :
    EqOn
      (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
        timeStart timeEnd timeOrder a b testCount)
      other (Icc timeStart timeEnd) := by
  exact fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_eqOn_Icc
    timeStart timeEnd timeOrder a b testCount _ other
    (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_initial
      timeStart timeEnd timeOrder a b testCount)
    otherInitial
    (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_evolution
      timeStart timeEnd timeOrder a b testCount)
    otherEvolution

/-- The canonical approximation history is exactly the finite source-action
propagator applied to the source mass projection.  This identifies the
existing generated family with the operator-valued evolution mouth; it does
not introduce another approximation actual. -/
theorem fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_eq_propagator
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (time : ℝ)
    (timeMem : time ∈ Icc timeStart timeEnd) :
    fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
        timeStart timeEnd timeOrder a b testCount time =
      fixedP506L0CauchySafeMatterCanonicalCoefficientPropagator
        timeStart timeEnd timeOrder a b testCount time timeMem
        (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
          timeStart a b testCount) := by
  have equality := fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_eqOn
    timeStart timeEnd timeOrder a b testCount
    (fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution
      timeStart timeEnd timeOrder a b testCount
      (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
        timeStart a b testCount))
    (fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution_initial
      timeStart timeEnd timeOrder a b testCount
      (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
        timeStart a b testCount))
    (fixedP506L0CauchySafeMatterCanonicalCoefficientEvolution_evolution
      timeStart timeEnd timeOrder a b testCount
      (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
        timeStart a b testCount))
  simpa only [fixedP506L0CauchySafeMatterCanonicalCoefficientPropagator_apply]
    using equality timeMem

theorem fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_weakEquation
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (time : ℝ)
    (timeMem : time ∈ Icc timeStart timeEnd)
    (test : FixedP506L0CauchySafeMatterCanonicalCoefficient a b testCount) :
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount time
          (fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
            a b testCount time
            (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
              timeStart timeEnd timeOrder a b testCount time)) test +
        fixedP506L0CauchySafeMatterWeakStiffnessForm
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
            a b testCount)
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
            a b testCount)
          time
          (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
            timeStart timeEnd timeOrder a b testCount time) test = 0 := by
  have equation := fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_operatorEquation
    timeStart timeEnd timeOrder a b testCount time timeMem
  have tested := congrArg (fun value => inner ℝ value test) equation
  rw [inner_add_left, inner_zero_left,
    real_inner_galerkinWeakMassOperator] at tested
  simpa only [fixedP506L0CauchySafeMatterCanonicalWeakStiffnessOperator,
    fixedP506L0CauchySafeMatterWeakStiffnessOperator_readout,
    fixedP506L0CauchySafeMatterWeakStiffnessForm,
    diracMatterWeakStiffnessForm_apply] using tested

/-- The canonical source-owned finite approximation at one prefix. -/
def fixedP506L0CauchySafeMatterCanonicalApproximation
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    FixedP506L0CauchySafeWeakGalerkinApproximation
      timeStart timeEnd a b
      (fixedP506L0CauchySafeMatterCanonicalSourceInitialMassEnergy
        timeStart a b) where
  modeCount :=
    cauchySafeMatterCanonicalInteriorScalarPrefixModeCount a b testCount
  basis :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount
  basisRegular :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular a b testCount
  basisCompact :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact a b testCount
  basisZeroOutside :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_zeroOutside
      a b testCount
  coefficient :=
    fixedP506L0CauchySafeMatterCanonicalCoefficientCurve timeStart timeEnd timeOrder a b testCount
  velocity := fun time =>
    fixedP506L0CauchySafeMatterCanonicalWeakActionOperator
      a b testCount time
      (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
        timeStart timeEnd timeOrder a b testCount time)
  evolution := fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_evolution
    timeStart timeEnd timeOrder a b testCount
  weakEquation :=
    fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_weakEquation
    timeStart timeEnd timeOrder a b testCount
  initialEnergyBound := by
    simp only [galerkinWeakEnergy, fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_initial]
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact
        fixedP506L0CauchySafeMatterCanonicalInitialCoefficient_massEnergy_le_source
          timeStart a b testCount
    · exact fixedP506L0CauchySafeMatterWeakMassForm_nonnegative
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
        (fun mode =>
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
            a b testCount mode).continuous)
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
          a b testCount)
        timeStart
        (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
          timeStart a b testCount)

/-- Canonical finite coordinate of the generated interior test after entry. -/
def fixedP506L0CauchySafeMatterCanonicalTestCoefficient
    (a b : DiracMatterSpatialCoordinates)
    (testCount test : ℕ) :
    DiracMatterGalerkinCoefficient
      (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
        a b testCount) :=
  if entered : cauchySafeMatterCanonicalInteriorTestEntry test ≤ testCount then
    Classical.choose
      (cauchySafeMatterCanonicalInteriorTest_eventualRepresentation
        a b testCount test entered)
  else 0

theorem fixedP506L0CauchySafeMatterCanonicalTestCoefficient_representation
    (a b : DiracMatterSpatialCoordinates)
    (testCount test : ℕ)
    (entered : cauchySafeMatterCanonicalInteriorTestEntry test ≤ testCount) :
    cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test = fun point ↦
      matterCoordinateEquiv
        (fixedP506L0CauchySafeMatterWeakSpatialCandidate
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
          (fixedP506L0CauchySafeMatterCanonicalTestCoefficient a b testCount test) point) := by
  funext point
  let space := (EuclideanSpace.equiv (Fin 3) ℝ)
    (canonicalSpatialProjection point)
  have representation := Classical.choose_spec
    (cauchySafeMatterCanonicalInteriorTest_eventualRepresentation
      a b testCount test entered) space
  rw [fixedP506L0CauchySafeMatterCanonicalTestCoefficient, dif_pos entered]
  change (cauchySafeMatterCanonicalInteriorDenseTest a b test).1 space = _
  exact representation.symm

theorem fixedP506L0CauchySafeMatterCanonicalSynthesis_testCoefficient
    (a b : DiracMatterSpatialCoordinates)
    (testCount test : ℕ)
    (entered : cauchySafeMatterCanonicalInteriorTestEntry test ≤ testCount) :
    fixedP506L0CauchySafeMatterCanonicalSynthesis a b testCount
        (fixedP506L0CauchySafeMatterCanonicalTestCoefficient a b testCount test) =
      cauchySafeMatterSmoothCompactTestToL2 a b
        (cauchySafeMatterCanonicalInteriorDenseTest a b test) := by
  change fixedMatterTrialL2
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
      (fun mode =>
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
          a b testCount mode).continuous)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b testCount)
      (fixedP506L0CauchySafeMatterCanonicalTestCoefficient a b testCount test) a b =
    (cauchySafeMatterSmoothCompactTest_memLp a b
      (cauchySafeMatterCanonicalInteriorDenseTest a b test)).toLp
        (cauchySafeMatterCanonicalInteriorDenseTest a b test)
  apply Lp.ext
  filter_upwards [
    fixedMatterTrialL2_coe_ae
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
      (fun mode =>
        (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
          a b testCount mode).continuous)
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
        a b testCount)
      (fixedP506L0CauchySafeMatterCanonicalTestCoefficient a b testCount test) a b,
    (cauchySafeMatterSmoothCompactTest_memLp a b
      (cauchySafeMatterCanonicalInteriorDenseTest a b test)).coeFn_toLp]
      with space synthesisRead testRead
  rw [synthesisRead, testRead]
  rw [fixedP506L0CauchySafeMatterCanonicalTestCoefficient, dif_pos entered]
  exact Classical.choose_spec
    (cauchySafeMatterCanonicalInteriorTest_eventualRepresentation
      a b testCount test entered) space

private theorem canonicalInitialReadExact
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (approximationIndex test : ℕ)
    (entered :
      cauchySafeMatterCanonicalInteriorTestEntry test ≤ approximationIndex) :
    fixedP506L0CauchySafeMatterGalerkinInitialMassRead
        (fixedP506L0CauchySafeMatterCanonicalApproximation timeStart timeEnd timeOrder a b)
        (fixedP506L0CauchySafeMatterCanonicalTestCoefficient a b) test approximationIndex =
      fixedP506L0CauchySafeMatterSpatialMassRead timeStart a b
        (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2
          timeStart a b) test := by
  let coefficient := fixedP506L0CauchySafeMatterCanonicalTestCoefficient a b approximationIndex test
  have massLaw :=
    fixedP506L0CauchySafeMatterCanonicalInitialCoefficient_massLaw
      timeStart a b approximationIndex coefficient
  have synthesisEq := fixedP506L0CauchySafeMatterCanonicalSynthesis_testCoefficient
    a b approximationIndex test entered
  unfold fixedP506L0CauchySafeMatterGalerkinInitialMassRead
  change fixedP506L0CauchySafeMatterCanonicalWeakMassForm
      a b approximationIndex timeStart
      (fixedP506L0CauchySafeMatterCanonicalCoefficientCurve
        timeStart timeEnd timeOrder a b approximationIndex timeStart)
      coefficient = _
  rw [fixedP506L0CauchySafeMatterCanonicalCoefficientCurve_initial]
  calc
    fixedP506L0CauchySafeMatterCanonicalWeakMassForm
          a b approximationIndex timeStart
          (fixedP506L0CauchySafeMatterCanonicalInitialCoefficient
            timeStart a b approximationIndex) coefficient = _ := massLaw
    _ = ∫ space,
          matterFiberMassPairing
            (fixedP506L0CauchySafeMatterWeakMassMatrix timeStart space)
            (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2
              timeStart a b space)
            (fixedP506L0CauchySafeMatterCanonicalSynthesis
              a b approximationIndex coefficient space)
          ∂volume.restrict (Icc a b) :=
      fixedP506L0CauchySafeMatterL2MassForm_eq_integral _ _ _ _ _ _ _
    _ = ∫ space,
          matterFiberMassPairing
            (fixedP506L0CauchySafeMatterWeakMassMatrix timeStart space)
            (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2
              timeStart a b space)
            ((cauchySafeMatterSmoothCompactTestToL2 a b
              (cauchySafeMatterCanonicalInteriorDenseTest a b test)) space)
          ∂volume.restrict (Icc a b) := by rw [synthesisEq]
    _ = fixedP506L0CauchySafeMatterSpatialMassRead timeStart a b
          (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2
            timeStart a b) test := by
      rw [fixedP506L0CauchySafeMatterSpatialMassRead]

/-- The fixed source and its canonical nested action evolution generate the
entire same-source Galerkin history; no approximation family is supplied. -/
def fixedP506L0CauchySafeMatterCanonicalSameSourceGalerkinFamily
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates) :
    FixedP506L0CauchySafeSameSourceWeakGalerkinFamily
      timeStart timeEnd a b
      (fixedP506L0CauchySafeMatterCanonicalSourceInitialMassEnergy
        timeStart a b) where
  approximation := fixedP506L0CauchySafeMatterCanonicalApproximation timeStart timeEnd timeOrder a b
  testEntry := cauchySafeMatterCanonicalInteriorTestEntry
  testCoefficient := fixedP506L0CauchySafeMatterCanonicalTestCoefficient a b
  testRepresentation := fixedP506L0CauchySafeMatterCanonicalTestCoefficient_representation a b
  initialField :=
    fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 timeStart a b
  initialReadExact := canonicalInitialReadExact
    timeStart timeEnd timeOrder a b

/-- The source-owned canonical history reaches the existing generated
physical `L²` limit occurrence without an externally supplied family. -/
theorem nonempty_fixedP506L0CauchySafeMatterCanonicalGeneratedLimitOccurrence
    (timeStart timeEnd : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    Nonempty
      (FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b
        (fixedP506L0CauchySafeMatterCanonicalSourceInitialMassEnergy
          timeStart a b)
        timeOrder
        (fixedP506L0CauchySafeMatterCanonicalSameSourceGalerkinFamily
          timeStart timeEnd timeOrder a b).approximation
        (fixedP506L0CauchySafeMatterCanonicalSameSourceGalerkinFamily
          timeStart timeEnd timeOrder a b).testEntry
        (fixedP506L0CauchySafeMatterCanonicalSameSourceGalerkinFamily
          timeStart timeEnd timeOrder a b).testCoefficient) := by
  exact
    (fixedP506L0CauchySafeMatterCanonicalSameSourceGalerkinFamily
      timeStart timeEnd timeOrder a b).nonemptyOccurrence
        timeOrder boxOrder
        (fixedP506L0CauchySafeMatterCanonicalSourceInitialMassEnergy_nonnegative
          timeStart a b)

end

end SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalSameSourceGalerkinFamily
