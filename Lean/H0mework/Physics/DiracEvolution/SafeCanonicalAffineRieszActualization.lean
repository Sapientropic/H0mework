import H0mework.Physics.DiracEvolution.SafeCanonicalAffineWeakLimitOccurrence
import H0mework.Physics.DiracEvolution.SafeL2MassActualization
import H0mework.Physics.DiracEvolution.SafeCanonicalDenseRieszActualization
import H0mework.Physics.DiracEvolution.GeneratedWeakLimitActualization

/-!
# Fixed P506/L0 canonical affine Riesz actualization

The source-owned correction weak-limit occurrence is actualized on the
canonical dense test span, inverted through the mother-action mass form, and
added to the fixed boundary lift.  No approximation family, limit,
representative, residual, or target field is supplied to the producer.
-/

namespace SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineRieszActualization

open Filter MeasureTheory Set
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineCauchySafeMatterCanonicalDenseRieszActualization
open StageNineCountableWeakPairingCompactness
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineBoundaryForcing
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineBoundaryStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineUniformEnergy
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineWeakLimitOccurrence
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterFiniteL2MassRead
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalSameSourceGalerkinFamily
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterSpatialEnergyBalance
open StageNineGeneratedWeakLimitActualization
open StageNineHolonomicField
open scoped BoundedContinuousFunction

noncomputable section

set_option autoImplicit false

abbrev CanonicalAffineCorrectionWeakLimitOccurrence
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates) :=
  CountableWeightedWeakLimitOccurrence timeNonnegative
    (canonicalAffineCorrectionBoundedPairing
      timeEnd timeNonnegative a b)
    (fun testCount test ↦
      (canonicalAffineCorrectionPairingPath
        timeEnd timeNonnegative a b testCount test).rate)
    cauchySafeMatterCanonicalInteriorTestEntry

def canonicalAffineCorrectionFiniteMassRead
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
    CauchySafeMatterSmoothCompactTest →ₗ[ℝ] ℝ :=
  fixedMatterFiniteMassRead C
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
    (fun mode ↦
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
        a b testCount mode).continuous)
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
      a b testCount)
    (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
      timeEnd timeNonnegative a b testCount time.1)
    time.1 a b (operatorBound time.1 time.2)

theorem canonicalAffineCorrectionFiniteMassRead_generatorConvergence
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C)
    (occurrence : CanonicalAffineCorrectionWeakLimitOccurrence
      timeEnd timeNonnegative a b)
    (time : Icc 0 timeEnd)
    (test : ℕ) :
    Tendsto
      (fun sequenceIndex ↦
        canonicalAffineCorrectionFiniteMassRead
          timeEnd timeNonnegative a b C operatorBound
          (occurrence.subsequence sequenceIndex) time
          (cauchySafeMatterCanonicalInteriorDenseTest a b test))
      atTop (nhds (occurrence.limit test time)) := by
  have rawConvergence :=
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      (occurrence.pairingConvergence test)).tendsto_at time
  apply rawConvergence.congr'
  have eventuallyEntered : ∀ᶠ sequenceIndex : ℕ in atTop,
      cauchySafeMatterCanonicalInteriorTestEntry test ≤
        occurrence.subsequence sequenceIndex :=
    occurrence.subsequenceStrict.tendsto_atTop
      (eventually_ge_atTop (cauchySafeMatterCanonicalInteriorTestEntry test))
  filter_upwards [eventuallyEntered] with sequenceIndex entered
  symm
  unfold canonicalAffineCorrectionFiniteMassRead
  have readEq := fixedMatterFiniteMassRead_eq_galerkinWeakTestPairing C
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b
      (occurrence.subsequence sequenceIndex))
    (fun mode ↦
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
        a b (occurrence.subsequence sequenceIndex) mode).continuous)
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
      a b (occurrence.subsequence sequenceIndex))
    a b
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_zeroOutside
      a b (occurrence.subsequence sequenceIndex))
    (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
      timeEnd timeNonnegative a b (occurrence.subsequence sequenceIndex))
    (fixedP506L0CauchySafeMatterCanonicalTestCoefficient a b
      (occurrence.subsequence sequenceIndex) test)
    time.1
    (operatorBound time.1 time.2)
    (cauchySafeMatterCanonicalInteriorDenseTest a b test)
    (fun space ↦ by
      have represented := congrFun
        (fixedP506L0CauchySafeMatterCanonicalTestCoefficient_representation
          a b (occurrence.subsequence sequenceIndex) test entered)
        (diracMatterSpacetimeCoordinatePoint time.1 space)
      rw [fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice] at represented
      simpa [fixedMatterTrialCoordinates] using represented.symm)
  rw [readEq]
  rfl

theorem exists_canonicalAffineCorrectionFiniteMassRead_uniform_bound
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (CNonnegative : 0 ≤ C)
    (operatorBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ testCount (time : Icc 0 timeEnd) test,
      ‖canonicalAffineCorrectionFiniteMassRead
          timeEnd timeNonnegative a b C operatorBound testCount time test‖ ≤
        B * ‖cauchySafeMatterSmoothCompactTestToL2 a b test‖ := by
  obtain ⟨R, RNonnegative, correctionBound⟩ :=
    exists_fixedP506L0CauchySafeMatterCanonicalAffineCorrection_uniform_bound
      timeEnd timeNonnegative a b boxOrder
  refine ⟨C * R, mul_nonneg CNonnegative RNonnegative, ?_⟩
  intro testCount time test
  have readBound := fixedMatterFiniteMassRead_bound C
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount)
    (fun mode ↦
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
        a b testCount mode).continuous)
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
      a b testCount)
    (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
      timeEnd timeNonnegative a b testCount time.1)
    time.1 a b (operatorBound time.1 time.2) test
  have correctionBoundAtTime := correctionBound testCount time.1 time.2
  exact readBound.trans (by
    change C * ‖fixedP506L0CauchySafeMatterCanonicalSynthesis
        a b testCount
        (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
          timeEnd timeNonnegative a b testCount time.1)‖ *
        ‖cauchySafeMatterSmoothCompactTestToL2 a b test‖ ≤
      (C * R) * ‖cauchySafeMatterSmoothCompactTestToL2 a b test‖
    gcongr)

def canonicalAffineCorrectionSpanFunctionalAt
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C)
    (time : Icc 0 timeEnd) :
    ℕ → CauchySafeMatterCanonicalInteriorTestSpan a b →ₗ[ℝ] ℝ :=
  fun testCount ↦
    (canonicalAffineCorrectionFiniteMassRead
      timeEnd timeNonnegative a b C operatorBound testCount time).comp
      (Submodule.subtype
        (CauchySafeMatterCanonicalInteriorTestSpan a b))

def canonicalAffineCorrectionRieszRepresentativeAt
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C)
    (occurrence : CanonicalAffineCorrectionWeakLimitOccurrence
      timeEnd timeNonnegative a b)
    (time : Icc 0 timeEnd)
    (limit : CauchySafeMatterCanonicalInteriorTestSpan a b → ℝ)
    (convergence : ∀ test,
      Tendsto
        (fun sequenceIndex ↦
          canonicalAffineCorrectionFiniteMassRead
            timeEnd timeNonnegative a b C operatorBound
            (occurrence.subsequence sequenceIndex) time test.1)
        atTop (nhds (limit test))) :
    CauchySafeMatterSpatialL2 a b :=
  pointwiseLimitRieszActualization
    (cauchySafeMatterCanonicalInteriorTestSpanToL2 a b)
    (canonicalAffineCorrectionSpanFunctionalAt
      timeEnd timeNonnegative a b C operatorBound time)
    occurrence.subsequence limit convergence

/-- One canonical-time dense-span actualization of the emitted correction
pairing. -/
structure CanonicalAffineCorrectionRieszSpanActualizationAt
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C)
    (occurrence : CanonicalAffineCorrectionWeakLimitOccurrence
      timeEnd timeNonnegative a b)
    (time : Icc 0 timeEnd) where
  limit : CauchySafeMatterCanonicalInteriorTestSpan a b → ℝ
  convergence : ∀ test,
    Tendsto
      (fun sequenceIndex ↦
        canonicalAffineCorrectionFiniteMassRead
          timeEnd timeNonnegative a b C operatorBound
          (occurrence.subsequence sequenceIndex) time test.1)
      atTop (nhds (limit test))
  spanPairing : ∀ test,
    inner ℝ
        (canonicalAffineCorrectionRieszRepresentativeAt
          timeEnd timeNonnegative a b C operatorBound occurrence time
          limit convergence)
        (cauchySafeMatterCanonicalInteriorTestSpanToL2 a b test) =
      limit test
  spanUnique : ∀ candidate : CauchySafeMatterSpatialL2 a b,
    (∀ test,
      inner ℝ candidate
          (cauchySafeMatterCanonicalInteriorTestSpanToL2 a b test) =
        limit test) →
      candidate = canonicalAffineCorrectionRieszRepresentativeAt
        timeEnd timeNonnegative a b C operatorBound occurrence time
        limit convergence
  generatorRecognition : ∀ test,
    limit ⟨cauchySafeMatterCanonicalInteriorDenseTest a b test,
      Submodule.subset_span (Set.mem_range_self test)⟩ =
      occurrence.limit test time

theorem nonempty_canonicalAffineCorrectionRieszSpanActualizationAt
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
    (occurrence : CanonicalAffineCorrectionWeakLimitOccurrence
      timeEnd timeNonnegative a b)
    (time : Icc 0 timeEnd) :
    Nonempty (CanonicalAffineCorrectionRieszSpanActualizationAt
      timeEnd timeNonnegative a b C operatorBound occurrence time) := by
  obtain ⟨B, _BNonnegative, finiteReadBound⟩ :=
    exists_canonicalAffineCorrectionFiniteMassRead_uniform_bound
      timeEnd timeNonnegative a b boxOrder C CNonnegative operatorBound
  obtain ⟨limit, convergence, spanPairing, spanUnique,
      generatorRecognition⟩ :=
    exists_canonicalDenseRieszSpanActualization a b
    (fun testCount ↦ canonicalAffineCorrectionFiniteMassRead
      timeEnd timeNonnegative a b C operatorBound testCount time)
    occurrence.subsequence (fun test ↦ occurrence.limit test time)
    (canonicalAffineCorrectionFiniteMassRead_generatorConvergence
      timeEnd timeNonnegative a b C operatorBound occurrence time)
    B (fun testCount test ↦ finiteReadBound testCount time test)
  exact ⟨{
    limit := limit
    convergence := convergence
    spanPairing := spanPairing
    spanUnique := spanUnique
    generatorRecognition := generatorRecognition }⟩

/-- The source-generated correction weak limit together with its dense-span
Riesz data and unique physical mass actualization. -/
structure FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates) where
  C : ℝ
  CNonnegative : 0 ≤ C
  operatorBound : ∀ time ∈ Icc 0 timeEnd,
    ∀ space ∈ Icc a b,
      ‖matterFiberMassPairing
        (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C
  weakLimit : CanonicalAffineCorrectionWeakLimitOccurrence
    timeEnd timeNonnegative a b
  rieszAt : ∀ time : Icc 0 timeEnd,
    CanonicalAffineCorrectionRieszSpanActualizationAt
      timeEnd timeNonnegative a b C operatorBound weakLimit time
  correctionMassRepresentative :
    Icc 0 timeEnd → CauchySafeMatterSpatialL2 a b
  correctionMassRepresentative_eq : ∀ time,
    correctionMassRepresentative time =
      canonicalAffineCorrectionRieszRepresentativeAt
        timeEnd timeNonnegative a b C operatorBound weakLimit time
        (rieszAt time).limit (rieszAt time).convergence
  correctionPhysicalActualization :
    FixedP506L0CauchySafeMatterPhysicalL2Actualization
      0 timeEnd a b correctionMassRepresentative

/-- The canonical affine physical output is the fixed source-owned boundary
lift plus the uniquely mass-actualized zero-boundary correction. -/
def FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence.affinePhysicalField
    {timeEnd : ℝ}
    {timeNonnegative : 0 ≤ timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b)
    (time : Icc 0 timeEnd) : CauchySafeMatterSpatialL2 a b :=
  fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b +
    occurrence.correctionPhysicalActualization.physicalField time

theorem FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence.correctionMassRepresentative_generatorPairing
    {timeEnd : ℝ}
    {timeNonnegative : 0 ≤ timeEnd}
    {a b : DiracMatterSpatialCoordinates}
    (occurrence :
      FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b)
    (time : Icc 0 timeEnd)
    (test : ℕ) :
    inner ℝ (occurrence.correctionMassRepresentative time)
        (cauchySafeMatterSmoothCompactTestToL2 a b
          (cauchySafeMatterCanonicalInteriorDenseTest a b test)) =
      occurrence.weakLimit.limit test time := by
  rw [occurrence.correctionMassRepresentative_eq time]
  let spanTest : CauchySafeMatterCanonicalInteriorTestSpan a b :=
    ⟨cauchySafeMatterCanonicalInteriorDenseTest a b test,
      Submodule.subset_span (Set.mem_range_self test)⟩
  calc
    _ = (occurrence.rieszAt time).limit spanTest :=
      (occurrence.rieszAt time).spanPairing spanTest
    _ = occurrence.weakLimit.limit test time :=
      (occurrence.rieszAt time).generatorRecognition test

/-- The fixed source-owned affine history generates one mass-actualized
physical `L²` output family.  No approximation family, limit, or representative
is supplied to this producer. -/
theorem nonempty_fixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    Nonempty
      (FixedP506L0CauchySafeCanonicalAffineMassActualizedLimitOccurrence
        timeEnd timeNonnegative a b) := by
  obtain ⟨C, CNonnegative, operatorBound⟩ :=
    exists_fixedMassPairingOperatorBoundOnBox
      0 timeEnd a b timeNonnegative boxOrder
  obtain ⟨weakLimit⟩ :=
    nonempty_canonicalAffineCorrectionWeakLimitOccurrence
      timeEnd timeNonnegative a b boxOrder
  have existsRieszAt : ∀ time : Icc 0 timeEnd,
      Nonempty (CanonicalAffineCorrectionRieszSpanActualizationAt
        timeEnd timeNonnegative a b C operatorBound weakLimit time) := by
    intro time
    exact nonempty_canonicalAffineCorrectionRieszSpanActualizationAt
      timeEnd timeNonnegative a b boxOrder C CNonnegative operatorBound
      weakLimit time
  let rieszAt := fun time : Icc 0 timeEnd ↦
    Classical.choice (existsRieszAt time)
  let correctionMassRepresentative :
      Icc 0 timeEnd → CauchySafeMatterSpatialL2 a b := fun time ↦
    canonicalAffineCorrectionRieszRepresentativeAt
      timeEnd timeNonnegative a b C operatorBound weakLimit time
      (rieszAt time).limit (rieszAt time).convergence
  obtain ⟨correctionPhysicalActualization⟩ :=
    nonempty_fixedP506L0CauchySafeMatterPhysicalL2Actualization
      0 timeEnd a b boxOrder correctionMassRepresentative
  exact ⟨{
    C := C
    CNonnegative := CNonnegative
    operatorBound := operatorBound
    weakLimit := weakLimit
    rieszAt := rieszAt
    correctionMassRepresentative := correctionMassRepresentative
    correctionMassRepresentative_eq := fun _ ↦ rfl
    correctionPhysicalActualization := correctionPhysicalActualization }⟩

end

end SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineRieszActualization
