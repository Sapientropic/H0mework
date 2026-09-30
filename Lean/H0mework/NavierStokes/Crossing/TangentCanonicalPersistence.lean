import H0mework.NavierStokes.Crossing.TangentQuantumPayment

/-!
# Canonical persistence of the generated crossing tangent quantum

The first quantitative crossing theorem used an arbitrary neighborhood
witness returned by continuity.  Here the same actual finite Fourier carrier
is assigned a canonical harmonic-grid lifetime: the least source-generated
index whose interval keeps at least half of the fixed tangent quantum.

Consequently a later collapse of these lifetimes is a statement about the
actual tangent density, not an artefact of choosing needlessly small open
neighborhoods.  No radius, modulus, interval, modes, cutoff, or lower-bound
certificate is accepted from a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCanonicalPersistence

open scoped BigOperators Interval Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentQuantumPayment

noncomputable section

/-! ## Canonical finite carrier and harmonic persistence grid -/

/-- One fixed finite carrier selected by the actual crossing from the whole
`H⁻¹` tangent sum. -/
noncomputable def wholeRestartCrossingTangentCanonicalModes
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    Finset NonzeroIntegerWavevector :=
  Classical.choose
    (exists_wholeRestartCrossingTangentCoerciveModes
      initial index crossed)

theorem wholeRestartCrossingTangentCanonicalModes_density_zero_gt
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    wholeRestartCrossingTangentCoerciveQuantum ν <
      wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
        initial index
        (wholeRestartCrossingTangentCanonicalModes
          initial index crossed) 0 :=
  Classical.choose_spec
    (exists_wholeRestartCrossingTangentCoerciveModes
      initial index crossed)

/-- Source-owned decreasing grid inside the exact next contact time.  The
offset `+2` keeps every candidate strictly inside the actual receipt. -/
def wholeRestartCrossingTangentHarmonicTime
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (gridIndex : ℕ) : ℝ :=
  (run initial index).nextContact.time.1 / (gridIndex + 2 : ℕ)

/-- A grid index is good when the actual finite tangent density retains at
least half of the fixed quantum on its complete closed prefix. -/
def WholeRestartCrossingTangentPersistenceGood
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (gridIndex : ℕ) : Prop :=
  ∀ actual ∈ Icc (0 : ℝ)
      (wholeRestartCrossingTangentHarmonicTime
        initial index gridIndex),
    wholeRestartCrossingTangentCoerciveQuantum ν / 2 ≤
      wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
        initial index
        (wholeRestartCrossingTangentCanonicalModes
          initial index crossed) actual

theorem exists_wholeRestartCrossingTangentPersistenceGood
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    ∃ gridIndex : ℕ,
      WholeRestartCrossingTangentPersistenceGood
        initial index crossed gridIndex := by
  let modes :=
    wholeRestartCrossingTangentCanonicalModes initial index crossed
  let density :=
    wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
      initial index modes
  let quantum := wholeRestartCrossingTangentCoerciveQuantum ν
  let duration := (run initial index).nextContact.time.1
  have densityContinuous : Continuous density :=
    wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity_continuous
      initial index modes
  have quantumPos : 0 < quantum :=
    wholeRestartCrossingTangentCoerciveQuantum_pos ν
  have densityZeroGt : quantum < density 0 := by
    simpa only [modes, density, quantum] using
      wholeRestartCrossingTangentCanonicalModes_density_zero_gt
        initial index crossed
  have halfQuantumLt : quantum / 2 < density 0 := by linarith
  have eventuallyLower :
      ∀ᶠ actual in 𝓝 (0 : ℝ), quantum / 2 < density actual :=
    densityContinuous.continuousAt.eventually
      (eventually_gt_nhds halfQuantumLt)
  obtain ⟨radius, radiusPos, withinRadius⟩ :=
    Metric.eventually_nhds_iff.mp eventuallyLower
  have durationPos : 0 < duration :=
    (run initial index).nextContact.time_pos
  obtain ⟨gridIndex, gridLarge⟩ :=
    exists_nat_gt (duration / radius)
  have durationLtGridRadius :
      duration < (gridIndex : ℝ) * radius := by
    exact (div_lt_iff₀ radiusPos).mp gridLarge
  have denominatorPos :
      0 < ((gridIndex + 2 : ℕ) : ℝ) := by positivity
  have harmonicLtRadius :
      duration / ((gridIndex + 2 : ℕ) : ℝ) < radius := by
    apply (div_lt_iff₀ denominatorPos).2
    calc
      duration < (gridIndex : ℝ) * radius := durationLtGridRadius
      _ < radius * ((gridIndex + 2 : ℕ) : ℝ) := by
        norm_num [Nat.cast_add, Nat.cast_ofNat]
        nlinarith
  refine ⟨gridIndex, ?_⟩
  intro actual actualMem
  have actualNonneg : 0 ≤ actual := actualMem.1
  have actualLtRadius : actual < radius := by
    exact actualMem.2.trans_lt harmonicLtRadius
  have distanceLt : dist actual 0 < radius := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg actualNonneg]
    exact actualLtRadius
  exact (withinRadius distanceLt).le

/-- Least harmonic-grid index whose entire interval retains half of the
generated quantum. -/
noncomputable def wholeRestartCrossingTangentCanonicalPersistenceIndex
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) : ℕ := by
  classical
  exact Nat.find
    (exists_wholeRestartCrossingTangentPersistenceGood
      initial index crossed)

/-- Canonical source-owned quantum lifetime. -/
noncomputable def wholeRestartCrossingTangentCanonicalPersistenceTime
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) : ℝ :=
  wholeRestartCrossingTangentHarmonicTime initial index
    (wholeRestartCrossingTangentCanonicalPersistenceIndex
      initial index crossed)

theorem wholeRestartCrossingTangentCanonicalPersistence_good
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    WholeRestartCrossingTangentPersistenceGood
      initial index crossed
      (wholeRestartCrossingTangentCanonicalPersistenceIndex
        initial index crossed) := by
  classical
  exact Nat.find_spec
    (exists_wholeRestartCrossingTangentPersistenceGood
      initial index crossed)

/-- Every earlier grid index represents a strictly larger harmonic window
and fails the complete half-quantum persistence predicate.  Thus the chosen
window is maximal in the generated harmonic grid, rather than an arbitrary
small neighborhood. -/
theorem wholeRestartCrossingTangentCanonicalPersistence_minimal
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    {earlier : ℕ}
    (earlierLt :
      earlier <
        wholeRestartCrossingTangentCanonicalPersistenceIndex
          initial index crossed) :
    ¬ WholeRestartCrossingTangentPersistenceGood
        initial index crossed earlier := by
  classical
  intro earlierGood
  have leastLe :
      wholeRestartCrossingTangentCanonicalPersistenceIndex
          initial index crossed ≤ earlier := by
    exact Nat.find_min'
      (exists_wholeRestartCrossingTangentPersistenceGood
        initial index crossed)
      earlierGood
  exact (Nat.not_lt_of_ge leastLe) earlierLt

/-- If the maximal generated grid index is nonzero, its immediately larger
physical window contains an actual point where the finite tangent density
has dropped below half of the fixed quantum. -/
theorem wholeRestartCrossingTangentCanonicalPersistence_drop_or_firstGrid
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    wholeRestartCrossingTangentCanonicalPersistenceIndex
          initial index crossed = 0 ∨
      ∃ actual ∈ Icc (0 : ℝ)
          (wholeRestartCrossingTangentHarmonicTime initial index
            (wholeRestartCrossingTangentCanonicalPersistenceIndex
              initial index crossed - 1)),
        wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
              initial index
              (wholeRestartCrossingTangentCanonicalModes
                initial index crossed) actual <
          wholeRestartCrossingTangentCoerciveQuantum ν / 2 := by
  by_cases firstGrid :
      wholeRestartCrossingTangentCanonicalPersistenceIndex
        initial index crossed = 0
  · exact Or.inl firstGrid
  · right
    let selected :=
      wholeRestartCrossingTangentCanonicalPersistenceIndex
        initial index crossed
    have selectedNe : selected ≠ 0 := by
      simpa only [selected] using firstGrid
    have predecessorLt : selected - 1 < selected := by
      exact Nat.sub_one_lt selectedNe
    have predecessorFails :=
      wholeRestartCrossingTangentCanonicalPersistence_minimal
        initial index crossed predecessorLt
    unfold WholeRestartCrossingTangentPersistenceGood at predecessorFails
    push Not at predecessorFails
    simpa only [selected] using predecessorFails

theorem wholeRestartCrossingTangentCanonicalPersistenceTime_pos
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    0 < wholeRestartCrossingTangentCanonicalPersistenceTime
      initial index crossed := by
  unfold wholeRestartCrossingTangentCanonicalPersistenceTime
    wholeRestartCrossingTangentHarmonicTime
  exact div_pos (run initial index).nextContact.time_pos (by positivity)

theorem wholeRestartCrossingTangentCanonicalPersistenceTime_lt
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    wholeRestartCrossingTangentCanonicalPersistenceTime
        initial index crossed <
      (run initial index).nextContact.time.1 := by
  unfold wholeRestartCrossingTangentCanonicalPersistenceTime
    wholeRestartCrossingTangentHarmonicTime
  have denominatorGtOne :
      (1 : ℝ) <
        ((wholeRestartCrossingTangentCanonicalPersistenceIndex
              initial index crossed + 2 : ℕ) : ℝ) := by
    exact_mod_cast
      (by omega : 1 <
        wholeRestartCrossingTangentCanonicalPersistenceIndex
            initial index crossed + 2)
  exact div_lt_self (run initial index).nextContact.time_pos denominatorGtOne

/-! ## Canonical amplitude--time payment -/

theorem wholeRestartCrossingTangentCanonicalPersistence_pointwise
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    ∀ actual ∈ Icc (0 : ℝ)
        (wholeRestartCrossingTangentCanonicalPersistenceTime
          initial index crossed),
      wholeRestartCrossingTangentCoerciveQuantum ν / 2 ≤
        wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
          initial index
          (wholeRestartCrossingTangentCanonicalModes
            initial index crossed) actual := by
  intro actual actualMem
  exact
    wholeRestartCrossingTangentCanonicalPersistence_good
      initial index crossed actual actualMem

theorem wholeRestartCrossingTangentCanonicalPersistence_amplitudeTime_le
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    wholeRestartCrossingTangentCanonicalPersistenceTime
          initial index crossed *
          (wholeRestartCrossingTangentCoerciveQuantum ν / 2) ≤
      ∫ actual in (0 : ℝ)..
          wholeRestartCrossingTangentCanonicalPersistenceTime
            initial index crossed,
        wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
          initial index
          (wholeRestartCrossingTangentCanonicalModes
            initial index crossed) actual := by
  let localTime :=
    wholeRestartCrossingTangentCanonicalPersistenceTime
      initial index crossed
  let density :=
    wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
      initial index
      (wholeRestartCrossingTangentCanonicalModes initial index crossed)
  let quantum := wholeRestartCrossingTangentCoerciveQuantum ν
  have localTimePos : 0 < localTime :=
    wholeRestartCrossingTangentCanonicalPersistenceTime_pos
      initial index crossed
  have densityContinuous : Continuous density :=
    wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity_continuous
      initial index _
  have integratedLower :=
    intervalIntegral.integral_mono_on
      (μ := volume)
      localTimePos.le
      (continuous_const.intervalIntegrable 0 localTime)
      (densityContinuous.intervalIntegrable 0 localTime)
      (wholeRestartCrossingTangentCanonicalPersistence_pointwise
        initial index crossed)
  have normalizedLower :
      localTime * quantum / 2 ≤
        ∫ actual in (0 : ℝ)..localTime, density actual := by
    simpa [localTime, density, quantum,
      intervalIntegral.integral_const, smul_eq_mul] using integratedLower
  calc
    wholeRestartCrossingTangentCanonicalPersistenceTime
          initial index crossed *
          (wholeRestartCrossingTangentCoerciveQuantum ν / 2) =
        localTime * quantum / 2 := by
      dsimp [localTime, quantum]
      ring
    _ ≤ ∫ actual in (0 : ℝ)..localTime, density actual := normalizedLower
    _ = ∫ actual in (0 : ℝ)..
          wholeRestartCrossingTangentCanonicalPersistenceTime
            initial index crossed,
        wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
          initial index
          (wholeRestartCrossingTangentCanonicalModes
            initial index crossed) actual := rfl

theorem wholeRestartCrossingTangentCanonicalPersistence_payment_pos
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    0 <
      ∫ actual in (0 : ℝ)..
          wholeRestartCrossingTangentCanonicalPersistenceTime
            initial index crossed,
        wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
          initial index
          (wholeRestartCrossingTangentCanonicalModes
            initial index crossed) actual := by
  have timePos :=
    wholeRestartCrossingTangentCanonicalPersistenceTime_pos
      initial index crossed
  have halfQuantumPos :
      0 < wholeRestartCrossingTangentCoerciveQuantum ν / 2 :=
    div_pos (wholeRestartCrossingTangentCoerciveQuantum_pos ν) (by norm_num)
  exact
    (mul_pos timePos halfQuantumPos).trans_le
      (wholeRestartCrossingTangentCanonicalPersistence_amplitudeTime_le
        initial index crossed)

theorem wholeRestartCrossingTangentCanonicalPersistence_payment_le
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    (∫ actual in (0 : ℝ)..
        wholeRestartCrossingTangentCanonicalPersistenceTime
          initial index crossed,
      wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
        initial index
        (wholeRestartCrossingTangentCanonicalModes
          initial index crossed) actual) ≤
      3 * ‖(run initial index).nextContact.prefixReceipt.wholeTangent‖ ^ 2 := by
  let localTime :=
    wholeRestartCrossingTangentCanonicalPersistenceTime
      initial index crossed
  let duration := (run initial index).nextContact.time.1
  let modes :=
    wholeRestartCrossingTangentCanonicalModes initial index crossed
  let density :=
    wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
      initial index modes
  have localTimePos : 0 < localTime :=
    wholeRestartCrossingTangentCanonicalPersistenceTime_pos
      initial index crossed
  have localTimeLe : localTime ≤ duration :=
    (wholeRestartCrossingTangentCanonicalPersistenceTime_lt
      initial index crossed).le
  have densityContinuous : Continuous density :=
    wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity_continuous
      initial index modes
  have localIntegralLeFull :
      (∫ actual in (0 : ℝ)..localTime, density actual) ≤
        ∫ actual in (0 : ℝ)..duration, density actual :=
    intervalIntegral.integral_mono_interval
      (μ := volume) (c := (0 : ℝ)) (d := duration)
      le_rfl localTimePos.le localTimeLe
      (Filter.Eventually.of_forall fun actual =>
        wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity_nonneg
          initial index modes actual)
      (densityContinuous.intervalIntegrable 0 duration)
  exact localIntegralLeFull.trans
    (by
      simpa only [density, duration, modes] using
        wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity_integral_le
          initial index modes)

end

end
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCanonicalPersistence
end NavierStokes
end SaturationMonoid
