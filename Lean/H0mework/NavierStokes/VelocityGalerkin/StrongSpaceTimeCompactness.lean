import H0mework.NavierStokes.VelocityGalerkin.InitialConvergence
import H0mework.NavierStokes.VelocityGalerkin.FiniteObservationTimeTightness
import H0mework.NavierStokes.GeneratedPaths.StrongSpaceTimeCompactness

/-!
# Strong velocity space-time compactness of the endpoint Galerkin family

The source-generated physical velocity endpoint already writes every
canonical unforced Galerkin orbit.  This module places the actual velocity
orbits in the common `L²([0,1]; ℓ²)` carrier.  The radius-uniform viscous
tail and the fixed-observation time compactness are then combined before any
quotient, producing one whole-carrier strongly convergent subsequence.

No subsequence, target path, compactness witness, cutoff, critical margin,
or continuation certificate enters the source-facing mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinStrongSpaceTimeCompactness

open scoped BigOperators ENNReal Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness

noncomputable section

/-! ## Actual velocity paths on one common carrier -/

/-- The actual finite Galerkin velocity at an ambient physical time,
extended by zero to the complete integer Fourier carrier. -/
def generatedVelocityEndpointGalerkinWholeStateAtTime
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ)
    (time : ℝ) : ComplexVorticityHilbertState :=
  finiteComplexVorticityState
    (wholeRestartModes radius)
    (fun wave =>
      finiteStateVelocityCoefficient
        ((ledger.family.stage radius).trajectory time) wave)

/-- The actual finite Galerkin velocity at one source radius and physical
time, extended by zero to the complete integer Fourier carrier. -/
def generatedVelocityEndpointGalerkinWholeState
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ)
    (time : Icc (0 : ℝ) 1) :
    ComplexVorticityHilbertState :=
  generatedVelocityEndpointGalerkinWholeStateAtTime
    ledger radius time.1

@[simp] theorem generatedVelocityEndpointGalerkinWholeState_apply
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ)
    (time : Icc (0 : ℝ) 1)
    (wave : IntegerWavevector) :
    generatedVelocityEndpointGalerkinWholeState ledger radius time wave =
      if wave ∈ wholeRestartModes radius then
        finiteStateVelocityCoefficient
          ((ledger.family.stage radius).trajectory time.1) wave
      else 0 := by
  simp [generatedVelocityEndpointGalerkinWholeState,
    generatedVelocityEndpointGalerkinWholeStateAtTime]

/-- At physical time zero, the whole velocity path is exactly the canonical
projection of the generated endpoint. -/
theorem generatedVelocityEndpointGalerkinWholeState_zero
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) :
    generatedVelocityEndpointGalerkinWholeState ledger radius
        ⟨0, by norm_num⟩ =
      wholeRestartVelocityEndpointFiniteProjection radius
        ledger.family.endpointReceipt.velocityEndpoint := by
  apply lp.ext
  funext wave
  by_cases waveMem : wave ∈ wholeRestartModes radius
  · rw [generatedVelocityEndpointGalerkinWholeState_apply,
      if_pos waveMem,
      (ledger.family.stage radius).initial,
      finiteStateVelocityCoefficient,
      wholeRestartVelocityEndpointFiniteVorticityInitialState_biotSavart
        radius ledger.family.endpointReceipt.velocityEndpoint
        ledger.family.endpointReceipt.velocityEndpoint_transverse
        wave waveMem]
  · simp [generatedVelocityEndpointGalerkinWholeState_apply,
      wholeRestartVelocityEndpointFiniteProjection_apply, waveMem]

/-- The actual complete velocity path is continuous on the fixed physical
interval. -/
theorem generatedVelocityEndpointGalerkinWholeState_continuous
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) :
    Continuous
      (generatedVelocityEndpointGalerkinWholeState ledger radius) := by
  unfold generatedVelocityEndpointGalerkinWholeState
    generatedVelocityEndpointGalerkinWholeStateAtTime
    finiteComplexVorticityState
  apply continuous_finsetSum
  intro wave waveMem
  apply
    (lp.singleContinuousLinearMap
      ℂ (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 wave).continuous.comp
  rw [continuous_iff_continuousAt]
  intro time
  have physical :=
    (ledger.family.stage radius).physical time.1 time.2
  exact
    (finiteStateVelocityTrajectoryWave_hasDerivAt
      (ledger.family.stage radius).trajectory time.1
      (finiteStateVorticityGenerator
        (wholeRestartModes radius) nu.coeff
        ((ledger.family.stage radius).trajectory time.1))
      wave physical.1).continuousAt.comp continuousAt_subtype_val

/-- Bounded-continuous realization of one actual velocity orbit. -/
def generatedVelocityEndpointGalerkinWholeBoundedPath
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) :
    BoundedContinuousFunction
      (Icc (0 : ℝ) 1) ComplexVorticityHilbertState :=
  BoundedContinuousFunction.mkOfCompact
    ⟨generatedVelocityEndpointGalerkinWholeState ledger radius,
      generatedVelocityEndpointGalerkinWholeState_continuous ledger radius⟩

/-- The complete actual velocity orbit in the common physical
`L²([0,1]; ℓ²)` carrier. -/
def generatedVelocityEndpointGalerkinSpaceTimePath
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) : SpaceTimeState 1 :=
  BoundedContinuousFunction.toLp 2 (commonTimeMeasure 1) ℂ
    (generatedVelocityEndpointGalerkinWholeBoundedPath ledger radius)

/-- The source-owned whole velocity family before compactness. -/
def generatedVelocityEndpointGalerkinSpaceTimePathFamily
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu) : Set (SpaceTimeState 1) :=
  Set.range (generatedVelocityEndpointGalerkinSpaceTimePath ledger)

/-! ## Spatial tail before the finite-observation quotient -/

/-- A wave outside the coordinate cube of radius `cutoff` lies above the
positive Euclidean frequency floor `(cutoff + 1)²`.  This is the exact
lattice bridge needed by the source-generated velocity tail ledger. -/
theorem lowFrequencyCube_outside_succ_sq_le
    (cutoff : ℕ)
    (wave : IntegerWavevector)
    (outside : wave ∉ lowFrequencyCube cutoff) :
    (((cutoff + 1 : ℕ) : ℝ) ^ 2) ≤ integerWaveNormSq wave := by
  rw [lowFrequencyCube, Fintype.mem_piFinset] at outside
  push Not at outside
  obtain ⟨coordinate, coordinateOutside⟩ := outside
  rw [Finset.mem_Icc] at coordinateOutside
  have coordinateSqLeShell :
      wave coordinate ^ 2 ≤ integerWaveShellSq wave := by
    unfold integerWaveShellSq
    exact Finset.single_le_sum
      (fun index _ => sq_nonneg (wave index))
      (Finset.mem_univ coordinate)
  have floorSqLeCoordinate :
      ((cutoff + 1 : ℕ) : ℤ) ^ 2 ≤ wave coordinate ^ 2 := by
    rw [sq_le_sq]
    have floorNonneg : 0 ≤ ((cutoff + 1 : ℕ) : ℤ) := by positivity
    rw [abs_of_nonneg floorNonneg]
    rcases not_and_or.mp coordinateOutside with left | right
    · have upper : wave coordinate ≤ -((cutoff : ℤ) + 1) := by omega
      have waveNonpos : wave coordinate ≤ 0 := by omega
      rw [abs_of_nonpos waveNonpos]
      norm_num only [Nat.cast_add, Nat.cast_one]
      omega
    · have lower : (cutoff : ℤ) + 1 ≤ wave coordinate := by omega
      have waveNonneg : 0 ≤ wave coordinate := by omega
      rw [abs_of_nonneg waveNonneg]
      norm_num only [Nat.cast_add, Nat.cast_one]
      omega
  have floorSqLeShell :
      ((cutoff + 1 : ℕ) : ℤ) ^ 2 ≤ integerWaveShellSq wave :=
    floorSqLeCoordinate.trans coordinateSqLeShell
  rw [integerWaveNormSq_eq_integerWaveShellSq]
  exact_mod_cast floorSqLeShell

/-- Before any coefficient quotient, the complete-carrier distance from an
actual Galerkin velocity to its low-frequency projection is paid by the
same physical high-frequency square written by the kinetic ledger. -/
theorem generatedVelocityEndpointGalerkinWholeState_sub_lowProjection_norm_sq_le_tail
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius cutoff : ℕ)
    (time : Icc (0 : ℝ) 1) :
    ‖generatedVelocityEndpointGalerkinWholeState ledger radius time -
        complexSharpSupportProjection (lowFrequencyCube cutoff)
          (generatedVelocityEndpointGalerkinWholeState ledger radius time)‖ ^ 2 ≤
      finiteStateVelocityHighFrequencySquare
        (wholeRestartModes radius) cutoff
        ((ledger.family.stage radius).trajectory time.1) := by
  let state : ComplexVorticityHilbertState :=
    generatedVelocityEndpointGalerkinWholeState ledger radius time
  have normIdentity :
      ‖state -
          complexSharpSupportProjection
            (lowFrequencyCube cutoff) state‖ ^ 2 =
        ∑' wave,
          ‖(state -
              complexSharpSupportProjection
                (lowFrequencyCube cutoff) state) wave‖ ^ 2 := by
    simpa using
      (lp.norm_rpow_eq_tsum
        (p := (2 : ℝ≥0∞)) (by norm_num)
        (state -
          complexSharpSupportProjection
            (lowFrequencyCube cutoff) state))
  change
    ‖state -
        complexSharpSupportProjection
          (lowFrequencyCube cutoff) state‖ ^ 2 ≤ _
  rw [normIdentity]
  rw [tsum_eq_sum
    (s := finiteStateVelocityHighFrequencyModes
      (wholeRestartModes radius) cutoff)]
  · rw [finiteStateVelocityHighFrequencySquare_eq_sum]
    apply Finset.sum_le_sum
    intro wave waveMem
    have modeMem : wave ∈ wholeRestartModes radius :=
      finiteStateVelocityHighFrequencyModes_subset
        (wholeRestartModes radius) cutoff waveMem
    by_cases retained : wave ∈ lowFrequencyCube cutoff
    · simp [complexSharpSupportProjection_apply, retained,
        complexCoordinateVectorNormSq_nonneg]
    · have projectionZero :
          complexSharpSupportProjection
              (lowFrequencyCube cutoff) state wave = 0 := by
        simp [complexSharpSupportProjection_apply, retained]
      rw [show
        (state -
            complexSharpSupportProjection
              (lowFrequencyCube cutoff) state) wave =
          state wave by exact sub_eq_self.mpr projectionZero]
      rw [generatedVelocityEndpointGalerkinWholeState_apply,
        if_pos modeMem]
      exact complexCoordinateVector_norm_sq_le_amplitudeSq _
  · intro wave waveNotMem
    by_cases modeMem : wave ∈ wholeRestartModes radius
    · have notHigh :
          ¬((((cutoff + 1 : ℕ) : ℝ) ^ 2) ≤
            integerWaveNormSq wave) := by
        intro high
        exact waveNotMem (Finset.mem_filter.mpr ⟨modeMem, high⟩)
      have retained : wave ∈ lowFrequencyCube cutoff := by
        by_contra outside
        exact notHigh
          (lowFrequencyCube_outside_succ_sq_le cutoff wave outside)
      simp [complexSharpSupportProjection_apply, retained]
    · have stateZero : state wave = 0 := by
        simp [state, generatedVelocityEndpointGalerkinWholeState_apply,
          modeMem]
      simp [complexSharpSupportProjection_apply, stateZero]

/-! ## Compact finite observations of the same actual paths -/

/-- Low-frequency observation of one actual whole velocity orbit, embedded
back into the common space-time carrier. -/
def projectedGeneratedVelocityEndpointGalerkinSpaceTimePath
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (observed : Finset IntegerWavevector)
    (radius : ℕ) : SpaceTimeState 1 :=
  observedPathToSpaceTime 1 observed
    (generatedFiniteObservedVelocityBoundedPath
      ledger observed radius)

/-- The compact space-time set generated by the uniform closure of one
fixed finite observation of all canonical radii. -/
def compactGeneratedVelocityEndpointObservedSpaceTimeSet
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (observed : Finset IntegerWavevector) : Set (SpaceTimeState 1) :=
  observedPathToSpaceTime 1 observed ''
    closure (generatedFiniteObservedVelocityPathFamily ledger observed)

theorem compactGeneratedVelocityEndpointObservedSpaceTimeSet_isCompact
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (observed : Finset IntegerWavevector) :
    IsCompact
      (compactGeneratedVelocityEndpointObservedSpaceTimeSet
        ledger observed) := by
  exact
    (generatedFiniteObservedVelocityPathFamily_isCompact_closure
      ledger observed).image
      (observedPathToSpaceTime 1 observed).continuous

theorem projectedGeneratedVelocityEndpointGalerkinSpaceTimePath_mem_compact
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (observed : Finset IntegerWavevector)
    (radius : ℕ) :
    projectedGeneratedVelocityEndpointGalerkinSpaceTimePath
        ledger observed radius ∈
      compactGeneratedVelocityEndpointObservedSpaceTimeSet
        ledger observed := by
  unfold projectedGeneratedVelocityEndpointGalerkinSpaceTimePath
    compactGeneratedVelocityEndpointObservedSpaceTimeSet
  refine ⟨generatedFiniteObservedVelocityBoundedPath
      ledger observed radius, ?_, rfl⟩
  exact subset_closure ⟨radius, rfl⟩

/-- The finite-observation path is exactly the restriction of the actual
whole velocity path, including radii at which an observed wave has not yet
entered the canonical support. -/
theorem finiteObservedEmbedding_generatedFiniteObservedVelocityTrajectory
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (observed : Finset IntegerWavevector)
    (radius : ℕ)
    (time : Icc (0 : ℝ) 1) :
    finiteObservedEmbedding observed
        (generatedFiniteObservedVelocityTrajectory
          ledger observed radius time) =
      complexSharpSupportProjection observed
        (generatedVelocityEndpointGalerkinWholeState
          ledger radius time) := by
  apply lp.ext
  funext wave
  by_cases observedMem : wave ∈ observed
  · rw [finiteObservedEmbedding_apply, dif_pos observedMem,
      complexSharpSupportProjection_apply, if_pos observedMem]
    change
      generatedVelocityEndpointGalerkinWavePath
          ledger radius wave time =
        generatedVelocityEndpointGalerkinWholeState
          ledger radius time wave
    rw [generatedVelocityEndpointGalerkinWholeState_apply]
    by_cases modeMem : wave ∈ wholeRestartModes radius
    · simp [generatedVelocityEndpointGalerkinWavePath, modeMem]
    · have stateZero :
          (ledger.family.stage radius).trajectory time.1 wave = 0 :=
        (ledger.family.stage radius).physical time.1 time.2 |>.2.1
          wave modeMem
      simp [generatedVelocityEndpointGalerkinWavePath,
        finiteStateVelocityCoefficient, modeMem, stateZero]
  · simp [finiteObservedEmbedding_apply,
      complexSharpSupportProjection_apply, observedMem]

/-- Almost-everywhere form of the same pre-quotient identity in the common
space-time carrier. -/
theorem generatedVelocityEndpointSpaceTime_sub_projection_coeFn_ae
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (observed : Finset IntegerWavevector)
    (radius : ℕ) :
    ∀ᵐ time ∂(commonTimeMeasure 1),
      (generatedVelocityEndpointGalerkinSpaceTimePath ledger radius -
        projectedGeneratedVelocityEndpointGalerkinSpaceTimePath
          ledger observed radius) time =
        generatedVelocityEndpointGalerkinWholeState ledger radius time -
          complexSharpSupportProjection observed
            (generatedVelocityEndpointGalerkinWholeState
              ledger radius time) := by
  have wholeAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure 1) ℂ
      (generatedVelocityEndpointGalerkinWholeBoundedPath ledger radius)
  have projectionAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure 1) ℂ
      ((finiteObservedEmbedding observed).compLeftContinuousBounded
        (Icc (0 : ℝ) 1)
        (generatedFiniteObservedVelocityBoundedPath
          ledger observed radius))
  have subAE := MeasureTheory.Lp.coeFn_sub
    (generatedVelocityEndpointGalerkinSpaceTimePath ledger radius)
    (projectedGeneratedVelocityEndpointGalerkinSpaceTimePath
      ledger observed radius)
  filter_upwards [subAE, wholeAE, projectionAE] with
    time subEq wholeEq projectionEq
  rw [subEq]
  change
    ((BoundedContinuousFunction.toLp 2
      (commonTimeMeasure 1) ℂ)
      (generatedVelocityEndpointGalerkinWholeBoundedPath
        ledger radius)) time -
        ((BoundedContinuousFunction.toLp 2
          (commonTimeMeasure 1) ℂ)
          ((finiteObservedEmbedding observed).compLeftContinuousBounded
            (Icc (0 : ℝ) 1)
            (generatedFiniteObservedVelocityBoundedPath
              ledger observed radius))) time = _
  rw [wholeEq, projectionEq]
  change
    generatedVelocityEndpointGalerkinWholeState ledger radius time -
        finiteObservedEmbedding observed
          (generatedFiniteObservedVelocityTrajectory
            ledger observed radius time) = _
  rw [finiteObservedEmbedding_generatedFiniteObservedVelocityTrajectory]

/-- Exact integral identity for the projection loss of one actual path. -/
theorem generatedVelocityEndpointSpaceTime_projection_norm_sq_eq_intervalIntegral
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (observed : Finset IntegerWavevector)
    (radius : ℕ) :
    ‖generatedVelocityEndpointGalerkinSpaceTimePath ledger radius -
        projectedGeneratedVelocityEndpointGalerkinSpaceTimePath
          ledger observed radius‖ ^ 2 =
      ∫ time in (0 : ℝ)..1,
        ‖generatedVelocityEndpointGalerkinWholeStateAtTime
              ledger radius time -
            complexSharpSupportProjection observed
              (generatedVelocityEndpointGalerkinWholeStateAtTime
                ledger radius time)‖ ^ 2 := by
  rw [spaceTime_norm_sq_eq_integral]
  calc
    (∫ time,
        ‖(generatedVelocityEndpointGalerkinSpaceTimePath ledger radius -
            projectedGeneratedVelocityEndpointGalerkinSpaceTimePath
              ledger observed radius) time‖ ^ 2
          ∂(commonTimeMeasure 1)) =
        ∫ time,
          ‖generatedVelocityEndpointGalerkinWholeState ledger radius time -
              complexSharpSupportProjection observed
                (generatedVelocityEndpointGalerkinWholeState
                  ledger radius time)‖ ^ 2
            ∂(commonTimeMeasure 1) := by
      apply integral_congr_ae
      filter_upwards [
        generatedVelocityEndpointSpaceTime_sub_projection_coeFn_ae
          ledger observed radius] with time pointwiseEq
      rw [pointwiseEq]
    _ = _ := by
      simpa [generatedVelocityEndpointGalerkinWholeState] using
        (commonTime_integral_eq_intervalIntegral
          1 (by norm_num)
          (fun time =>
            ‖generatedVelocityEndpointGalerkinWholeStateAtTime
                  ledger radius time -
                complexSharpSupportProjection observed
                  (generatedVelocityEndpointGalerkinWholeStateAtTime
                    ledger radius time)‖ ^ 2))

/-- The common-carrier projection loss is bounded by the actual physical
velocity tail before any finite-observation quotient. -/
theorem generatedVelocityEndpointSpaceTime_projection_norm_sq_le_tail_integral
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (cutoff radius : ℕ) :
    ‖generatedVelocityEndpointGalerkinSpaceTimePath ledger radius -
        projectedGeneratedVelocityEndpointGalerkinSpaceTimePath
          ledger (lowFrequencyCube cutoff) radius‖ ^ 2 ≤
      ∫ time in (0 : ℝ)..1,
        finiteStateVelocityHighFrequencySquare
          (wholeRestartModes radius) cutoff
          ((ledger.family.stage radius).trajectory time) := by
  rw [generatedVelocityEndpointSpaceTime_projection_norm_sq_eq_intervalIntegral]
  have wholeContinuousOn :
      ContinuousOn
        (generatedVelocityEndpointGalerkinWholeStateAtTime ledger radius)
        (Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous
      (generatedVelocityEndpointGalerkinWholeState ledger radius)
    exact generatedVelocityEndpointGalerkinWholeState_continuous ledger radius
  have projectionContinuousOn :
      ContinuousOn
        (fun time =>
          sharpSupportProjectionCLM (lowFrequencyCube cutoff)
            (generatedVelocityEndpointGalerkinWholeStateAtTime
              ledger radius time))
        (Icc (0 : ℝ) 1) := by
    change
      ContinuousOn
        ((sharpSupportProjectionCLM (lowFrequencyCube cutoff)) ∘
          generatedVelocityEndpointGalerkinWholeStateAtTime ledger radius)
        (Icc (0 : ℝ) 1)
    exact
      (sharpSupportProjectionCLM
          (lowFrequencyCube cutoff)).continuous.comp_continuousOn
        wholeContinuousOn
  have differenceIntegrable :
      IntervalIntegrable
        (fun time =>
          ‖generatedVelocityEndpointGalerkinWholeStateAtTime
                ledger radius time -
              complexSharpSupportProjection (lowFrequencyCube cutoff)
                (generatedVelocityEndpointGalerkinWholeStateAtTime
                  ledger radius time)‖ ^ 2)
        volume 0 1 := by
    have clmIntegrable :
        IntervalIntegrable
          (fun time =>
            ‖generatedVelocityEndpointGalerkinWholeStateAtTime
                  ledger radius time -
                sharpSupportProjectionCLM (lowFrequencyCube cutoff)
                  (generatedVelocityEndpointGalerkinWholeStateAtTime
                    ledger radius time)‖ ^ 2)
          volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by norm_num)]
      exact (wholeContinuousOn.sub projectionContinuousOn).norm.pow 2
    simpa only [sharpSupportProjectionCLM_apply] using clmIntegrable
  have tailIntegrable :
      IntervalIntegrable
        (fun time =>
          finiteStateVelocityHighFrequencySquare
            (wholeRestartModes radius) cutoff
            ((ledger.family.stage radius).trajectory time))
        volume 0 1 := by
    exact
      GeneratedWholeRestartVelocityEndpointGalerkinStage.highFrequencySquare_intervalIntegrable
        (ledger.family.stage radius) cutoff ⟨1, by norm_num⟩
  apply intervalIntegral.integral_mono_on
    (by norm_num) differenceIntegrable tailIntegrable
  intro time timeMem
  change
    ‖generatedVelocityEndpointGalerkinWholeState ledger radius
          ⟨time, timeMem⟩ -
        complexSharpSupportProjection (lowFrequencyCube cutoff)
          (generatedVelocityEndpointGalerkinWholeState ledger radius
            ⟨time, timeMem⟩)‖ ^ 2 ≤ _
  exact
    generatedVelocityEndpointGalerkinWholeState_sub_lowProjection_norm_sq_le_tail
      ledger radius cutoff ⟨time, timeMem⟩

/-- Radius-uniform projection loss generated by the exact kinetic/viscous
ledger.  The cutoff is an output index of the bound, not a source premise. -/
theorem generatedVelocityEndpointSpaceTime_projection_norm_sq_le_uniformTail
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (cutoff radius : ℕ) :
    ‖generatedVelocityEndpointGalerkinSpaceTimePath ledger radius -
        projectedGeneratedVelocityEndpointGalerkinSpaceTimePath
          ledger (lowFrequencyCube cutoff) radius‖ ^ 2 ≤
      ((1 / 2 : ℝ) *
          ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2) /
        (nu.coeff *
          ((2 * Real.pi) ^ 2 *
            (((cutoff + 1 : ℕ) : ℝ) ^ 2))) := by
  let weight : ℝ :=
    (2 * Real.pi) ^ 2 * (((cutoff + 1 : ℕ) : ℝ) ^ 2)
  have weightPos : 0 < weight := by
    dsimp [weight]
    positivity
  have denominatorPos : 0 < nu.coeff * weight :=
    mul_pos nu.coeff_pos weightPos
  have tailLe :=
    generatedVelocityEndpointSpaceTime_projection_norm_sq_le_tail_integral
      ledger cutoff radius
  apply tailLe.trans
  rw [le_div_iff₀ denominatorPos]
  calc
    (∫ time in (0 : ℝ)..1,
            finiteStateVelocityHighFrequencySquare
              (wholeRestartModes radius) cutoff
              ((ledger.family.stage radius).trajectory time)) *
          (nu.coeff * weight) =
        nu.coeff *
          (weight *
            (∫ time in (0 : ℝ)..1,
              finiteStateVelocityHighFrequencySquare
                (wholeRestartModes radius) cutoff
                ((ledger.family.stage radius).trajectory time))) := by ring
    _ ≤ (1 / 2 : ℝ) *
          ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 :=
      ledger.velocity_highFrequency_integral_le
        radius cutoff ⟨1, by norm_num⟩

/-- Every actual canonical-radius path is uniformly approximated by one
source-independent finite observation.  The cutoff is generated in the
conclusion from the exact endpoint norm and viscosity. -/
theorem exists_lowFrequencyCube_generatedVelocityEndpoint_uniformly_close
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (ε : ℝ)
    (εPos : 0 < ε) :
    ∃ cutoff : ℕ,
      ∀ radius : ℕ,
        dist
            (generatedVelocityEndpointGalerkinSpaceTimePath ledger radius)
            (projectedGeneratedVelocityEndpointGalerkinSpaceTimePath
              ledger (lowFrequencyCube cutoff) radius) < ε := by
  let numerator : ℝ :=
    (1 / 2 : ℝ) *
      ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2
  let coefficient : ℝ := nu.coeff * (2 * Real.pi) ^ 2
  have numeratorNonneg : 0 ≤ numerator := by
    exact mul_nonneg (by norm_num) (sq_nonneg _)
  have coefficientPos : 0 < coefficient := by
    dsimp [coefficient]
    exact mul_pos nu.coeff_pos
      (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))
  have εSqPos : 0 < ε ^ 2 := sq_pos_of_pos εPos
  obtain ⟨cutoff, cutoffGt⟩ :=
    exists_nat_gt (numerator / (coefficient * ε ^ 2))
  have ratioNonneg :
      0 ≤ numerator / (coefficient * ε ^ 2) :=
    div_nonneg numeratorNonneg
      (mul_nonneg coefficientPos.le εSqPos.le)
  have cutoffRealPos : 0 < (cutoff : ℝ) :=
    ratioNonneg.trans_lt cutoffGt
  have cutoffLeSuccSq :
      (cutoff : ℝ) ≤ (((cutoff + 1 : ℕ) : ℝ) ^ 2) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have numeratorLtCutoff :
      numerator < (cutoff : ℝ) * (coefficient * ε ^ 2) :=
    (div_lt_iff₀ (mul_pos coefficientPos εSqPos)).1 cutoffGt
  have uniformRatioLt :
      numerator /
          (coefficient * (((cutoff + 1 : ℕ) : ℝ) ^ 2)) <
        ε ^ 2 := by
    apply
      (div_lt_iff₀
        (mul_pos coefficientPos (by positivity))).2
    calc
      numerator <
          (cutoff : ℝ) * (coefficient * ε ^ 2) :=
        numeratorLtCutoff
      _ ≤
          (((cutoff + 1 : ℕ) : ℝ) ^ 2) *
            (coefficient * ε ^ 2) :=
        mul_le_mul_of_nonneg_right cutoffLeSuccSq
          (mul_nonneg coefficientPos.le εSqPos.le)
      _ =
          ε ^ 2 *
            (coefficient * (((cutoff + 1 : ℕ) : ℝ) ^ 2)) := by
        ring
  refine ⟨cutoff, ?_⟩
  intro radius
  rw [dist_eq_norm]
  have normSqLe :=
    generatedVelocityEndpointSpaceTime_projection_norm_sq_le_uniformTail
      ledger cutoff radius
  have normSqLt :
      ‖generatedVelocityEndpointGalerkinSpaceTimePath ledger radius -
          projectedGeneratedVelocityEndpointGalerkinSpaceTimePath
            ledger (lowFrequencyCube cutoff) radius‖ ^ 2 < ε ^ 2 := by
    exact normSqLe.trans_lt (by
      simpa [numerator, coefficient, mul_assoc] using uniformRatioLt)
  nlinarith [
    norm_nonneg
      (generatedVelocityEndpointGalerkinSpaceTimePath ledger radius -
        projectedGeneratedVelocityEndpointGalerkinSpaceTimePath
          ledger (lowFrequencyCube cutoff) radius)]

/-! ## Whole-carrier compact closure -/

/-- The full family of actual unforced velocity paths is totally bounded in
the common physical space-time carrier.  Finite observations are consumed
only as compact approximants; all tail responsibility is paid beforehand. -/
theorem generatedVelocityEndpointGalerkinSpaceTimePathFamily_totallyBounded
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu) :
    TotallyBounded
      (generatedVelocityEndpointGalerkinSpaceTimePathFamily ledger) := by
  rw [Metric.totallyBounded_iff]
  intro ε εPos
  have halfεPos : 0 < ε / 2 := by linarith
  obtain ⟨cutoff, uniformlyClose⟩ :=
    exists_lowFrequencyCube_generatedVelocityEndpoint_uniformly_close
      ledger (ε / 2) halfεPos
  let compactSet : Set (SpaceTimeState 1) :=
    compactGeneratedVelocityEndpointObservedSpaceTimeSet
      ledger (lowFrequencyCube cutoff)
  have compactSetCompact : IsCompact compactSet := by
    exact compactGeneratedVelocityEndpointObservedSpaceTimeSet_isCompact
      ledger (lowFrequencyCube cutoff)
  obtain ⟨centers, centersFinite, centersCover⟩ :=
    (Metric.totallyBounded_iff.mp compactSetCompact.totallyBounded)
      (ε / 2) halfεPos
  refine ⟨centers, centersFinite, ?_⟩
  intro member memberMem
  rcases memberMem with ⟨radius, rfl⟩
  let projection : SpaceTimeState 1 :=
    projectedGeneratedVelocityEndpointGalerkinSpaceTimePath
      ledger (lowFrequencyCube cutoff) radius
  have projectionMem : projection ∈ compactSet := by
    exact
      projectedGeneratedVelocityEndpointGalerkinSpaceTimePath_mem_compact
        ledger (lowFrequencyCube cutoff) radius
  rcases Set.mem_iUnion.mp (centersCover projectionMem) with
    ⟨center, centerCover⟩
  rcases Set.mem_iUnion.mp centerCover with
    ⟨centerMem, projectionInBall⟩
  refine Set.mem_iUnion.mpr ⟨center, ?_⟩
  refine Set.mem_iUnion.mpr ⟨centerMem, ?_⟩
  rw [Metric.mem_ball] at projectionInBall ⊢
  have memberClose :
      dist
          (generatedVelocityEndpointGalerkinSpaceTimePath ledger radius)
          projection < ε / 2 :=
    uniformlyClose radius
  calc
    dist
        (generatedVelocityEndpointGalerkinSpaceTimePath ledger radius)
        center ≤
      dist
          (generatedVelocityEndpointGalerkinSpaceTimePath ledger radius)
          projection + dist projection center :=
      dist_triangle _ _ _
    _ < ε := by linarith

/-- Compact closure of the entire source-generated actual velocity family.
This is the whole-carrier compactness theorem consumed by nonlinear weak
passage; no target limit or subsequence appears in its mouth. -/
theorem generatedVelocityEndpointGalerkinSpaceTimePathFamily_isCompact_closure
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu) :
    IsCompact
      (closure
        (generatedVelocityEndpointGalerkinSpaceTimePathFamily ledger)) := by
  exact
    (generatedVelocityEndpointGalerkinSpaceTimePathFamily_totallyBounded
      ledger).closure.isCompact_of_isClosed isClosed_closure

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinStrongSpaceTimeCompactness
end NavierStokes
end SaturationMonoid
