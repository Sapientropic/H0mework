import H0mework.NavierStokes.VelocityGalerkin.VelocityWeakLimit
import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeGradientLowerSemicontinuity
import H0mework.NavierStokes.Fourier.TransverseSpaceTimeNonlinearRow
import H0mework.NavierStokes.ShellSources.InfiniteMildPhysicalLimit

/-!
# Source-generated Leray--Hopf receipt for the whole velocity endpoint

The bounded whole-restart source already generates one common strong
space-time subsequence of actual unforced velocity Galerkin writes.  This
module keeps the data discarded by the first weak-NSE wrapper and transports
the exact kinetic/viscous ledger through that same subsequence.

The source-facing producer accepts no target state, subsequence, cutoff,
energy certificate, or convergence witness.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointLerayHopfReceipt

open scoped BigOperators ENNReal Interval Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildPhysicalLimit
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinStrongSpaceTimeSubsequence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinNonlinearSpaceTimePassage
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinVelocityWeakLimit
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity

noncomputable section

/-! ## The finite Hodge payment before passage to the limit -/

/-- One velocity row's physical gradient square is paid by the vorticity
row that generated it.  The ambient row norm is the repository's sup norm,
so this statement first uses the exact Euclidean Hodge identity and then the
already proved sup-to-Euclidean contraction. -/
theorem finiteStateWholeVelocity_gradientRow_le_vorticityRow
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (state : ComplexVorticityHilbertState)
    (transverse : FiniteStateTransverseOn modes state)
    (wave : IntegerWavevector) :
    (2 * Real.pi) ^ 2 * integerWaveNormSq wave *
        ‖finiteStateWholeVelocity modes state wave‖ ^ 2 ≤
      complexCoordinateVectorNormSq (state wave) := by
  by_cases waveMem : wave ∈ modes
  · have waveNe : wave ≠ 0 := fun waveZero =>
      zeroNotMem (waveZero ▸ waveMem)
    have denominatorPos :
        0 < (2 * Real.pi) ^ 2 * integerWaveNormSq wave := by
      exact mul_pos (sq_pos_of_pos (by positivity))
        (integerWaveNormSq_pos waveNe)
    have normLe :
        ‖finiteStateWholeVelocity modes state wave‖ ^ 2 ≤
          complexCoordinateVectorNormSq
            (finiteStateVelocityCoefficient state wave) := by
      rw [finiteStateWholeVelocity_apply, if_pos waveMem]
      simpa only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
        using complexCoordinateVector_norm_sq_le_amplitudeSq
          (finiteStateVelocityCoefficient state wave)
    have hodgeEq :
        complexCoordinateVectorNormSq
            (finiteStateVelocityCoefficient state wave) =
          complexCoordinateVectorNormSq (state wave) /
            ((2 * Real.pi) ^ 2 * integerWaveNormSq wave) := by
      rw [finiteStateVelocityCoefficient,
        biotSavartVelocityCoefficient_normSq_of_transverse
          wave (state wave) waveNe (transverse wave waveMem)]
    calc
      (2 * Real.pi) ^ 2 * integerWaveNormSq wave *
          ‖finiteStateWholeVelocity modes state wave‖ ^ 2 ≤
        (2 * Real.pi) ^ 2 * integerWaveNormSq wave *
          (complexCoordinateVectorNormSq (state wave) /
            ((2 * Real.pi) ^ 2 * integerWaveNormSq wave)) :=
        mul_le_mul_of_nonneg_left (normLe.trans_eq hodgeEq)
          denominatorPos.le
      _ = complexCoordinateVectorNormSq (state wave) := by
        exact mul_div_cancel₀ _ denominatorPos.ne'
  · rw [finiteStateWholeVelocity_apply, if_neg waveMem]
    simp
    exact complexCoordinateVectorNormSq_nonneg _

/-- Every finite collection of physical velocity gradient rows is paid by
the actual vorticity-mass integral of the same generated Galerkin event. -/
theorem generatedVelocityEndpointGalerkin_gradientDensity_finsetSum_le
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ)
    (waves : Finset IntegerWavevector) :
    (2 * Real.pi) ^ 2 *
        (∑ wave ∈ waves,
          wholeSpaceTimeVorticityGradientDensity 1
            (generatedVelocityEndpointGalerkinSpaceTimePath ledger radius)
            wave) ≤
      ∫ time in (0 : ℝ)..1,
        finiteStateVorticityMass
          (wholeRestartModes radius)
          ((ledger.family.stage radius).trajectory time) := by
  let modes := wholeRestartModes radius
  let stage := ledger.family.stage radius
  let velocityTrajectory : ℝ → ComplexVorticityHilbertState :=
    generatedVelocityEndpointGalerkinWholeStateAtTime ledger radius
  have velocityContinuous :
      ContinuousOn velocityTrajectory (Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous
      (generatedVelocityEndpointGalerkinWholeState ledger radius)
    exact generatedVelocityEndpointGalerkinWholeState_continuous ledger radius
  have statePathEq :
      generatedVelocityEndpointGalerkinSpaceTimePath ledger radius =
        wholeTrajectorySpaceTimePath 1 velocityTrajectory
          velocityContinuous := by
    rfl
  have rowIntegrable :
      ∀ wave : IntegerWavevector,
        IntervalIntegrable
          (fun time =>
            integerWaveNormSq wave *
              ‖velocityTrajectory time wave‖ ^ 2)
          volume 0 1 := by
    intro wave
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    have rowContinuous :
        ContinuousOn
          (fun time => velocityTrajectory time wave)
          (Icc (0 : ℝ) 1) :=
      (lp.evalCLM ℂ
        (fun _ : IntegerWavevector => ComplexCoordinateVector)
        2 wave).continuous.comp_continuousOn velocityContinuous
    exact continuousOn_const.mul (rowContinuous.norm.pow 2)
  have baseEq :
      (∑ wave ∈ waves,
        wholeSpaceTimeVorticityGradientDensity 1
          (generatedVelocityEndpointGalerkinSpaceTimePath ledger radius)
          wave) =
        ∫ time in (0 : ℝ)..1,
          ∑ wave ∈ waves,
            integerWaveNormSq wave *
              ‖velocityTrajectory time wave‖ ^ 2 := by
    rw [statePathEq]
    calc
      (∑ wave ∈ waves,
          wholeSpaceTimeVorticityGradientDensity 1
            (wholeTrajectorySpaceTimePath 1 velocityTrajectory
              velocityContinuous) wave) =
          ∑ wave ∈ waves,
            ∫ time in (0 : ℝ)..1,
              integerWaveNormSq wave *
                ‖velocityTrajectory time wave‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro wave _waveMem
        unfold wholeSpaceTimeVorticityGradientDensity
        rw [
          fixedWaveSpaceTimeRestriction_wholeTrajectory_norm_sq_eq_intervalIntegral
            1 (by norm_num) velocityTrajectory velocityContinuous wave,
          intervalIntegral.integral_const_mul]
      _ = _ := by
        symm
        exact intervalIntegral.integral_finsetSum
          (fun wave _waveMem => rowIntegrable wave)
  rw [baseEq, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      (continuousOn_const.mul
        (continuousOn_finsetSum waves fun wave _ =>
          continuousOn_const.mul
            (((lp.evalCLM ℂ
              (fun _ : IntegerWavevector => ComplexCoordinateVector)
              2 wave).continuous.comp_continuousOn velocityContinuous).norm.pow 2)))
  · exact
      GeneratedWholeRestartVelocityEndpointGalerkinStage.vorticityMass_intervalIntegrable
        stage ⟨1, by norm_num⟩
  · intro time timeMem
    let active := waves.filter fun wave => wave ∈ modes
    have removeSilent :
        (∑ wave ∈ waves,
          integerWaveNormSq wave *
            ‖velocityTrajectory time wave‖ ^ 2) =
          ∑ wave ∈ active,
            integerWaveNormSq wave *
              ‖velocityTrajectory time wave‖ ^ 2 := by
      classical
      rw [show active = waves.filter (fun wave => wave ∈ modes) from rfl,
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro wave _waveMem
      by_cases waveInModes : wave ∈ modes
      · simp [waveInModes]
      · have velocityZero :
            velocityTrajectory time wave = 0 := by
          simp [velocityTrajectory,
            generatedVelocityEndpointGalerkinWholeStateAtTime,
            modes, waveInModes]
        simp [waveInModes, velocityZero]
    rw [removeSilent, Finset.mul_sum]
    calc
      (∑ wave ∈ active,
          (2 * Real.pi) ^ 2 *
            (integerWaveNormSq wave *
              ‖velocityTrajectory time wave‖ ^ 2)) ≤
        ∑ wave ∈ active,
          complexCoordinateVectorNormSq (stage.trajectory time wave) := by
        apply Finset.sum_le_sum
        intro wave waveMem
        have pointwise :=
          finiteStateWholeVelocity_gradientRow_le_vorticityRow
            modes
            (zero_not_mem_puncturedIntegerWaveFrequencyCube radius)
            (stage.trajectory time)
            (fun output _outputMem =>
              (stage.physical time timeMem).2.2.1 output)
            wave
        simpa [velocityTrajectory,
          generatedVelocityEndpointGalerkinWholeStateAtTime,
          finiteStateWholeVelocity, stage, modes, mul_assoc] using pointwise
      _ ≤ ∑ wave ∈ modes,
          complexCoordinateVectorNormSq (stage.trajectory time wave) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro wave waveMem
          exact (Finset.mem_filter.mp waveMem).2
        · intro wave _waveNotMem _waveMem
          exact complexCoordinateVectorNormSq_nonneg _
      _ = finiteStateVorticityMass modes (stage.trajectory time) := rfl

/-! ## Uniform viscous payment and lower-semicontinuous limit -/

/-- The internally generated whole-lattice gradient ceiling. -/
def generatedVelocityEndpointGradientCeiling
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu) : ℝ :=
  ((1 / 2 : ℝ) * ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2) /
    (nu.coeff * (2 * Real.pi) ^ 2)

theorem generatedVelocityEndpointGradientCeiling_nonneg
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu) :
    0 ≤ generatedVelocityEndpointGradientCeiling ledger := by
  unfold generatedVelocityEndpointGradientCeiling
  exact div_nonneg
    (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg nu.coeff_pos.le (sq_nonneg _))

/-- The exact kinetic ledger pays every finite partial sum of the velocity
gradient density, uniformly in the generated Galerkin radius. -/
theorem generatedVelocityEndpointGalerkin_gradientDensity_finsetSum_le_ceiling
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ)
    (waves : Finset IntegerWavevector) :
    (∑ wave ∈ waves,
        wholeSpaceTimeVorticityGradientDensity 1
          (generatedVelocityEndpointGalerkinSpaceTimePath ledger radius)
          wave) ≤
      generatedVelocityEndpointGradientCeiling ledger := by
  have hodgePayment :=
    generatedVelocityEndpointGalerkin_gradientDensity_finsetSum_le
      ledger radius waves
  have scaledPayment :=
    mul_le_mul_of_nonneg_left hodgePayment nu.coeff_pos.le
  have viscousPayment :=
    ledger.viscous_integral_le radius ⟨1, by norm_num⟩
  have totalPayment :
      (nu.coeff * (2 * Real.pi) ^ 2) *
          (∑ wave ∈ waves,
            wholeSpaceTimeVorticityGradientDensity 1
              (generatedVelocityEndpointGalerkinSpaceTimePath ledger radius)
              wave) ≤
        (1 / 2 : ℝ) *
          ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 := by
    exact (by
      calc
        (nu.coeff * (2 * Real.pi) ^ 2) *
              (∑ wave ∈ waves,
                wholeSpaceTimeVorticityGradientDensity 1
                  (generatedVelocityEndpointGalerkinSpaceTimePath
                    ledger radius) wave) =
            nu.coeff *
              ((2 * Real.pi) ^ 2 *
                (∑ wave ∈ waves,
                  wholeSpaceTimeVorticityGradientDensity 1
                    (generatedVelocityEndpointGalerkinSpaceTimePath
                      ledger radius) wave)) := by ring
        _ ≤ nu.coeff *
              (∫ time in (0 : ℝ)..1,
                finiteStateVorticityMass
                  (wholeRestartModes radius)
                  ((ledger.family.stage radius).trajectory time)) :=
            scaledPayment
        _ ≤ _ := viscousPayment)
  unfold generatedVelocityEndpointGradientCeiling
  apply (le_div_iff₀ (mul_pos nu.coeff_pos
    (sq_pos_of_pos (by positivity)))).2
  simpa [mul_comm] using totalPayment

/-- Any strong limit of the actual generated radius family inherits the
whole-lattice velocity gradient summability and the source-paid ceiling. -/
theorem generatedVelocityEndpoint_stateLimit_gradientMass_le
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (subsequence : ℕ → ℕ)
    (stateLimit : SpaceTimeState 1)
    (stateTendsto :
      Tendsto
        (fun index =>
          generatedVelocityEndpointGalerkinSpaceTimePath
            ledger (subsequence index))
        atTop (𝓝 stateLimit)) :
    Summable
        (fun wave : IntegerWavevector =>
          wholeSpaceTimeVorticityGradientDensity 1 stateLimit wave) ∧
      wholeSpaceTimeVorticityGradientMass 1 stateLimit ≤
        generatedVelocityEndpointGradientCeiling ledger := by
  let stateSequence : ℕ → SpaceTimeState 1 :=
    fun index =>
      generatedVelocityEndpointGalerkinSpaceTimePath
        ledger (subsequence index)
  have finiteSumBound :
      ∀ index : ℕ, ∀ waves : Finset IntegerWavevector,
        (∑ wave ∈ waves,
          wholeSpaceTimeVorticityGradientDensity 1
            (stateSequence index) wave) ≤
          generatedVelocityEndpointGradientCeiling ledger := by
    intro index waves
    exact
      generatedVelocityEndpointGalerkin_gradientDensity_finsetSum_le_ceiling
        ledger (subsequence index) waves
  constructor
  · exact
      summable_wholeSpaceTimeVorticityGradientDensity_of_uniform_bound
        1 stateSequence stateLimit stateTendsto
        (generatedVelocityEndpointGradientCeiling ledger)
        finiteSumBound
  · exact
      wholeSpaceTimeVorticityGradientMass_le_of_uniform_bound
        1 stateSequence stateLimit stateTendsto
        (generatedVelocityEndpointGradientCeiling ledger)
        finiteSumBound

/-- Product form of the same limit budget, retaining the exact viscosity and
Fourier normalization without division. -/
theorem generatedVelocityEndpoint_stateLimit_viscousGradientMass_le
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (subsequence : ℕ → ℕ)
    (stateLimit : SpaceTimeState 1)
    (stateTendsto :
      Tendsto
        (fun index =>
          generatedVelocityEndpointGalerkinSpaceTimePath
            ledger (subsequence index))
        atTop (𝓝 stateLimit)) :
    nu.coeff * (2 * Real.pi) ^ 2 *
        wholeSpaceTimeVorticityGradientMass 1 stateLimit ≤
      (1 / 2 : ℝ) *
        ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 := by
  have massLe :=
    (generatedVelocityEndpoint_stateLimit_gradientMass_le
      ledger subsequence stateLimit stateTendsto).2
  have coefficientPos :
      0 < nu.coeff * (2 * Real.pi) ^ 2 :=
    mul_pos nu.coeff_pos (sq_pos_of_pos (by positivity))
  unfold generatedVelocityEndpointGradientCeiling at massLe
  simpa [mul_comm] using (le_div_iff₀ coefficientPos).1 massLe

/-! ## Space-time kinetic mass on the same physical limit -/

theorem finiteStateWholeVelocity_coefficientEnstrophy_eq_two_kineticEnergy
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteStateVorticityCoefficientEnstrophy modes
        (finiteStateWholeVelocity modes state) =
      2 * finiteStateVorticityKineticEnergy modes state := by
  unfold finiteStateVorticityCoefficientEnstrophy
  calc
    (∑ wave ∈ modes,
        complexCoordinateAmplitudeSq
          (finiteStateWholeVelocity modes state wave)) =
      ∑ wave ∈ modes, velocityRowAmplitude state wave ^ 2 := by
        apply Finset.sum_congr rfl
        intro wave waveMem
        rw [finiteStateWholeVelocity_apply, if_pos waveMem,
          velocityRowAmplitude_sq]
    _ = _ :=
      velocityRowAmplitude_sq_sum_eq_two_kineticEnergy modes state

/-- The complete time-`L²` kinetic mass of every generated Galerkin path is
paid by the source endpoint square, uniformly in the internal radius. -/
theorem generatedVelocityEndpointGalerkinSpaceTimePath_norm_sq_le_endpoint
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) :
    ‖generatedVelocityEndpointGalerkinSpaceTimePath ledger radius‖ ^ 2 ≤
      ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 := by
  let modes := wholeRestartModes radius
  let stage := ledger.family.stage radius
  let velocityTrajectory : ℝ → ComplexVorticityHilbertState :=
    generatedVelocityEndpointGalerkinWholeStateAtTime ledger radius
  have velocityContinuous :
      ContinuousOn velocityTrajectory (Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous
      (generatedVelocityEndpointGalerkinWholeState ledger radius)
    exact generatedVelocityEndpointGalerkinWholeState_continuous ledger radius
  rw [generatedVelocityEndpointGalerkinSpaceTimePath_norm_sq_eq_intervalIntegral]
  calc
    (∫ time in (0 : ℝ)..1, ‖velocityTrajectory time‖ ^ 2) ≤
        ∫ _time in (0 : ℝ)..1,
          ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num)
      · exact ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
          (velocityContinuous.norm.pow 2)
      · exact intervalIntegrable_const
      · intro time timeMem
        have supported :
            ∀ wave, wave ∉ modes →
              finiteStateWholeVelocity modes (stage.trajectory time) wave = 0 := by
          intro wave waveNotMem
          simp [finiteStateWholeVelocity_apply, waveNotMem]
        have ambientLe :=
          complexVorticityHilbertState_norm_sq_le_coefficientEnstrophy
            modes
            (finiteStateWholeVelocity modes (stage.trajectory time))
            supported
        rw [finiteStateWholeVelocity_coefficientEnstrophy_eq_two_kineticEnergy]
          at ambientLe
        have energyLe := ledger.kinetic_energy_le radius ⟨time, timeMem⟩
        have trajectoryEq :
            velocityTrajectory time =
              finiteStateWholeVelocity modes (stage.trajectory time) := by
          rfl
        rw [trajectoryEq]
        nlinarith
    _ = ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 := by
      simp

/-- Strong whole-carrier passage retains the source-paid integrated kinetic
mass.  This is an actual time-`L²` energy bound; the pointwise prefix energy
inequality remains attached to the downstream continuous representative. -/
theorem generatedVelocityEndpoint_stateLimit_spaceTime_norm_sq_le_endpoint
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (subsequence : ℕ → ℕ)
    (stateLimit : SpaceTimeState 1)
    (stateTendsto :
      Tendsto
        (fun index =>
          generatedVelocityEndpointGalerkinSpaceTimePath
            ledger (subsequence index))
        atTop (𝓝 stateLimit)) :
    ‖stateLimit‖ ^ 2 ≤
      ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 := by
  exact le_of_tendsto' (stateTendsto.norm.pow 2) fun index =>
    generatedVelocityEndpointGalerkinSpaceTimePath_norm_sq_le_endpoint
      ledger (subsequence index)

/-! ## Divergence-free and Fourier-real closure on the same subsequence -/

/-- The actual velocity Galerkin path lifted to the closed transverse
space-time carrier before taking any limit. -/
def generatedVelocityEndpointGalerkinTransverseSpaceTimePath
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) : TransverseSpaceTimeState 1 :=
  wholeTransverseTrajectorySpaceTimePath 1
    (generatedVelocityEndpointGalerkinWholeStateAtTime ledger radius)
    (by
      rw [continuousOn_iff_continuous_restrict]
      change Continuous
        (generatedVelocityEndpointGalerkinWholeState ledger radius)
      exact generatedVelocityEndpointGalerkinWholeState_continuous ledger radius)
    (fun time _timeMem =>
      generatedVelocityEndpointGalerkinWholeStateAtTime_transverse
        ledger radius time)

theorem generatedVelocityEndpointGalerkinTransverseSpaceTimePath_inclusion
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ) :
    transverseSpaceTimeInclusion 1
        (generatedVelocityEndpointGalerkinTransverseSpaceTimePath
          ledger radius) =
      generatedVelocityEndpointGalerkinSpaceTimePath ledger radius := by
  rw [generatedVelocityEndpointGalerkinTransverseSpaceTimePath,
    transverseSpaceTimeInclusion_wholeTransverseTrajectory]
  rfl

/-- Strong ambient convergence of the generated velocity family produces a
strong limit in the closed divergence-free carrier. -/
theorem generatedVelocityEndpoint_stateLimit_transverseLift
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (subsequence : ℕ → ℕ)
    (stateLimit : SpaceTimeState 1)
    (stateTendsto :
      Tendsto
        (fun index =>
          generatedVelocityEndpointGalerkinSpaceTimePath
            ledger (subsequence index))
        atTop (𝓝 stateLimit)) :
    ∃ transverseLimit : TransverseSpaceTimeState 1,
      Tendsto
          (fun index =>
            generatedVelocityEndpointGalerkinTransverseSpaceTimePath
              ledger (subsequence index))
          atTop (𝓝 transverseLimit) ∧
        transverseSpaceTimeInclusion 1 transverseLimit = stateLimit := by
  apply transverseSpaceTime_limit_of_inclusion_tendsto
  simpa only [
    generatedVelocityEndpointGalerkinTransverseSpaceTimePath_inclusion]
    using stateTendsto

/-- Every actual finite velocity path obeys Fourier reality at every
physical time before the time-`L²` quotient. -/
theorem generatedVelocityEndpointGalerkinWholeState_fourierReality
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ)
    (time : Icc (0 : ℝ) 1) :
    FiniteStateFourierReality
      (generatedVelocityEndpointGalerkinWholeState ledger radius time) := by
  intro wave
  by_cases waveMem : wave ∈ wholeRestartModes radius
  · have negWaveMem : waveNeg wave ∈ wholeRestartModes radius :=
      puncturedIntegerWaveFrequencyCube_waveNeg_mem radius waveMem
    rw [generatedVelocityEndpointGalerkinWholeState_apply,
      generatedVelocityEndpointGalerkinWholeState_apply,
      if_pos waveMem, if_pos negWaveMem]
    exact finiteStateVelocityCoefficient_waveNeg
      ((ledger.family.stage radius).physical time.1 time.2 |>.2.2.2 wave)
  · have negWaveNotMem : waveNeg wave ∉ wholeRestartModes radius := by
      intro negWaveMem
      exact waveMem (by
        simpa [wholeRestartModes] using
          puncturedIntegerWaveFrequencyCube_waveNeg_mem radius negWaveMem)
    rw [generatedVelocityEndpointGalerkinWholeState_apply,
      generatedVelocityEndpointGalerkinWholeState_apply,
      if_neg waveMem, if_neg negWaveNotMem]
    exact vectorConj_zero.symm

/-- Fourier reality of one generated approximant in the rowwise time-`L²`
carrier. -/
theorem generatedVelocityEndpointGalerkinSpaceTimePath_fourierReality
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ)
    (wave : IntegerWavevector) :
    fixedWaveSpaceTimeRestriction 1 (waveNeg wave)
        (generatedVelocityEndpointGalerkinSpaceTimePath ledger radius) =
      fixedWaveSpaceTimeConjugation 1
        (fixedWaveSpaceTimeRestriction 1 wave
          (generatedVelocityEndpointGalerkinSpaceTimePath ledger radius)) := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    fixedWaveSpaceTimeRestriction_coeFn 1 (waveNeg wave)
      (generatedVelocityEndpointGalerkinSpaceTimePath ledger radius),
    fixedWaveSpaceTimeRestriction_coeFn 1 wave
      (generatedVelocityEndpointGalerkinSpaceTimePath ledger radius),
    fixedWaveSpaceTimeConjugation_coeFn 1
      (fixedWaveSpaceTimeRestriction 1 wave
        (generatedVelocityEndpointGalerkinSpaceTimePath ledger radius)),
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞)) (μ := commonTimeMeasure 1) ℂ
      (generatedVelocityEndpointGalerkinWholeBoundedPath ledger radius)] with
      time negRowEq rowEq conjugateEq wholeEq
  rw [negRowEq, conjugateEq, rowEq]
  change
    generatedVelocityEndpointGalerkinSpaceTimePath ledger radius time
        (waveNeg wave) =
      vectorConj
        (generatedVelocityEndpointGalerkinSpaceTimePath ledger radius time wave)
  change
    ((BoundedContinuousFunction.toLp 2 (commonTimeMeasure 1) ℂ)
      (generatedVelocityEndpointGalerkinWholeBoundedPath ledger radius)) time
        (waveNeg wave) =
      vectorConj
        (((BoundedContinuousFunction.toLp 2 (commonTimeMeasure 1) ℂ)
          (generatedVelocityEndpointGalerkinWholeBoundedPath ledger radius))
            time wave)
  rw [wholeEq]
  exact
    generatedVelocityEndpointGalerkinWholeState_fourierReality
      ledger radius time wave

/-- Fourier reality is closed under the same whole-carrier strong passage
used by the weak NSE and gradient receipt. -/
theorem generatedVelocityEndpoint_stateLimit_fourierReality
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (subsequence : ℕ → ℕ)
    (stateLimit : SpaceTimeState 1)
    (stateTendsto :
      Tendsto
        (fun index =>
          generatedVelocityEndpointGalerkinSpaceTimePath
            ledger (subsequence index))
        atTop (𝓝 stateLimit))
    (wave : IntegerWavevector) :
    fixedWaveSpaceTimeRestriction 1 (waveNeg wave) stateLimit =
      fixedWaveSpaceTimeConjugation 1
        (fixedWaveSpaceTimeRestriction 1 wave stateLimit) := by
  have negativeRowTendsto :
      Tendsto
        (fun index =>
          fixedWaveSpaceTimeRestriction 1 (waveNeg wave)
            (generatedVelocityEndpointGalerkinSpaceTimePath
              ledger (subsequence index)))
        atTop
        (𝓝 (fixedWaveSpaceTimeRestriction 1 (waveNeg wave) stateLimit)) :=
    (fixedWaveSpaceTimeRestriction 1 (waveNeg wave)).continuous.tendsto
      stateLimit |>.comp stateTendsto
  have positiveRowTendsto :
      Tendsto
        (fun index =>
          fixedWaveSpaceTimeRestriction 1 wave
            (generatedVelocityEndpointGalerkinSpaceTimePath
              ledger (subsequence index)))
        atTop
        (𝓝 (fixedWaveSpaceTimeRestriction 1 wave stateLimit)) :=
    (fixedWaveSpaceTimeRestriction 1 wave).continuous.tendsto
      stateLimit |>.comp stateTendsto
  have conjugateRowTendsto :
      Tendsto
        (fun index =>
          fixedWaveSpaceTimeConjugation 1
            (fixedWaveSpaceTimeRestriction 1 wave
              (generatedVelocityEndpointGalerkinSpaceTimePath
                ledger (subsequence index))))
        atTop
        (𝓝 (fixedWaveSpaceTimeConjugation 1
          (fixedWaveSpaceTimeRestriction 1 wave stateLimit))) :=
    (fixedWaveSpaceTimeConjugation 1).continuous.tendsto
      (fixedWaveSpaceTimeRestriction 1 wave stateLimit) |>.comp
        positiveRowTendsto
  exact tendsto_nhds_unique negativeRowTendsto <| by
    simpa only [generatedVelocityEndpointGalerkinSpaceTimePath_fourierReality]
      using conjugateRowTendsto

/-- Strong whole-carrier passage preserves the source-generated missing
zero Fourier row. -/
theorem generatedVelocityEndpoint_stateLimit_zero_ae
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (subsequence : ℕ → ℕ)
    (stateLimit : SpaceTimeState 1)
    (stateTendsto :
      Tendsto
        (fun index =>
          generatedVelocityEndpointGalerkinSpaceTimePath
            ledger (subsequence index))
        atTop (𝓝 stateLimit)) :
    ∀ᵐ time ∂(commonTimeMeasure 1), stateLimit time 0 = 0 := by
  have approximationZero (index : ℕ) :
      fixedWaveSpaceTimeRestriction 1 0
          (generatedVelocityEndpointGalerkinSpaceTimePath
            ledger (subsequence index)) =
        0 := by
    apply MeasureTheory.Lp.ext
    filter_upwards [
      fixedWaveSpaceTimeRestriction_coeFn 1 0
        (generatedVelocityEndpointGalerkinSpaceTimePath
          ledger (subsequence index)),
      BoundedContinuousFunction.coeFn_toLp
        (p := (2 : ℝ≥0∞)) (μ := commonTimeMeasure 1) ℂ
        (generatedVelocityEndpointGalerkinWholeBoundedPath
          ledger (subsequence index)),
      MeasureTheory.Lp.coeFn_zero
        ComplexCoordinateVector 2 (commonTimeMeasure 1)] with
        time rowEq wholeEq zeroEq
    rw [rowEq, zeroEq]
    change
      ((BoundedContinuousFunction.toLp 2 (commonTimeMeasure 1) ℂ)
          (generatedVelocityEndpointGalerkinWholeBoundedPath
            ledger (subsequence index))) time 0 = 0
    rw [wholeEq]
    change
      generatedVelocityEndpointGalerkinWholeState
          ledger (subsequence index) time 0 = 0
    rw [generatedVelocityEndpointGalerkinWholeState_apply]
    simp [wholeRestartModes,
      zero_not_mem_puncturedIntegerWaveFrequencyCube]
  have rowTendsto :
      Tendsto
        (fun index =>
          fixedWaveSpaceTimeRestriction 1 0
            (generatedVelocityEndpointGalerkinSpaceTimePath
              ledger (subsequence index)))
        atTop
        (𝓝 (fixedWaveSpaceTimeRestriction 1 0 stateLimit)) :=
    ((fixedWaveSpaceTimeRestriction 1 0).continuous.tendsto stateLimit).comp
      stateTendsto
  have rowLimitZero :
      fixedWaveSpaceTimeRestriction 1 0 stateLimit = 0 := by
    have approximationSequenceEq :
        (fun index =>
          fixedWaveSpaceTimeRestriction 1 0
            (generatedVelocityEndpointGalerkinSpaceTimePath
              ledger (subsequence index))) =
          (fun _ : ℕ => (0 : FixedWaveSpaceTimeState 1)) := by
      funext index
      exact approximationZero index
    rw [approximationSequenceEq] at rowTendsto
    exact tendsto_nhds_unique rowTendsto tendsto_const_nhds
  filter_upwards [
    fixedWaveSpaceTimeRestriction_coeFn 1 0 stateLimit,
    MeasureTheory.Lp.coeFn_zero
      ComplexCoordinateVector 2 (commonTimeMeasure 1)] with
      time rowEq zeroEq
  rw [← rowEq, rowLimitZero, zeroEq]
  simp

theorem stateLimit_transverse_ae_of_transverseLift
    (stateLimit : SpaceTimeState 1)
    (transverseLimit : TransverseSpaceTimeState 1)
    (inclusionEq :
      transverseSpaceTimeInclusion 1 transverseLimit = stateLimit) :
    ∀ᵐ time ∂(commonTimeMeasure 1),
      WholeStateTransverse (stateLimit time) := by
  have inclusionAE :
      ∀ᵐ time ∂(commonTimeMeasure 1),
        stateLimit time = (transverseLimit time).1 := by
    simpa only [inclusionEq] using
      transverseSpaceTimeInclusion_coeFn 1 transverseLimit
  filter_upwards [inclusionAE] with time pointEq
  rw [pointEq]
  exact (transverseLimit time).2

theorem stateLimit_fourierReality_ae_of_rowwise
    (stateLimit : SpaceTimeState 1)
    (rowwiseReality :
      ∀ wave : IntegerWavevector,
        fixedWaveSpaceTimeRestriction 1 (waveNeg wave) stateLimit =
          fixedWaveSpaceTimeConjugation 1
            (fixedWaveSpaceTimeRestriction 1 wave stateLimit)) :
    ∀ᵐ time ∂(commonTimeMeasure 1),
      FiniteStateFourierReality (stateLimit time) := by
  have realityAE :
      ∀ wave : IntegerWavevector,
        ∀ᵐ time ∂(commonTimeMeasure 1),
          stateLimit time (waveNeg wave) =
            vectorConj (stateLimit time wave) := by
    intro wave
    have negRowAE :=
      fixedWaveSpaceTimeRestriction_coeFn 1 (waveNeg wave) stateLimit
    have rowAE :=
      fixedWaveSpaceTimeRestriction_coeFn 1 wave stateLimit
    have conjugationAE :=
      fixedWaveSpaceTimeConjugation_coeFn 1
        (fixedWaveSpaceTimeRestriction 1 wave stateLimit)
    filter_upwards [negRowAE, rowAE, conjugationAE] with
        time negRowEq rowEq conjugationEq
    calc
      stateLimit time (waveNeg wave) =
          fixedWaveSpaceTimeRestriction 1 (waveNeg wave)
            stateLimit time := negRowEq.symm
      _ = fixedWaveSpaceTimeConjugation 1
            (fixedWaveSpaceTimeRestriction 1 wave stateLimit) time := by
        rw [rowwiseReality wave]
      _ = vectorConj
            (fixedWaveSpaceTimeRestriction 1 wave stateLimit time) :=
        conjugationEq
      _ = vectorConj (stateLimit time wave) := by rw [rowEq]
  exact eventually_countable_forall.2 realityAE

/-! ## Same-lineage Leray--Hopf core receipt -/

/-- The complete information already generated on one common strong
subsequence: unforced weak NSE, source initial-data convergence, closed
physical invariants, and the lower-semicontinuous viscous gradient budget.

The pointwise time trace and prefix energy inequality are deliberately not
fields of this carrier: they require a continuous-time representative of the
time-`L²` class and are supplied by the downstream endpoint compiler. -/
structure GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu) where
  stateLimit : SpaceTimeState 1
  stateLimit_mem :
    stateLimit ∈
      closure (generatedVelocityEndpointGalerkinSpaceTimePathFamily ledger)
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  state_tendsto :
    Tendsto
      (fun index =>
        generatedVelocityEndpointGalerkinSpaceTimePath
          ledger (subsequence index))
      atTop (𝓝 stateLimit)
  state_strong :
    Tendsto
      (fun index =>
        ‖generatedVelocityEndpointGalerkinSpaceTimePath
              ledger (subsequence index) -
            stateLimit‖)
      atTop (𝓝 0)
  initial_tendsto :
    Tendsto
      (fun index =>
        wholeRestartVelocityEndpointGalerkinInitialVelocity
          (subsequence index)
          ledger.family.endpointReceipt.velocityEndpoint)
      atTop (𝓝 ledger.family.endpointReceipt.velocityEndpoint)
  initial_energy_tendsto :
    Tendsto
      (fun index =>
        finiteStateVorticityKineticEnergy
          (wholeRestartModes (subsequence index))
          (wholeRestartVelocityEndpointFiniteVorticityInitialState
            (subsequence index)
            ledger.family.endpointReceipt.velocityEndpoint))
      atTop
      (𝓝 ((1 / 2 : ℝ) *
        ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2))
  spaceTime_norm_sq_le_endpoint :
    ‖stateLimit‖ ^ 2 ≤
      ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2
  fixedWave_tendsto :
    ∀ wave : IntegerWavevector,
      Tendsto
        (fun index =>
          fixedWaveSpaceTimeRestriction 1 wave
            (generatedVelocityEndpointGalerkinSpaceTimePath
              ledger (subsequence index)))
        atTop (𝓝 (fixedWaveSpaceTimeRestriction 1 wave stateLimit))
  fixedWave_strong :
    ∀ wave : IntegerWavevector,
      Tendsto
        (fun index =>
          ‖fixedWaveSpaceTimeRestriction 1 wave
                (generatedVelocityEndpointGalerkinSpaceTimePath
                  ledger (subsequence index)) -
              fixedWaveSpaceTimeRestriction 1 wave stateLimit‖)
        atTop (𝓝 0)
  transverseLimit : TransverseSpaceTimeState 1
  transverse_tendsto :
    Tendsto
      (fun index =>
        generatedVelocityEndpointGalerkinTransverseSpaceTimePath
          ledger (subsequence index))
      atTop (𝓝 transverseLimit)
  transverse_inclusion :
    transverseSpaceTimeInclusion 1 transverseLimit = stateLimit
  zero_ae :
    ∀ᵐ time ∂(commonTimeMeasure 1), stateLimit time 0 = 0
  transverse_ae :
    ∀ᵐ time ∂(commonTimeMeasure 1),
      WholeStateTransverse (stateLimit time)
  fourier_reality :
    ∀ wave : IntegerWavevector,
      fixedWaveSpaceTimeRestriction 1 (waveNeg wave) stateLimit =
        fixedWaveSpaceTimeConjugation 1
          (fixedWaveSpaceTimeRestriction 1 wave stateLimit)
  fourier_reality_ae :
    ∀ᵐ time ∂(commonTimeMeasure 1),
      FiniteStateFourierReality (stateLimit time)
  gradient_summable :
    Summable
      (fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity 1 stateLimit wave)
  gradient_mass_le :
    wholeSpaceTimeVorticityGradientMass 1 stateLimit ≤
      generatedVelocityEndpointGradientCeiling ledger
  viscous_gradient_mass_le :
    nu.coeff * (2 * Real.pi) ^ 2 *
        wholeSpaceTimeVorticityGradientMass 1 stateLimit ≤
      (1 / 2 : ℝ) *
        ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2
  nonlinearLimit :
    IntegerWavevector → NonlinearRowSpaceTimeState 1
  nonlinear_tendsto :
    ∀ output : IntegerWavevector,
      Tendsto
        (fun index =>
          generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
            ledger (subsequence index) output)
        atTop (𝓝 (nonlinearLimit output))
  weak_nse :
    ∀ output : IntegerWavevector, output ≠ 0 →
      WholeVelocityFixedWaveWeakNSE nu.coeff output stateLimit
        (wholeVelocityLerayProjectionSpaceTime output
          (nonlinearLimit output))

private theorem generatedWholeRestartVelocityEndpointLerayHopfCoreReceipt_nonempty
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu) :
    Nonempty
      (GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger) := by
  obtain
      ⟨stateLimit, stateLimitMem, subsequence, subsequenceMono,
        stateTendsto, stateStrong, initialTendsto,
        initialEnergyTendsto, fixedWaveTendsto, fixedWaveStrong⟩ :=
    generatedVelocityEndpointGalerkinSpaceTimePath_strong_subsequence_with_fixed_wave_rows
      ledger
  have stateCauchy :
      CauchySeq
        (fun index =>
          generatedVelocityEndpointGalerkinSpaceTimePath
            ledger (subsequence index)) :=
    stateTendsto.cauchy_map
  have nonlinearExists (output : IntegerWavevector) :
      ∃ limit : NonlinearRowSpaceTimeState 1,
        Tendsto
          (fun index =>
            generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
              ledger (subsequence index) output)
          atTop (𝓝 limit) :=
    cauchySeq_tendsto_of_complete
      (generatedVelocityEndpointGalerkinWholeNonlinearRow_cauchySeq_of_spaceTime_cauchySeq
        ledger subsequence output stateCauchy)
  let nonlinearLimit :
      IntegerWavevector → NonlinearRowSpaceTimeState 1 :=
    fun output => Classical.choose (nonlinearExists output)
  have nonlinearTendsto (output : IntegerWavevector) :
      Tendsto
        (fun index =>
          generatedVelocityEndpointGalerkinWholeNonlinearRowSpaceTimePath
            ledger (subsequence index) output)
        atTop (𝓝 (nonlinearLimit output)) :=
    Classical.choose_spec (nonlinearExists output)
  obtain ⟨transverseLimit, transverseTendsto, transverseInclusion⟩ :=
    generatedVelocityEndpoint_stateLimit_transverseLift
      ledger subsequence stateLimit stateTendsto
  obtain ⟨gradientSummable, gradientMassLe⟩ :=
    generatedVelocityEndpoint_stateLimit_gradientMass_le
      ledger subsequence stateLimit stateTendsto
  have viscousGradientMassLe :=
    generatedVelocityEndpoint_stateLimit_viscousGradientMass_le
      ledger subsequence stateLimit stateTendsto
  apply Nonempty.intro
  refine
    { stateLimit := stateLimit
      stateLimit_mem := stateLimitMem
      subsequence := subsequence
      subsequence_strictMono := subsequenceMono
      state_tendsto := stateTendsto
      state_strong := stateStrong
      initial_tendsto := initialTendsto
      initial_energy_tendsto := initialEnergyTendsto
      spaceTime_norm_sq_le_endpoint :=
        generatedVelocityEndpoint_stateLimit_spaceTime_norm_sq_le_endpoint
          ledger subsequence stateLimit stateTendsto
      fixedWave_tendsto := fixedWaveTendsto
      fixedWave_strong := fixedWaveStrong
      transverseLimit := transverseLimit
      transverse_tendsto := transverseTendsto
      transverse_inclusion := transverseInclusion
      zero_ae :=
        generatedVelocityEndpoint_stateLimit_zero_ae
          ledger subsequence stateLimit stateTendsto
      transverse_ae :=
        stateLimit_transverse_ae_of_transverseLift
          stateLimit transverseLimit transverseInclusion
      fourier_reality := fun wave =>
        generatedVelocityEndpoint_stateLimit_fourierReality
          ledger subsequence stateLimit stateTendsto wave
      fourier_reality_ae :=
        stateLimit_fourierReality_ae_of_rowwise stateLimit
          (fun wave =>
            generatedVelocityEndpoint_stateLimit_fourierReality
              ledger subsequence stateLimit stateTendsto wave)
      gradient_summable := gradientSummable
      gradient_mass_le := gradientMassLe
      viscous_gradient_mass_le := viscousGradientMassLe
      nonlinearLimit := nonlinearLimit
      nonlinear_tendsto := nonlinearTendsto
      weak_nse := ?_ }
  intro output outputNe
  exact generatedVelocityEndpoint_fixedWaveWeakNSE_of_tendsto
    ledger subsequence subsequenceMono stateLimit stateTendsto
    output outputNe (nonlinearLimit output) (nonlinearTendsto output)

/-- Generate the enriched weak/Leray--Hopf core on exactly the strong
subsequence selected from the source-owned Galerkin family. -/
noncomputable def generatedWholeRestartVelocityEndpointLerayHopfCoreReceipt
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu) :
    GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger :=
  Classical.choice
    (generatedWholeRestartVelocityEndpointLerayHopfCoreReceipt_nonempty
      ledger)

/-- Source-facing producer.  The kinetic ledger, compactness limit,
subsequence, invariant lifts, gradient budget, nonlinear limit, and weak NSE
are all generated internally from the bounded whole-restart source. -/
noncomputable def sourceGeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded).toCore :=
  generatedWholeRestartVelocityEndpointLerayHopfCoreReceipt
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      initial elapsedBounded).toCore

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointLerayHopfReceipt
end NavierStokes
end SaturationMonoid
