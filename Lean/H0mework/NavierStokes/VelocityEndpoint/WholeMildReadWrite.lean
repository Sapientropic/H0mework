import H0mework.NavierStokes.VelocityGalerkin.ContinuousMildRepresentative
import H0mework.NavierStokes.Galerkin.AmbientNorm
import H0mework.NavierStokes.Restart.NativeAccumulationRoot

/-!
# Whole pointwise mild read/write generated at the velocity endpoint

The endpoint Leray--Hopf core lives in the time-`L²` quotient.  Its
source-generated continuous mild rows determine a canonical value at every
physical time before that quotient.  This module assembles those rows in the
original whole `ℓ²` velocity carrier.  Summability and the uniform kinetic
bound are transported from the identical Galerkin events; they are not
stored as target-path premises.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite

open scoped BigOperators ENNReal Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
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
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinNonlinearSpaceTimePassage
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinVelocityWeakLimit
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointLerayHopfReceipt
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinContinuousMildRepresentative
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot

noncomputable section

/-! ## Actual finite whole-state ceiling -/

/-- Every actual endpoint Galerkin velocity state is paid by the source
endpoint kinetic square, pointwise in physical time and independently of
the canonical radius. -/
theorem generatedVelocityEndpointGalerkinWholeState_norm_sq_le_endpoint
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu)
    (radius : ℕ)
    (time : Icc (0 : ℝ) 1) :
    ‖generatedVelocityEndpointGalerkinWholeState ledger radius time‖ ^ 2 ≤
      ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 := by
  let state := (ledger.family.stage radius).trajectory time.1
  let velocityState :=
    generatedVelocityEndpointGalerkinWholeState ledger radius time
  have supported :
      ∀ wave, wave ∉ wholeRestartModes radius → velocityState wave = 0 := by
    intro wave waveNotMem
    simp [velocityState,
      generatedVelocityEndpointGalerkinWholeState_apply, waveNotMem]
  have ambientLe :
      ‖velocityState‖ ^ 2 ≤
        finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius) velocityState :=
    complexVorticityHilbertState_norm_sq_le_coefficientEnstrophy
      (wholeRestartModes radius) velocityState supported
  have coefficientEq :
      finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius) velocityState =
        2 * finiteStateVorticityKineticEnergy
          (wholeRestartModes radius) state := by
    rw [← velocityRowAmplitude_sq_sum_eq_two_kineticEnergy
      (wholeRestartModes radius) state]
    unfold finiteStateVorticityCoefficientEnstrophy
    apply Finset.sum_congr rfl
    intro wave waveMem
    rw [velocityRowAmplitude_sq]
    simp [velocityState, state,
      generatedVelocityEndpointGalerkinWholeState_apply, waveMem]
  rw [coefficientEq] at ambientLe
  exact ambientLe.trans (by
    nlinarith [ledger.kinetic_energy_le radius time])

/-! ## Canonical coefficient table -/

/-- The canonical pre-quotient velocity coefficient.  A nonzero row is the
continuous mild path generated from the common Leray--Hopf core; the mean
row is the source-owned zero row. -/
def velocityEndpointWholeMildCoefficient
    {nu : Viscosity}
    {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
    (receipt :
      GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger)
    (time : Icc (0 : ℝ) 1)
    (output : IntegerWavevector) : ComplexCoordinateVector :=
  if outputNe : output ≠ 0 then
    (GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt.fixedWaveContinuousMildReceipt
      receipt output outputNe).rowPath time
  else 0

@[simp] theorem velocityEndpointWholeMildCoefficient_zero
    {nu : Viscosity}
    {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
    (receipt :
      GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger)
    (time : Icc (0 : ℝ) 1) :
    velocityEndpointWholeMildCoefficient receipt time 0 = 0 := by
  simp [velocityEndpointWholeMildCoefficient]

theorem velocityEndpointWholeMildCoefficient_of_ne
    {nu : Viscosity}
    {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
    (receipt :
      GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger)
    (time : Icc (0 : ℝ) 1)
    (output : IntegerWavevector)
    (outputNe : output ≠ 0) :
    velocityEndpointWholeMildCoefficient receipt time output =
      (GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt.fixedWaveContinuousMildReceipt
        receipt output outputNe).rowPath time := by
  simp only [velocityEndpointWholeMildCoefficient, dif_pos outputNe]

/-- Along the common source-selected radius subsequence, every actual whole
velocity coefficient converges pointwise to the canonical continuous mild
coefficient. -/
theorem generatedVelocityEndpointGalerkinWholeState_tendsto_mildCoefficient
    {nu : Viscosity}
    {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
    (receipt :
      GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger)
    (time : Icc (0 : ℝ) 1)
    (output : IntegerWavevector) :
    Tendsto
      (fun index =>
        generatedVelocityEndpointGalerkinWholeState ledger
          (receipt.subsequence index) time output)
      atTop
      (𝓝 (velocityEndpointWholeMildCoefficient receipt time output)) := by
  by_cases outputNe : output ≠ 0
  · let endpointRow :=
      wholeRestartVelocityEndpointCoefficient
        ledger.family.endpointReceipt.velocityEndpoint output
    have outputEventuallyMem :
        ∀ᶠ index : ℕ in atTop,
          output ∈ wholeRestartModes (receipt.subsequence index) :=
      receipt.subsequence_strictMono.tendsto_atTop
        (nonzero_integerWave_eventually_mem_puncturedFrequencyCube
          output outputNe)
    let zeroTime : Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
    have initialEventually :
        (fun index =>
          generatedVelocityEndpointGalerkinWholeState ledger
            (receipt.subsequence index) zeroTime output) =ᶠ[atTop]
          (fun _ : ℕ => endpointRow) := by
      filter_upwards [outputEventuallyMem] with index outputMem
      rw [generatedVelocityEndpointGalerkinWholeState_zero,
        wholeRestartVelocityEndpointFiniteProjection_apply,
        if_pos outputMem]
    have initialTendsto :
        Tendsto
          (fun index =>
            generatedVelocityEndpointGalerkinWholeState ledger
              (receipt.subsequence index) zeroTime output)
          atTop (𝓝 endpointRow) :=
      tendsto_const_nhds.congr' initialEventually.symm
    have projectedNonlinearTendsto :
        Tendsto
          (fun index =>
            generatedVelocityEndpointGalerkinProjectedNonlinearRowSpaceTimePath
              ledger (receipt.subsequence index) output)
          atTop
          (𝓝 (wholeVelocityLerayProjectionSpaceTime output
            (receipt.nonlinearLimit output))) :=
      ((wholeVelocityLerayProjectionSpaceTime output).continuous.tendsto
        (receipt.nonlinearLimit output)).comp
          (receipt.nonlinear_tendsto output)
    have duhamelTendsto :
        Tendsto
          (fun index =>
            fixedWaveHeatDuhamelValue 1 nu.coeff output
              (generatedVelocityEndpointGalerkinWholeState ledger
                (receipt.subsequence index) zeroTime output)
              (generatedVelocityEndpointGalerkinProjectedNonlinearRowSpaceTimePath
                ledger (receipt.subsequence index) output)
              time)
          atTop
          (𝓝 (fixedWaveHeatDuhamelValue 1 nu.coeff output endpointRow
            (wholeVelocityLerayProjectionSpaceTime output
              (receipt.nonlinearLimit output)) time)) :=
      tendsto_fixedWaveHeatDuhamelValue 1 nu.coeff nu.coeff_pos.le
        output time
        (fun index =>
          generatedVelocityEndpointGalerkinWholeState ledger
            (receipt.subsequence index) zeroTime output)
        (fun index =>
          generatedVelocityEndpointGalerkinProjectedNonlinearRowSpaceTimePath
            ledger (receipt.subsequence index) output)
        endpointRow
        (wholeVelocityLerayProjectionSpaceTime output
          (receipt.nonlinearLimit output))
        initialTendsto projectedNonlinearTendsto
    have finiteMildEventually :
        (fun index =>
          generatedVelocityEndpointGalerkinWholeState ledger
            (receipt.subsequence index) time output) =ᶠ[atTop]
        (fun index =>
          fixedWaveHeatDuhamelValue 1 nu.coeff output
            (generatedVelocityEndpointGalerkinWholeState ledger
              (receipt.subsequence index) zeroTime output)
            (generatedVelocityEndpointGalerkinProjectedNonlinearRowSpaceTimePath
              ledger (receipt.subsequence index) output)
            time) := by
      filter_upwards [outputEventuallyMem] with index outputMem
      exact generatedVelocityEndpointGalerkinWholeVelocityWave_mildIdentity
        ledger (receipt.subsequence index) output outputMem time
    have actualTendsto :=
      duhamelTendsto.congr' finiteMildEventually.symm
    rw [velocityEndpointWholeMildCoefficient_of_ne
      receipt time output outputNe]
    rw [(GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt.fixedWaveContinuousMildReceipt
      receipt output outputNe).row_mild_identity]
    simpa [endpointRow] using actualTendsto
  · have outputZero : output = 0 := not_ne_iff.mp outputNe
    subst output
    have sequenceZero :
        (fun index =>
          generatedVelocityEndpointGalerkinWholeState ledger
            (receipt.subsequence index) time 0) =
          (fun _ : ℕ => (0 : ComplexCoordinateVector)) := by
      funext index
      have zeroNotMem :
          (0 : IntegerWavevector) ∉
            wholeRestartModes (receipt.subsequence index) := by
        exact zero_not_mem_puncturedIntegerWaveFrequencyCube
          (receipt.subsequence index)
      rw [generatedVelocityEndpointGalerkinWholeState_apply,
        if_neg zeroNotMem]
    rw [sequenceZero]
    exact tendsto_const_nhds

/-! ## Whole-carrier assembly -/

/-- Every finite inventory of canonical mild rows is paid by the same
endpoint kinetic square.  The proof takes the limit of the identical
finite inventory on the actual Galerkin lineage, so no rowwise compactness
choice can create extra whole-state mass. -/
theorem velocityEndpointWholeMildCoefficient_finsetSum_le_endpoint
    {nu : Viscosity}
    {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
    (receipt :
      GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger)
    (time : Icc (0 : ℝ) 1)
    (waves : Finset IntegerWavevector) :
    (∑ wave ∈ waves,
        ‖velocityEndpointWholeMildCoefficient receipt time wave‖ ^ 2) ≤
      ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 := by
  have finiteSumTendsto :
      Tendsto
        (fun index =>
          ∑ wave ∈ waves,
            ‖generatedVelocityEndpointGalerkinWholeState ledger
                (receipt.subsequence index) time wave‖ ^ 2)
        atTop
        (𝓝 (∑ wave ∈ waves,
          ‖velocityEndpointWholeMildCoefficient receipt time wave‖ ^ 2)) := by
    apply tendsto_finsetSum
    intro wave waveMem
    exact
      (generatedVelocityEndpointGalerkinWholeState_tendsto_mildCoefficient
        receipt time wave).norm.pow 2
  apply le_of_tendsto finiteSumTendsto
  exact Filter.Eventually.of_forall fun index => by
    let state :=
      generatedVelocityEndpointGalerkinWholeState ledger
        (receipt.subsequence index) time
    have stateSummable :
        Summable fun wave : IntegerWavevector => ‖state wave‖ ^ 2 := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        Memℓp.summable (by norm_num) state.2
    have finiteLeNorm :
        (∑ wave ∈ waves, ‖state wave‖ ^ 2) ≤ ‖state‖ ^ 2 := by
      rw [show ‖state‖ ^ 2 =
          ∑' wave : IntegerWavevector, ‖state wave‖ ^ 2 by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          lp.norm_rpow_eq_tsum
            (p := (2 : ℝ≥0∞)) (by norm_num) state]
      exact stateSummable.sum_le_tsum waves fun wave waveMem => sq_nonneg _
    exact finiteLeNorm.trans
      (generatedVelocityEndpointGalerkinWholeState_norm_sq_le_endpoint
        ledger (receipt.subsequence index) time)

theorem velocityEndpointWholeMildCoefficient_summable
    {nu : Viscosity}
    {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
    (receipt :
      GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger)
    (time : Icc (0 : ℝ) 1) :
    Summable fun wave : IntegerWavevector =>
      ‖velocityEndpointWholeMildCoefficient receipt time wave‖ ^ 2 := by
  apply summable_of_sum_le
    (fun wave => sq_nonneg
      ‖velocityEndpointWholeMildCoefficient receipt time wave‖)
  intro waves
  exact velocityEndpointWholeMildCoefficient_finsetSum_le_endpoint
    receipt time waves

/-- The canonical pointwise endpoint write in the complete physical
velocity `ℓ²` carrier. -/
def velocityEndpointWholeMildState
    {nu : Viscosity}
    {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
    (receipt :
      GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger)
    (time : Icc (0 : ℝ) 1) : ComplexVorticityHilbertState :=
  ⟨velocityEndpointWholeMildCoefficient receipt time, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      velocityEndpointWholeMildCoefficient_summable receipt time⟩

@[simp] theorem velocityEndpointWholeMildState_apply
    {nu : Viscosity}
    {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
    (receipt :
      GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger)
    (time : Icc (0 : ℝ) 1)
    (output : IntegerWavevector) :
    velocityEndpointWholeMildState receipt time output =
      velocityEndpointWholeMildCoefficient receipt time output := rfl

theorem velocityEndpointWholeMildState_norm_sq_le_endpoint
    {nu : Viscosity}
    {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
    (receipt :
      GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger)
    (time : Icc (0 : ℝ) 1) :
    ‖velocityEndpointWholeMildState receipt time‖ ^ 2 ≤
      ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 := by
  rw [show ‖velocityEndpointWholeMildState receipt time‖ ^ 2 =
      ∑' wave : IntegerWavevector,
        ‖velocityEndpointWholeMildCoefficient receipt time wave‖ ^ 2 by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      velocityEndpointWholeMildState_apply] using
      lp.norm_rpow_eq_tsum
        (p := (2 : ℝ≥0∞)) (by norm_num)
        (velocityEndpointWholeMildState receipt time)]
  apply le_of_tendsto
    (velocityEndpointWholeMildCoefficient_summable receipt time).hasSum
  exact Filter.Eventually.of_forall fun waves =>
    velocityEndpointWholeMildCoefficient_finsetSum_le_endpoint
      receipt time waves

/-- The pointwise whole write is the identical time-`L²` state generated by
the Leray--Hopf core, almost everywhere. -/
theorem velocityEndpointWholeMildState_eq_stateLimit_ae
    {nu : Viscosity}
    {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
    (receipt :
      GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger) :
    ∀ᵐ time ∂(commonTimeMeasure 1),
      velocityEndpointWholeMildState receipt time = receipt.stateLimit time := by
  have coefficientAE :
      ∀ output : IntegerWavevector,
        ∀ᵐ time ∂(commonTimeMeasure 1),
          velocityEndpointWholeMildCoefficient receipt time output =
            receipt.stateLimit time output := by
    intro output
    by_cases outputNe : output ≠ 0
    · let rowReceipt :=
        GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt.fixedWaveContinuousMildReceipt
          receipt output outputNe
      have restrictionAE :=
        fixedWaveSpaceTimeRestriction_coeFn 1 output receipt.stateLimit
      filter_upwards [rowReceipt.row_represents, restrictionAE] with
        time rowEq restrictionEq
      rw [velocityEndpointWholeMildCoefficient_of_ne
        receipt time output outputNe, rowEq, restrictionEq]
    · have outputZero : output = 0 := not_ne_iff.mp outputNe
      subst output
      filter_upwards [receipt.zero_ae] with time zeroEq
      simpa using zeroEq.symm
  filter_upwards [eventually_countable_forall.2 coefficientAE] with
    time allRows
  apply lp.ext
  funext output
  exact allRows output

theorem velocityEndpointWholeMildState_initial_row
    {nu : Viscosity}
    {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
    (receipt :
      GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger)
    (output : IntegerWavevector) :
    velocityEndpointWholeMildState receipt ⟨0, by norm_num⟩ output =
      wholeRestartVelocityEndpointCoefficient
        ledger.family.endpointReceipt.velocityEndpoint output := by
  by_cases outputNe : output ≠ 0
  · rw [velocityEndpointWholeMildState_apply,
      velocityEndpointWholeMildCoefficient_of_ne
        receipt ⟨0, by norm_num⟩ output outputNe]
    exact
      (GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt.fixedWaveContinuousMildReceipt
        receipt output outputNe).row_initial
  · have outputZero : output = 0 := not_ne_iff.mp outputNe
    subst output
    simp [velocityEndpointWholeMildState_apply]

theorem velocityEndpointWholeMildState_row_mild_identity
    {nu : Viscosity}
    {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
    (receipt :
      GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger)
    (output : IntegerWavevector)
    (outputNe : output ≠ 0)
    (time : Icc (0 : ℝ) 1) :
    velocityEndpointWholeMildState receipt time output =
      fixedWaveHeatDuhamelValue 1 nu.coeff output
        (wholeRestartVelocityEndpointCoefficient
          ledger.family.endpointReceipt.velocityEndpoint output)
        (wholeVelocityLerayProjectionSpaceTime output
          (receipt.nonlinearLimit output)) time := by
  rw [velocityEndpointWholeMildState_apply,
    velocityEndpointWholeMildCoefficient_of_ne
      receipt time output outputNe]
  exact
    (GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt.fixedWaveContinuousMildReceipt
      receipt output outputNe).row_mild_identity time

/-! ## Source-owned whole read/write receipt -/

/-- The accumulation endpoint read writes a genuine pointwise whole
velocity state.  Its rows are continuous, its time-zero value is the
source-generated endpoint, and its causal mild law consumes the nonlinear
limit carried by the identical Leray--Hopf lineage. -/
structure GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu) where
  core : GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger
  wholePath : Icc (0 : ℝ) 1 → ComplexVorticityHilbertState
  wholePath_apply :
    ∀ time : Icc (0 : ℝ) 1,
      wholePath time = velocityEndpointWholeMildState core time
  stateLimit_ae :
    ∀ᵐ time ∂(commonTimeMeasure 1),
      wholePath time = core.stateLimit time
  norm_sq_le_endpoint :
    ∀ time : Icc (0 : ℝ) 1,
      ‖wholePath time‖ ^ 2 ≤
        ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2
  initial_row :
    ∀ output : IntegerWavevector,
      wholePath ⟨0, by norm_num⟩ output =
        wholeRestartVelocityEndpointCoefficient
          ledger.family.endpointReceipt.velocityEndpoint output
  coordinate_continuous :
    ∀ output : IntegerWavevector,
      Continuous fun time : Icc (0 : ℝ) 1 => wholePath time output
  row_mild_identity :
    ∀ (output : IntegerWavevector), output ≠ 0 →
      ∀ time : Icc (0 : ℝ) 1,
        wholePath time output =
          fixedWaveHeatDuhamelValue 1 nu.coeff output
            (wholeRestartVelocityEndpointCoefficient
              ledger.family.endpointReceipt.velocityEndpoint output)
            (wholeVelocityLerayProjectionSpaceTime output
              (core.nonlinearLimit output)) time

/-- Generate the pointwise whole mild read/write from the exact
Leray--Hopf core already selected by the source lineage. -/
noncomputable def generatedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
    {nu : Viscosity}
    (ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu) :
    GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger := by
  let core := generatedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger
  let wholePath : Icc (0 : ℝ) 1 → ComplexVorticityHilbertState :=
    velocityEndpointWholeMildState core
  refine
    { core := core
      wholePath := wholePath
      wholePath_apply := fun time => rfl
      stateLimit_ae := ?_
      norm_sq_le_endpoint := ?_
      initial_row := ?_
      coordinate_continuous := ?_
      row_mild_identity := ?_ }
  · simpa only [wholePath] using
      velocityEndpointWholeMildState_eq_stateLimit_ae core
  · intro time
    simpa only [wholePath] using
      velocityEndpointWholeMildState_norm_sq_le_endpoint core time
  · intro output
    simpa only [wholePath] using
      velocityEndpointWholeMildState_initial_row core output
  · intro output
    by_cases outputNe : output ≠ 0
    · simpa only [wholePath, velocityEndpointWholeMildState_apply,
        velocityEndpointWholeMildCoefficient, dif_pos outputNe] using
        (GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt.fixedWaveContinuousMildReceipt
          core output outputNe).rowPath.continuous
    · have outputZero : output = 0 := not_ne_iff.mp outputNe
      subst output
      simpa [wholePath, velocityEndpointWholeMildState_apply,
        velocityEndpointWholeMildCoefficient] using
        (continuous_const : Continuous
          (fun _ : Icc (0 : ℝ) 1 => (0 : ComplexCoordinateVector)))
  · intro output outputNe time
    simpa only [wholePath] using
      velocityEndpointWholeMildState_row_mild_identity
        core output outputNe time

/-- Source-facing endpoint producer.  The only external data are the actual
whole-restart source and its already generated bounded elapsed-time law;
the compactness limit, nonlinear limit, pointwise whole path and causal
write are selected internally. -/
noncomputable def sourceGeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
      (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded).toCore :=
  generatedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      initial elapsedBounded).toCore

/-- The original cofinal root generates a pointwise whole mild write from
its endpoint-indexed Galerkin ledger. -/
noncomputable def sourceGeneratedNativeTemporalWholeMildReadWriteReceipt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
      (sourceGeneratedNativeTemporalUniformKineticViscousLedgerCore
        initial) :=
  generatedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
    (sourceGeneratedNativeTemporalUniformKineticViscousLedgerCore initial)

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
end NavierStokes
end SaturationMonoid
