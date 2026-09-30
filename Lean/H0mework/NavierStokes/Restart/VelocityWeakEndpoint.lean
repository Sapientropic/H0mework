import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import H0mework.NavierStokes.Crossing.TangentCoercivity
import H0mework.NavierStokes.KineticRestart.KineticWeakEndpoint

/-!
# Source-generated physical velocity weak endpoint of the whole restart run

Every actual contact already carries a transverse whole vorticity state.  Its
Biot--Savart velocity therefore belongs to the complete nonzero-frequency
Euclidean `ℓ²` carrier, with norm square exactly equal to the existing kinetic
mass.  The native kinetic ledger then generates a uniformly bounded physical
velocity sequence, hence a weak endpoint along a strictly monotone source
subsequence.

This is an endpoint producer for the physical `L²` velocity coefficients.  It
does not construct a whole Navier--Stokes continuation from that endpoint.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint

open scoped BigOperators ENNReal

open Filter Metric Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint

noncomputable section

/-! ## Complete physical velocity carrier -/

/-- The complete nonzero-frequency physical velocity coefficient carrier. -/
abbrev WholeRestartVelocityEndpointState :=
  lp (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2

/-- Negation preserves the nonzero integer-wave carrier. -/
def nonzeroIntegerWavevectorNeg
    (wave : NonzeroIntegerWavevector) : NonzeroIntegerWavevector :=
  ⟨waveNeg wave.1, fun equality =>
    wave.2 ((waveNeg_eq_zero_iff wave.1).mp equality)⟩

@[simp] theorem nonzeroIntegerWavevectorNeg_value
    (wave : NonzeroIntegerWavevector) :
    (nonzeroIntegerWavevectorNeg wave).1 = waveNeg wave.1 := rfl

/-- Divergence-free law on the complete nonzero-frequency velocity
endpoint carrier. -/
def WholeRestartVelocityEndpointTransverse
    (state : WholeRestartVelocityEndpointState) : Prop :=
  ∀ wave : NonzeroIntegerWavevector,
    complexWavevector wave.1 ⬝ᵥ
      (fun coordinate => state wave coordinate) = 0

/-- Fourier reality on the complete nonzero-frequency velocity endpoint
carrier. -/
def WholeRestartVelocityEndpointReality
    (state : WholeRestartVelocityEndpointState) : Prop :=
  ∀ (wave : NonzeroIntegerWavevector) (coordinate : Coordinate),
    state (nonzeroIntegerWavevectorNeg wave) coordinate =
      star (state wave coordinate)

/-- One Biot--Savart velocity row, with the exact Euclidean coordinate norm. -/
def puncturedWholeVelocityEuclideanCoefficient
    (state : ComplexVorticityHilbertState)
    (wave : NonzeroIntegerWavevector) : ComplexCoordinateEuclidean :=
  euclideanCoordinateRow
    (biotSavartVelocityCoefficient wave.1 (state wave.1))

@[simp] theorem puncturedWholeVelocityEuclideanCoefficient_apply
    (state : ComplexVorticityHilbertState)
    (wave : NonzeroIntegerWavevector)
    (coordinate : Coordinate) :
    puncturedWholeVelocityEuclideanCoefficient state wave coordinate =
      biotSavartVelocityCoefficient wave.1 (state wave.1) coordinate := rfl

/-- Source transversality turns the physical Biot--Savart row norm into the
exact kinetic-mass summand. -/
theorem puncturedWholeVelocityEuclideanCoefficient_norm_sq
    (state : ComplexVorticityHilbertState)
    (transverse : WholeStateTransverse state)
    (wave : NonzeroIntegerWavevector) :
    ‖puncturedWholeVelocityEuclideanCoefficient state wave‖ ^ 2 =
      complexCoordinateAmplitudeSq (state wave.1) /
        integerWaveViscousMultiplier wave.1 := by
  change
    ‖euclideanCoordinateRow
        (biotSavartVelocityCoefficient wave.1 (state wave.1))‖ ^ 2 =
      complexCoordinateAmplitudeSq (state wave.1) /
        integerWaveViscousMultiplier wave.1
  rw [euclideanCoordinateRow_norm_sq,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
    biotSavartVelocityCoefficient_normSq_of_transverse
      wave.1 (state wave.1) wave.2 (transverse wave.1)]
  rfl

/-- The full nonzero-wave Biot--Savart velocity generated by a transverse
whole vorticity state. -/
def puncturedWholeVelocityEuclideanState
    (state : ComplexVorticityHilbertState) :
    WholeRestartVelocityEndpointState :=
  ⟨puncturedWholeVelocityEuclideanCoefficient state, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      Summable.of_nonneg_of_le
        (fun wave => sq_nonneg
          ‖puncturedWholeVelocityEuclideanCoefficient state wave‖)
        (fun wave => by
          change
            ‖euclideanCoordinateRow
                (biotSavartVelocityCoefficient wave.1 (state wave.1))‖ ^ 2 ≤
              complexCoordinateAmplitudeSq (state wave.1) /
                integerWaveViscousMultiplier wave.1
          rw [euclideanCoordinateRow_norm_sq]
          simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
          simpa only [integerWaveViscousMultiplier] using
            biotSavartVelocityCoefficient_normSq_le
              wave.1 (state wave.1) wave.2)
        (summable_puncturedWholeVorticityKineticMass state)⟩

@[simp] theorem puncturedWholeVelocityEuclideanState_apply
    (state : ComplexVorticityHilbertState)
    (wave : NonzeroIntegerWavevector) :
    puncturedWholeVelocityEuclideanState state wave =
      puncturedWholeVelocityEuclideanCoefficient state wave := rfl

/-- Physical velocity `L²` mass is exactly the existing kinetic-scale
vorticity mass, before any weak limit is selected. -/
theorem puncturedWholeVelocityEuclideanState_norm_sq
    (state : ComplexVorticityHilbertState)
    (transverse : WholeStateTransverse state) :
    ‖puncturedWholeVelocityEuclideanState state‖ ^ 2 =
      puncturedWholeVorticityKineticMass state := by
  calc
    ‖puncturedWholeVelocityEuclideanState state‖ ^ 2 =
        ∑' wave,
          ‖puncturedWholeVelocityEuclideanState state wave‖ ^ 2 := by
      convert
        (lp.norm_rpow_eq_tsum
          (p := (2 : ℝ≥0∞)) (by norm_num)
          (puncturedWholeVelocityEuclideanState state)) using 1 <;>
        simp only [ENNReal.toReal_ofNat, Real.rpow_two,
          puncturedWholeVelocityEuclideanState_apply]
    _ = puncturedWholeVorticityKineticMass state := by
      unfold puncturedWholeVorticityKineticMass
      apply tsum_congr
      intro wave
      exact
        puncturedWholeVelocityEuclideanCoefficient_norm_sq
          state transverse wave

/-- On zero-origin transverse whole states, the complete nonzero-frequency
Biot--Savart velocity carrier is faithful.  Curl recovers every retained
vorticity row; the separately generated zero-origin laws recover the omitted
origin row. -/
theorem puncturedWholeVelocityEuclideanState_eq_imp_eq_of_zero_transverse
    (left right : ComplexVorticityHilbertState)
    (leftZero : left 0 = 0)
    (rightZero : right 0 = 0)
    (leftTransverse : WholeStateTransverse left)
    (rightTransverse : WholeStateTransverse right)
    (velocityEq :
      puncturedWholeVelocityEuclideanState left =
        puncturedWholeVelocityEuclideanState right) :
    left = right := by
  apply lp.ext
  funext wave
  by_cases waveZero : wave = 0
  · subst wave
    rw [leftZero, rightZero]
  · have velocityRowEq :
        biotSavartVelocityCoefficient wave (left wave) =
          biotSavartVelocityCoefficient wave (right wave) := by
      funext coordinate
      have atWave :=
        congrArg
          (fun state : WholeRestartVelocityEndpointState =>
            state ⟨wave, waveZero⟩ coordinate)
          velocityEq
      exact atWave
    calc
      left wave =
          fourierCurlCoefficient wave
            (biotSavartVelocityCoefficient wave (left wave)) :=
        (fourierCurlCoefficient_biotSavartVelocityCoefficient_of_transverse
          wave (left wave) waveZero (leftTransverse wave)).symm
      _ =
          fourierCurlCoefficient wave
            (biotSavartVelocityCoefficient wave (right wave)) := by
        rw [velocityRowEq]
      _ = right wave :=
        fourierCurlCoefficient_biotSavartVelocityCoefficient_of_transverse
          wave (right wave) waveZero (rightTransverse wave)

/-! ## Actual native contact sequence -/

/-- The physical velocity written at one actual native whole-restart
contact.  Its transverse proof is generated by that same contact. -/
def wholeRestartContactVelocityState
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : ℕ) : WholeRestartVelocityEndpointState :=
  puncturedWholeVelocityEuclideanState
    (run initial index).contact.physicalState

/-- Every actual velocity contact has norm square equal to its exact native
kinetic ledger entry. -/
theorem wholeRestartContactVelocityState_norm_sq
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : ℕ) :
    ‖wholeRestartContactVelocityState initial index‖ ^ 2 =
      puncturedWholeVorticityKineticMass
        (run initial index).contact.physicalState :=
  puncturedWholeVelocityEuclideanState_norm_sq _
    (run initial index).contact.transverse

/-- Every actual contact velocity is divergence free on every retained
nonzero Fourier row. -/
theorem wholeRestartContactVelocityState_transverse
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : ℕ) :
    WholeRestartVelocityEndpointTransverse
      (wholeRestartContactVelocityState initial index) := by
  intro wave
  change
    complexWavevector wave.1 ⬝ᵥ
      biotSavartVelocityCoefficient wave.1
        ((run initial index).contact.physicalState wave.1) = 0
  exact complexWavevector_dot_biotSavartVelocityCoefficient _ _

/-- The same actual contact's vorticity reality law is transported through
Biot--Savart to physical velocity reality. -/
theorem wholeRestartContactVelocityState_reality
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : ℕ) :
    WholeRestartVelocityEndpointReality
      (wholeRestartContactVelocityState initial index) := by
  intro wave coordinate
  let state : ComplexVorticityHilbertState :=
    (run initial index).contact.physicalState
  have stateReality : FiniteStateFourierReality state := by
    intro actualWave
    exact (run initial index).contact.reality actualWave
  change
    biotSavartVelocityCoefficient (waveNeg wave.1)
        (state (waveNeg wave.1))
        coordinate =
      star
        (biotSavartVelocityCoefficient wave.1
          (state wave.1)
          coordinate)
  rw [stateReality wave.1,
    biotSavartVelocityCoefficient_waveNeg_vectorConj]
  rfl

/-- The native kinetic monotonicity gives the physical velocity sequence a
source-owned uniform norm bound. -/
theorem wholeRestartContactVelocityState_norm_le_initial
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : ℕ) :
    ‖wholeRestartContactVelocityState initial index‖ ≤
      ‖wholeRestartContactVelocityState initial 0‖ := by
  have massLe :=
    run_contact_kineticMass_antitone initial (Nat.zero_le index)
  have squareLe :
      ‖wholeRestartContactVelocityState initial index‖ ^ 2 ≤
        ‖wholeRestartContactVelocityState initial 0‖ ^ 2 := by
    calc
      ‖wholeRestartContactVelocityState initial index‖ ^ 2 =
          puncturedWholeVorticityKineticMass
            (run initial index).contact.physicalState :=
        wholeRestartContactVelocityState_norm_sq initial index
      _ ≤
          puncturedWholeVorticityKineticMass
            (run initial 0).contact.physicalState := massLe
      _ = ‖wholeRestartContactVelocityState initial 0‖ ^ 2 :=
        (wholeRestartContactVelocityState_norm_sq initial 0).symm
  nlinarith [norm_nonneg (wholeRestartContactVelocityState initial index),
    norm_nonneg (wholeRestartContactVelocityState initial 0)]

/-! ## Source-generated physical velocity weak endpoint -/

/-- Riesz realization of one actual physical velocity contact in the weak
dual carrier used by sequential Banach--Alaoglu. -/
def wholeRestartContactVelocityWeakDual
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : ℕ) : WeakDual ℂ WholeRestartVelocityEndpointState :=
  StrongDual.toWeakDual
    (InnerProductSpace.toDual ℂ WholeRestartVelocityEndpointState
      (wholeRestartContactVelocityState initial index))

theorem wholeRestartContactVelocityWeakDual_mem_initialClosedBall
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : ℕ) :
    wholeRestartContactVelocityWeakDual initial index ∈
      WeakDual.toStrongDual ⁻¹'
        Metric.closedBall 0
          ‖wholeRestartContactVelocityState initial 0‖ := by
  change
    dist
        (WeakDual.toStrongDual
          (wholeRestartContactVelocityWeakDual initial index))
        0 ≤
      ‖wholeRestartContactVelocityState initial 0‖
  rw [dist_zero_right]
  change
    ‖InnerProductSpace.toDual ℂ WholeRestartVelocityEndpointState
        (wholeRestartContactVelocityState initial index)‖ ≤
      ‖wholeRestartContactVelocityState initial 0‖
  rw [(InnerProductSpace.toDual
    ℂ WholeRestartVelocityEndpointState).norm_map]
  exact wholeRestartContactVelocityState_norm_le_initial initial index

/-- Weak convergence against every Hilbert test preserves every concrete
Fourier-coordinate observation. -/
theorem velocityWeakTendsto_coordinate
    (sequence : ℕ → WholeRestartVelocityEndpointState)
    (endpoint : WholeRestartVelocityEndpointState)
    (weakTendsto :
      ∀ test : WholeRestartVelocityEndpointState,
        Tendsto
          (fun index => inner ℂ (sequence index) test)
          atTop (nhds (inner ℂ endpoint test)))
    (wave : NonzeroIntegerWavevector)
    (coordinate : Coordinate) :
    Tendsto
      (fun index => sequence index wave coordinate)
      atTop (nhds (endpoint wave coordinate)) := by
  classical
  let rowTest : ComplexCoordinateEuclidean :=
    EuclideanSpace.single coordinate (1 : ℂ)
  let test : WholeRestartVelocityEndpointState :=
    lp.single 2 wave rowTest
  have conjugateTendsto :
      Tendsto
        (fun index => (starRingEnd ℂ) (sequence index wave coordinate))
        atTop (nhds ((starRingEnd ℂ) (endpoint wave coordinate))) := by
    simpa only [test, rowTest, lp.inner_single_right,
      EuclideanSpace.inner_single_right, one_mul] using
        weakTendsto test
  have restoredTendsto :=
    (continuous_star.tendsto
      ((starRingEnd ℂ) (endpoint wave coordinate))).comp
      conjugateTendsto
  have sourceEq :
      (star ∘
          fun index =>
            (starRingEnd ℂ) (sequence index wave coordinate)) =
        (fun index => sequence index wave coordinate) := by
    funext index
    exact starRingEnd_self_apply _
  rw [sourceEq] at restoredTendsto
  simpa only [Complex.star_def, Complex.conj_conj] using restoredTendsto

/-- Divergence freedom is closed under the generated Hilbert-weak endpoint
transport because every fixed Fourier row is a finite coordinate readout. -/
theorem velocityWeakLimit_transverse
    (sequence : ℕ → WholeRestartVelocityEndpointState)
    (endpoint : WholeRestartVelocityEndpointState)
    (weakTendsto :
      ∀ test : WholeRestartVelocityEndpointState,
        Tendsto
          (fun index => inner ℂ (sequence index) test)
          atTop (nhds (inner ℂ endpoint test)))
    (sequenceTransverse :
      ∀ index, WholeRestartVelocityEndpointTransverse (sequence index)) :
    WholeRestartVelocityEndpointTransverse endpoint := by
  intro wave
  have rowTendsto :
      Tendsto
        (fun index coordinate => sequence index wave coordinate)
        atTop
        (nhds (fun coordinate => endpoint wave coordinate)) := by
    rw [tendsto_pi_nhds]
    intro coordinate
    exact velocityWeakTendsto_coordinate
      sequence endpoint weakTendsto wave coordinate
  have dotTendsto :
      Tendsto
        (fun index =>
          complexWavevector wave.1 ⬝ᵥ
            (fun coordinate => sequence index wave coordinate))
        atTop
        (nhds
          (complexWavevector wave.1 ⬝ᵥ
            (fun coordinate => endpoint wave coordinate))) :=
    ((continuous_const.dotProduct continuous_id).tendsto
      (fun coordinate => endpoint wave coordinate)).comp rowTendsto
  have generatedDotTendsto :
      Tendsto
        (fun index =>
          complexWavevector wave.1 ⬝ᵥ
            (fun coordinate => sequence index wave coordinate))
        atTop (nhds 0) := by
    have sourceEq :
        (fun index =>
          complexWavevector wave.1 ⬝ᵥ
            (fun coordinate => sequence index wave coordinate)) =
          (fun _ : ℕ => (0 : ℂ)) := by
      funext index
      exact sequenceTransverse index wave
    rw [sourceEq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique dotTendsto generatedDotTendsto

/-- Fourier reality is closed under the same weak endpoint transport, with
positive and negative rows compared before the coefficient quotient. -/
theorem velocityWeakLimit_reality
    (sequence : ℕ → WholeRestartVelocityEndpointState)
    (endpoint : WholeRestartVelocityEndpointState)
    (weakTendsto :
      ∀ test : WholeRestartVelocityEndpointState,
        Tendsto
          (fun index => inner ℂ (sequence index) test)
          atTop (nhds (inner ℂ endpoint test)))
    (sequenceReality :
      ∀ index, WholeRestartVelocityEndpointReality (sequence index)) :
    WholeRestartVelocityEndpointReality endpoint := by
  intro wave coordinate
  have positiveTendsto :=
    velocityWeakTendsto_coordinate
      sequence endpoint weakTendsto wave coordinate
  have conjugateTendsto :
      Tendsto
        (fun index => star (sequence index wave coordinate))
        atTop (nhds (star (endpoint wave coordinate))) := by
    simpa only [Function.comp_def] using
      (continuous_star.tendsto (endpoint wave coordinate)).comp
        positiveTendsto
  have negativeAsConjugateTendsto :
      Tendsto
        (fun index =>
          sequence index (nonzeroIntegerWavevectorNeg wave) coordinate)
        atTop (nhds (star (endpoint wave coordinate))) := by
    have sourceEq :
        (fun index =>
          sequence index (nonzeroIntegerWavevectorNeg wave) coordinate) =
        (fun index => star (sequence index wave coordinate)) := by
      funext index
      exact sequenceReality index wave coordinate
    rw [sourceEq]
    exact conjugateTendsto
  exact tendsto_nhds_unique
    (velocityWeakTendsto_coordinate sequence endpoint weakTendsto
      (nonzeroIntegerWavevectorNeg wave) coordinate)
    negativeAsConjugateTendsto

/-- Compactness of the velocity sequence after a previously generated
source subsequence.  This private helper is used to keep kinetic and
velocity limits on one actual lineage. -/
private theorem exists_wholeRestartContactVelocityWeakEndpoint_along
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (sourceSubsequence : ℕ → ℕ) :
    ∃ endpoint : WholeRestartVelocityEndpointState,
      ∃ subsubsequence : ℕ → ℕ,
        StrictMono subsubsequence ∧
          ‖endpoint‖ ≤
            ‖wholeRestartContactVelocityState initial 0‖ ∧
          ∀ test : WholeRestartVelocityEndpointState,
            Tendsto
              (fun index =>
                inner ℂ
                  (wholeRestartContactVelocityState initial
                    (sourceSubsequence (subsubsequence index)))
                  test)
              atTop
              (nhds (inner ℂ endpoint test)) := by
  let radius := ‖wholeRestartContactVelocityState initial 0‖
  let sequence : ℕ → WeakDual ℂ WholeRestartVelocityEndpointState :=
    fun index =>
      wholeRestartContactVelocityWeakDual initial
        (sourceSubsequence index)
  have sequenceMem :
      ∀ index,
        sequence index ∈
          WeakDual.toStrongDual ⁻¹'
            Metric.closedBall 0 radius := by
    intro index
    exact wholeRestartContactVelocityWeakDual_mem_initialClosedBall
      initial (sourceSubsequence index)
  obtain ⟨limitDual, limitMem, subsubsequence, subsubsequenceMono,
      dualTendsto⟩ :=
    (WeakDual.isSeqCompact_closedBall
      ℂ WholeRestartVelocityEndpointState 0 radius) sequenceMem
  let endpoint : WholeRestartVelocityEndpointState :=
    (InnerProductSpace.toDual ℂ WholeRestartVelocityEndpointState).symm
      (WeakDual.toStrongDual limitDual)
  have endpointNormLe :
      ‖endpoint‖ ≤
        ‖wholeRestartContactVelocityState initial 0‖ := by
    change dist (WeakDual.toStrongDual limitDual) 0 ≤ radius at limitMem
    have dualNormLe :
        ‖WeakDual.toStrongDual limitDual‖ ≤ radius := by
      simpa only [dist_zero_right] using limitMem
    change
      ‖(InnerProductSpace.toDual
          ℂ WholeRestartVelocityEndpointState).symm
          (WeakDual.toStrongDual limitDual)‖ ≤
        ‖wholeRestartContactVelocityState initial 0‖
    rw [(InnerProductSpace.toDual
      ℂ WholeRestartVelocityEndpointState).symm.norm_map]
    simpa only [radius] using dualNormLe
  refine
    ⟨endpoint, subsubsequence, subsubsequenceMono, endpointNormLe, ?_⟩
  intro test
  have evaluated :=
    (WeakDual.eval_continuous test).tendsto limitDual
      |>.comp dualTendsto
  have sourceEq :
      (fun index => sequence (subsubsequence index) test) =
        (fun index =>
          inner ℂ
            (wholeRestartContactVelocityState initial
              (sourceSubsequence (subsubsequence index))) test) := by
    funext index
    change
      (InnerProductSpace.toDual
        ℂ WholeRestartVelocityEndpointState
        (wholeRestartContactVelocityState initial
          (sourceSubsequence (subsubsequence index)))) test =
        inner ℂ
          (wholeRestartContactVelocityState initial
            (sourceSubsequence (subsubsequence index))) test
    exact InnerProductSpace.toDual_apply_apply
  have targetEq :
      limitDual test = inner ℂ endpoint test := by
    calc
      limitDual test = (WeakDual.toStrongDual limitDual) test := rfl
      _ = inner ℂ endpoint test := by
        symm
        exact InnerProductSpace.toDual_symm_apply
  change
    Tendsto
      (fun index => sequence (subsubsequence index) test)
      atTop (nhds (limitDual test)) at evaluated
  rw [sourceEq, targetEq] at evaluated
  exact evaluated

/-- Kinetic and physical-velocity weak endpoints generated on the same
actual native contacts.  The second compactness extraction is composed with
the first, so no independently chosen lineage enters the result. -/
theorem exists_wholeRestartContactKineticVelocityWeakEndpoints
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ∃ kineticEndpoint : WholeRestartKineticEndpointState,
      ∃ velocityEndpoint : WholeRestartVelocityEndpointState,
        ∃ subsequence : ℕ → ℕ,
          StrictMono subsequence ∧
            ‖kineticEndpoint‖ ≤
              ‖wholeRestartContactKineticState initial 0‖ ∧
            ‖velocityEndpoint‖ ≤
              ‖wholeRestartContactVelocityState initial 0‖ ∧
            (∀ test : WholeRestartKineticEndpointState,
              Tendsto
                (fun index =>
                  inner ℂ
                    (wholeRestartContactKineticState
                      initial (subsequence index))
                    test)
                atTop
                (nhds (inner ℂ kineticEndpoint test))) ∧
            (∀ test : WholeRestartVelocityEndpointState,
              Tendsto
                  (fun index =>
                    inner ℂ
                      (wholeRestartContactVelocityState
                        initial (subsequence index))
                      test)
                  atTop
                  (nhds (inner ℂ velocityEndpoint test))) ∧
              WholeRestartVelocityEndpointTransverse velocityEndpoint ∧
              WholeRestartVelocityEndpointReality velocityEndpoint := by
  let kineticReceipt :=
    generatedWholeRestartKineticWeakEndpoint initial
  let kineticEndpoint := kineticReceipt.endpoint
  obtain ⟨velocityEndpoint, velocitySubsubsequence,
      velocitySubsubsequenceMono, velocityEndpointNormLe,
      velocityWeakTendsto⟩ :=
    exists_wholeRestartContactVelocityWeakEndpoint_along
      initial kineticReceipt.subsequence
  let sharedSubsequence : ℕ → ℕ :=
    kineticReceipt.subsequence ∘ velocitySubsubsequence
  have sharedSubsequenceMono : StrictMono sharedSubsequence :=
    kineticReceipt.subsequence_strictMono.comp
      velocitySubsubsequenceMono
  have kineticWeakTendstoShared :
      ∀ test : WholeRestartKineticEndpointState,
        Tendsto
          (fun index =>
            inner ℂ
              (wholeRestartContactKineticState
                initial (sharedSubsequence index)) test)
          atTop (nhds (inner ℂ kineticEndpoint test)) := by
    intro test
    simpa only [sharedSubsequence, Function.comp_def] using
      (kineticReceipt.weak_tendsto test).comp
        velocitySubsubsequenceMono.tendsto_atTop
  have velocityWeakTendstoShared :
      ∀ test : WholeRestartVelocityEndpointState,
        Tendsto
          (fun index =>
            inner ℂ
              (wholeRestartContactVelocityState
                initial (sharedSubsequence index)) test)
          atTop (nhds (inner ℂ velocityEndpoint test)) := by
    intro test
    simpa only [sharedSubsequence, Function.comp_def] using
      velocityWeakTendsto test
  have velocityEndpointTransverse :
      WholeRestartVelocityEndpointTransverse velocityEndpoint :=
    velocityWeakLimit_transverse
      (fun index =>
        wholeRestartContactVelocityState
          initial (sharedSubsequence index))
      velocityEndpoint velocityWeakTendstoShared
      (fun index =>
        wholeRestartContactVelocityState_transverse
          initial (sharedSubsequence index))
  have velocityEndpointReality :
      WholeRestartVelocityEndpointReality velocityEndpoint :=
    velocityWeakLimit_reality
      (fun index =>
        wholeRestartContactVelocityState
          initial (sharedSubsequence index))
      velocityEndpoint velocityWeakTendstoShared
      (fun index =>
        wholeRestartContactVelocityState_reality
          initial (sharedSubsequence index))
  exact
    ⟨kineticEndpoint, velocityEndpoint, sharedSubsequence,
      sharedSubsequenceMono, kineticReceipt.endpoint_norm_le_initial,
      velocityEndpointNormLe, kineticWeakTendstoShared,
      velocityWeakTendstoShared, velocityEndpointTransverse,
      velocityEndpointReality⟩

/-- The finite accumulation time generated by the actual native run. -/
def wholeRestartVelocityAccumulationTime
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : ℝ :=
  ⨆ index : ℕ, elapsedTime initial index

/-- Under bounded elapsed time, the same generated native contacts carry
both the kinetic and physical-velocity weak endpoints and converge to the
source-owned accumulation time. -/
theorem exists_wholeRestartContactKineticVelocityWeakEndpoints_at_accumulation
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ∃ kineticEndpoint : WholeRestartKineticEndpointState,
      ∃ velocityEndpoint : WholeRestartVelocityEndpointState,
        ∃ subsequence : ℕ → ℕ,
          StrictMono subsequence ∧
            ‖kineticEndpoint‖ ≤
              ‖wholeRestartContactKineticState initial 0‖ ∧
            ‖velocityEndpoint‖ ≤
              ‖wholeRestartContactVelocityState initial 0‖ ∧
            Tendsto
              (fun index => elapsedTime initial (subsequence index))
              atTop
              (nhds (wholeRestartVelocityAccumulationTime initial)) ∧
            (∀ test : WholeRestartKineticEndpointState,
              Tendsto
                (fun index =>
                  inner ℂ
                    (wholeRestartContactKineticState
                      initial (subsequence index))
                    test)
                atTop
                (nhds (inner ℂ kineticEndpoint test))) ∧
            (∀ test : WholeRestartVelocityEndpointState,
              Tendsto
                (fun index =>
                  inner ℂ
                    (wholeRestartContactVelocityState
                      initial (subsequence index))
                    test)
                atTop
                (nhds (inner ℂ velocityEndpoint test))) ∧
            WholeRestartVelocityEndpointTransverse velocityEndpoint ∧
            WholeRestartVelocityEndpointReality velocityEndpoint := by
  obtain ⟨kineticEndpoint, velocityEndpoint, subsequence,
      subsequenceMono, kineticEndpointNormLe, velocityEndpointNormLe,
      kineticWeakTendsto, velocityWeakTendsto,
      velocityEndpointTransverse, velocityEndpointReality⟩ :=
    exists_wholeRestartContactKineticVelocityWeakEndpoints initial
  have elapsedTendsto :
      Tendsto
        (fun index => elapsedTime initial (subsequence index))
        atTop
        (nhds (wholeRestartVelocityAccumulationTime initial)) := by
    exact
      (tendsto_atTop_ciSup
        (elapsedTime_strictMono initial).monotone elapsedBounded).comp
          subsequenceMono.tendsto_atTop
  exact
    ⟨kineticEndpoint, velocityEndpoint, subsequence, subsequenceMono,
      kineticEndpointNormLe, velocityEndpointNormLe, elapsedTendsto,
      kineticWeakTendsto, velocityWeakTendsto,
      velocityEndpointTransverse, velocityEndpointReality⟩

/-! ## Canonical Type-valued endpoint receipt -/

/-- Source-owned bounded-accumulation endpoint data.  All fields are selected
internally from the actual native run; the index only records the bounded-time
case in which this endpoint producer is consumed. -/
structure GeneratedWholeRestartVelocityWeakEndpointAtAccumulation
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (_elapsedBounded : BddAbove (Set.range (elapsedTime initial))) where
  kineticReceipt :
    GeneratedWholeRestartKineticWeakEndpointAtAccumulation initial
  velocityEndpoint : WholeRestartVelocityEndpointState
  velocitySubsubsequence : ℕ → ℕ
  velocitySubsubsequence_strictMono : StrictMono velocitySubsubsequence
  velocityEndpoint_norm_le :
    ‖velocityEndpoint‖ ≤ ‖wholeRestartContactVelocityState initial 0‖
  velocity_weak_tendsto :
    ∀ test : WholeRestartVelocityEndpointState,
      Tendsto
        (fun index =>
          inner ℂ
            (wholeRestartContactVelocityState
              initial
              (kineticReceipt.subsequence
                (velocitySubsubsequence index)))
            test)
        atTop
        (nhds (inner ℂ velocityEndpoint test))
  velocityEndpoint_transverse :
    WholeRestartVelocityEndpointTransverse velocityEndpoint
  velocityEndpoint_reality :
    WholeRestartVelocityEndpointReality velocityEndpoint

namespace GeneratedWholeRestartVelocityWeakEndpointAtAccumulation

/-- The exact native contacts shared by the canonical kinetic endpoint and
its physical-velocity sublimit. -/
def subsequence
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {elapsedBounded : BddAbove (Set.range (elapsedTime initial))}
    (receipt :
      GeneratedWholeRestartVelocityWeakEndpointAtAccumulation
        initial elapsedBounded) : ℕ → ℕ :=
  receipt.kineticReceipt.subsequence ∘ receipt.velocitySubsubsequence

theorem subsequence_strictMono
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {elapsedBounded : BddAbove (Set.range (elapsedTime initial))}
    (receipt :
      GeneratedWholeRestartVelocityWeakEndpointAtAccumulation
        initial elapsedBounded) :
    StrictMono receipt.subsequence :=
  receipt.kineticReceipt.subsequence_strictMono.comp
    receipt.velocitySubsubsequence_strictMono

/-- The shared contacts still converge to the same source-generated
accumulation time. -/
theorem elapsed_tendsto
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {elapsedBounded : BddAbove (Set.range (elapsedTime initial))}
    (receipt :
      GeneratedWholeRestartVelocityWeakEndpointAtAccumulation
        initial elapsedBounded) :
    Tendsto
      (fun index => elapsedTime initial (receipt.subsequence index))
      atTop
      (nhds (wholeRestartVelocityAccumulationTime initial)) := by
  simpa only [subsequence, Function.comp_def,
    wholeRestartVelocityAccumulationTime, wholeRestartAccumulationTime] using
      receipt.kineticReceipt.elapsed_tendsto.comp
        receipt.velocitySubsubsequence_strictMono.tendsto_atTop

/-- The kinetic endpoint remains the canonical endpoint selected upstream,
now read on the same refined contacts as the physical velocity endpoint. -/
theorem kinetic_weak_tendsto
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {elapsedBounded : BddAbove (Set.range (elapsedTime initial))}
    (receipt :
      GeneratedWholeRestartVelocityWeakEndpointAtAccumulation
        initial elapsedBounded)
    (test : WholeRestartKineticEndpointState) :
    Tendsto
      (fun index =>
        inner ℂ
          (wholeRestartContactKineticState
            initial (receipt.subsequence index))
          test)
      atTop
      (nhds (inner ℂ receipt.kineticReceipt.endpoint test)) := by
  simpa only [subsequence, Function.comp_def] using
    (receipt.kineticReceipt.weak_tendsto test).comp
      receipt.velocitySubsubsequence_strictMono.tendsto_atTop

/-- The velocity field and upstream kinetic endpoint are observed on exactly
the same actual contact indices. -/
theorem velocity_weak_tendsto_shared
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {elapsedBounded : BddAbove (Set.range (elapsedTime initial))}
    (receipt :
      GeneratedWholeRestartVelocityWeakEndpointAtAccumulation
        initial elapsedBounded)
    (test : WholeRestartVelocityEndpointState) :
    Tendsto
      (fun index =>
        inner ℂ
          (wholeRestartContactVelocityState
            initial (receipt.subsequence index))
          test)
      atTop
      (nhds (inner ℂ receipt.velocityEndpoint test)) := by
  simpa only [subsequence, Function.comp_def] using
    receipt.velocity_weak_tendsto test

end GeneratedWholeRestartVelocityWeakEndpointAtAccumulation

/-- Canonical generated endpoint receipt for the bounded-accumulation case.
The caller supplies neither endpoint, subsequence, norm bound, nor physical
law certificate. -/
noncomputable def generatedWholeRestartVelocityWeakEndpointAtAccumulation
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    GeneratedWholeRestartVelocityWeakEndpointAtAccumulation
      initial elapsedBounded := by
  let kineticReceipt :=
    generatedWholeRestartKineticWeakEndpointAtAccumulation
      initial elapsedBounded
  let velocityResult :=
    exists_wholeRestartContactVelocityWeakEndpoint_along
      initial kineticReceipt.subsequence
  let velocityEndpoint := Classical.choose velocityResult
  let velocitySubsequenceResult := Classical.choose_spec velocityResult
  let velocitySubsubsequence := Classical.choose velocitySubsequenceResult
  have velocitySpecifications :=
    Classical.choose_spec velocitySubsequenceResult
  have velocitySubsubsequenceMono : StrictMono velocitySubsubsequence :=
    velocitySpecifications.1
  have velocityEndpointNormLe :
      ‖velocityEndpoint‖ ≤
        ‖wholeRestartContactVelocityState initial 0‖ :=
    velocitySpecifications.2.1
  have velocityWeakTendsto :
      ∀ test : WholeRestartVelocityEndpointState,
        Tendsto
          (fun index =>
            inner ℂ
              (wholeRestartContactVelocityState initial
                (kineticReceipt.subsequence
                  (velocitySubsubsequence index)))
              test)
          atTop
          (nhds (inner ℂ velocityEndpoint test)) :=
    velocitySpecifications.2.2
  have velocityEndpointTransverse :
      WholeRestartVelocityEndpointTransverse velocityEndpoint :=
    velocityWeakLimit_transverse
      (fun index =>
        wholeRestartContactVelocityState initial
          (kineticReceipt.subsequence (velocitySubsubsequence index)))
      velocityEndpoint velocityWeakTendsto
      (fun index =>
        wholeRestartContactVelocityState_transverse initial
          (kineticReceipt.subsequence (velocitySubsubsequence index)))
  have velocityEndpointReality :
      WholeRestartVelocityEndpointReality velocityEndpoint :=
    velocityWeakLimit_reality
      (fun index =>
        wholeRestartContactVelocityState initial
          (kineticReceipt.subsequence (velocitySubsubsequence index)))
      velocityEndpoint velocityWeakTendsto
      (fun index =>
        wholeRestartContactVelocityState_reality initial
          (kineticReceipt.subsequence (velocitySubsubsequence index)))
  exact
    { kineticReceipt := kineticReceipt
      velocityEndpoint := velocityEndpoint
      velocitySubsubsequence := velocitySubsubsequence
      velocitySubsubsequence_strictMono := velocitySubsubsequenceMono
      velocityEndpoint_norm_le := velocityEndpointNormLe
      velocity_weak_tendsto := velocityWeakTendsto
      velocityEndpoint_transverse := velocityEndpointTransverse
      velocityEndpoint_reality := velocityEndpointReality }

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
end NavierStokes
end SaturationMonoid
