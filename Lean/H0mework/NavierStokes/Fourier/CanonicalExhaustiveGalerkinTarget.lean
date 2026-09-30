import H0mework.NavierStokes.WholeSpace.InfiniteFixedOutputNonlinearRow
import H0mework.NavierStokes.Galerkin.MildDuhamel

/-!
# Canonical exhaustive Galerkin target for the infinite nonlinear row

This module substitutes sharply supported canonical integer-cube Galerkin
states into the genuine full-lattice Fourier vorticity equation.

At every wave, the exact Galerkin tangent equals the full infinite-row
tangent minus one explicit omitted nonlinear projection complement.  Hence:

* retained waves satisfy the full-lattice differential law exactly;
* omitted waves have zero Galerkin derivative and carry the explicit negative
  infinite nonlinear row as their PDE residual;
* every fixed wave is eventually retained by the canonical cube exhaustion,
  so both its omitted defect and its full-lattice residual are eventually
  identically zero;
* the same replacement is exact inside the Fourier mild/Duhamel identity,
  and is eventually available at every fixed wave.

The exhaustion theorem generates fixed-wave coverage internally.  No target
limit, support-coverage certificate, tail-silence field, compactness witness,
or continuation conclusion appears in a theorem mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget

open scoped BigOperators ENNReal Topology

open Set
open Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow

noncomputable section

/-- Full-lattice Fourier tangent read from the actual infinite nonlinear row
and the exact viscous multiplier. -/
def wholeLatticeVorticityFourierTangentAt
    (ν : ℝ)
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : ComplexCoordinateVector :=
  wholeStateVorticityNonlinearCoefficientAt state wave -
    (ν * integerWaveViscousMultiplier wave) • state wave

/-- Nonlinear row omitted by the canonical sharp Galerkin projection. -/
def canonicalCubeOmittedNonlinearDefectAt
    (radius : ℕ)
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : ComplexCoordinateVector :=
  if wave ∈ integerWaveFrequencyCube radius then 0
  else wholeStateVorticityNonlinearCoefficientAt state wave

/-- Full-lattice PDE residual of a proposed whole-carrier tangent. -/
def wholeLatticeVorticityFourierPDEResidualAt
    (ν : ℝ)
    (state tangent : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : ComplexCoordinateVector :=
  tangent wave -
    wholeLatticeVorticityFourierTangentAt ν state wave

theorem complexSharpSupportProjection_eq_self_of_supported
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (supported :
      ∀ wave : IntegerWavevector,
        wave ∉ modes → state wave = 0) :
    complexSharpSupportProjection modes state = state := by
  ext wave
  by_cases waveMem : wave ∈ modes
  · simp [complexSharpSupportProjection_apply, waveMem]
  · simp [complexSharpSupportProjection_apply, waveMem,
      supported wave waveMem]

/-- A sharply supported canonical Galerkin generator is exactly the
full-lattice tangent minus the omitted nonlinear projection complement. -/
theorem canonicalCube_generator_eq_wholeTangent_sub_omittedDefect
    (radius : ℕ)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState)
    (supported :
      ∀ wave : IntegerWavevector,
        wave ∉ integerWaveFrequencyCube radius →
          state wave = 0)
    (wave : IntegerWavevector) :
    finiteStateVorticityGenerator
        (integerWaveFrequencyCube radius) ν state wave =
      wholeLatticeVorticityFourierTangentAt ν state wave -
        canonicalCubeOmittedNonlinearDefectAt radius state wave := by
  have nonlinearEq :
      wholeStateVorticityNonlinearCoefficientAt state wave =
        finiteStateVorticityNonlinearCoefficientAt
          (integerWaveFrequencyCube radius) state wave :=
    wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
      (integerWaveFrequencyCube radius) state supported wave
  by_cases waveMem : wave ∈ integerWaveFrequencyCube radius
  · simp [finiteStateVorticityGenerator_apply,
      wholeLatticeVorticityFourierTangentAt,
      canonicalCubeOmittedNonlinearDefectAt,
      waveMem, nonlinearEq]
  · have stateZero := supported wave waveMem
    simp [finiteStateVorticityGenerator_apply,
      wholeLatticeVorticityFourierTangentAt,
      canonicalCubeOmittedNonlinearDefectAt,
      waveMem, stateZero]

/-- The full-lattice residual of the actual canonical Galerkin tangent is
the negative omitted projection complement, at every Fourier wave. -/
theorem canonicalCube_fullLatticePDEResidual_eq_neg_omittedDefect
    (radius : ℕ)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState)
    (supported :
      ∀ wave : IntegerWavevector,
        wave ∉ integerWaveFrequencyCube radius →
          state wave = 0)
    (wave : IntegerWavevector) :
    wholeLatticeVorticityFourierPDEResidualAt ν state
        (finiteStateVorticityGenerator
          (integerWaveFrequencyCube radius) ν state) wave =
      -canonicalCubeOmittedNonlinearDefectAt radius state wave := by
  rw [wholeLatticeVorticityFourierPDEResidualAt,
    canonicalCube_generator_eq_wholeTangent_sub_omittedDefect
      radius ν state supported wave]
  abel

/-- On every retained canonical-cube wave, the actual Galerkin tangent is
already the exact full-lattice infinite-row tangent. -/
theorem canonicalCube_generator_eq_wholeTangent_of_mem
    (radius : ℕ)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState)
    (supported :
      ∀ wave : IntegerWavevector,
        wave ∉ integerWaveFrequencyCube radius →
          state wave = 0)
    (wave : IntegerWavevector)
    (waveMem : wave ∈ integerWaveFrequencyCube radius) :
    finiteStateVorticityGenerator
        (integerWaveFrequencyCube radius) ν state wave =
      wholeLatticeVorticityFourierTangentAt ν state wave := by
  rw [canonicalCube_generator_eq_wholeTangent_sub_omittedDefect
    radius ν state supported wave]
  simp [canonicalCubeOmittedNonlinearDefectAt, waveMem]

/-- On an omitted wave, the canonical Galerkin tangent is zero and the full
PDE residual is the explicit negative infinite nonlinear row. -/
theorem canonicalCube_fullLatticePDEResidual_eq_neg_infiniteRow_of_not_mem
    (radius : ℕ)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState)
    (supported :
      ∀ wave : IntegerWavevector,
        wave ∉ integerWaveFrequencyCube radius →
          state wave = 0)
    (wave : IntegerWavevector)
    (waveNotMem : wave ∉ integerWaveFrequencyCube radius) :
    wholeLatticeVorticityFourierPDEResidualAt ν state
        (finiteStateVorticityGenerator
          (integerWaveFrequencyCube radius) ν state) wave =
      -wholeStateVorticityNonlinearCoefficientAt state wave := by
  rw [canonicalCube_fullLatticePDEResidual_eq_neg_omittedDefect
    radius ν state supported wave]
  simp [canonicalCubeOmittedNonlinearDefectAt, waveNotMem]

/-- The actual row derivative of a sharply supported canonical Galerkin
trajectory is the full-lattice tangent with precisely the omitted nonlinear
defect written back. -/
theorem canonicalCube_trajectoryWave_hasDerivAt_wholeTangent_sub_omittedDefect
    (radius : ℕ)
    (ν : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (evolves :
      HasDerivAt trajectory
        (finiteStateVorticityGenerator
          (integerWaveFrequencyCube radius) ν (trajectory t)) t)
    (supported :
      ∀ wave : IntegerWavevector,
        wave ∉ integerWaveFrequencyCube radius →
          trajectory t wave = 0)
    (wave : IntegerWavevector) :
    HasDerivAt
      (fun time => trajectory time wave)
      (wholeLatticeVorticityFourierTangentAt
          ν (trajectory t) wave -
        canonicalCubeOmittedNonlinearDefectAt
          radius (trajectory t) wave)
      t := by
  have rowDerivative :=
    complexVorticityTrajectoryWave_hasDerivAt
      trajectory t
      (finiteStateVorticityGenerator
        (integerWaveFrequencyCube radius) ν (trajectory t))
      wave evolves
  rw [canonicalCube_generator_eq_wholeTangent_sub_omittedDefect
    radius ν (trajectory t) supported wave] at rowDerivative
  exact rowDerivative

/-- A retained wave of an actual canonical Galerkin trajectory satisfies the
full infinite-row Fourier Navier--Stokes law exactly. -/
theorem canonicalCube_trajectoryWave_hasDerivAt_wholeTangent_of_mem
    (radius : ℕ)
    (ν : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (evolves :
      HasDerivAt trajectory
        (finiteStateVorticityGenerator
          (integerWaveFrequencyCube radius) ν (trajectory t)) t)
    (supported :
      ∀ wave : IntegerWavevector,
        wave ∉ integerWaveFrequencyCube radius →
          trajectory t wave = 0)
    (wave : IntegerWavevector)
    (waveMem : wave ∈ integerWaveFrequencyCube radius) :
    HasDerivAt
      (fun time => trajectory time wave)
      (wholeLatticeVorticityFourierTangentAt
        ν (trajectory t) wave)
      t := by
  simpa [canonicalCubeOmittedNonlinearDefectAt, waveMem] using
    canonicalCube_trajectoryWave_hasDerivAt_wholeTangent_sub_omittedDefect
      radius ν trajectory t evolves supported wave

/-- Every omitted wave of the finite Galerkin trajectory has zero actual
derivative; its full-lattice discrepancy is therefore exactly the explicit
omitted nonlinear defect above. -/
theorem canonicalCube_trajectoryWave_hasDerivAt_zero_of_not_mem
    (radius : ℕ)
    (ν : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (evolves :
      HasDerivAt trajectory
        (finiteStateVorticityGenerator
          (integerWaveFrequencyCube radius) ν (trajectory t)) t)
    (wave : IntegerWavevector)
    (waveNotMem : wave ∉ integerWaveFrequencyCube radius) :
    HasDerivAt
      (fun time => trajectory time wave)
      0
      t := by
  have rowDerivative :=
    complexVorticityTrajectoryWave_hasDerivAt
      trajectory t
      (finiteStateVorticityGenerator
        (integerWaveFrequencyCube radius) ν (trajectory t))
      wave evolves
  simpa [finiteStateVorticityGenerator_apply, waveNotMem] using
    rowDerivative

/-- Canonical lattice exhaustion itself, without a caller-supplied coverage
premise, makes the omitted defect at every fixed wave eventually vanish. -/
theorem canonicalCubeOmittedNonlinearDefectAt_eventually_eq_zero
    (states : ℕ → ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    ∀ᶠ radius : ℕ in atTop,
      canonicalCubeOmittedNonlinearDefectAt
        radius (states radius) wave = 0 := by
  filter_upwards
    [integerWave_eventually_mem_frequencyCube wave] with radius waveMem
  simp [canonicalCubeOmittedNonlinearDefectAt, waveMem]

/-- Consequently the full-lattice PDE residual of any sharply supported
canonical Galerkin state family is eventually zero at each fixed wave. -/
theorem canonicalCube_fullLatticePDEResidual_eventually_eq_zero
    (ν : ℝ)
    (states : ℕ → ComplexVorticityHilbertState)
    (supported :
      ∀ radius wave,
        wave ∉ integerWaveFrequencyCube radius →
          states radius wave = 0)
    (wave : IntegerWavevector) :
    ∀ᶠ radius : ℕ in atTop,
      wholeLatticeVorticityFourierPDEResidualAt
          ν (states radius)
          (finiteStateVorticityGenerator
            (integerWaveFrequencyCube radius) ν (states radius))
          wave = 0 := by
  filter_upwards
    [integerWave_eventually_mem_frequencyCube wave] with radius waveMem
  rw [canonicalCube_fullLatticePDEResidual_eq_neg_omittedDefect
    radius ν (states radius) (supported radius) wave]
  simp [canonicalCubeOmittedNonlinearDefectAt, waveMem]

/-- For an actual family of canonical Galerkin trajectories, every fixed
Fourier wave eventually satisfies the exact infinite-row differential law.
The required membership is generated by the canonical exhaustion. -/
theorem canonicalCube_trajectoryWave_eventually_hasDerivAt_wholeTangent
    (ν : ℝ)
    (trajectories : ℕ → ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (evolves :
      ∀ radius,
        HasDerivAt (trajectories radius)
          (finiteStateVorticityGenerator
            (integerWaveFrequencyCube radius) ν
            (trajectories radius t))
          t)
    (supported :
      ∀ radius wave,
        wave ∉ integerWaveFrequencyCube radius →
          trajectories radius t wave = 0)
    (wave : IntegerWavevector) :
    ∀ᶠ radius : ℕ in atTop,
      HasDerivAt
        (fun time => trajectories radius time wave)
        (wholeLatticeVorticityFourierTangentAt
          ν (trajectories radius t) wave)
        t := by
  filter_upwards
    [integerWave_eventually_mem_frequencyCube wave] with radius waveMem
  exact
    canonicalCube_trajectoryWave_hasDerivAt_wholeTangent_of_mem
      radius ν (trajectories radius) t
      (evolves radius) (supported radius) wave waveMem

/-! ## Exact infinite-row mild identity -/

/-- The exact finite Galerkin mild identity can be written with the genuine
full-lattice nonlinear row on every retained canonical-cube frequency.
Support preservation is consumed from the actual trajectory at each time. -/
theorem canonicalCubeWave_infiniteRow_mild_identity
    (radius : ℕ)
    (wave : IntegerWavevector)
    (waveMem : wave ∈ integerWaveFrequencyCube radius)
    (ν : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (a b : ℝ)
    (hab : a ≤ b)
    (evolves :
      ∀ t ∈ Icc a b,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            (integerWaveFrequencyCube radius) ν (trajectory t)) t)
    (supported :
      ∀ t ∈ Icc a b,
        ∀ output : IntegerWavevector,
          output ∉ integerWaveFrequencyCube radius →
            trajectory t output = 0) :
    trajectory b wave =
      finiteStateVorticityHeatMultiplier ν (b - a) wave •
          trajectory a wave +
        ∫ t in a..b,
          finiteStateVorticityHeatMultiplier ν (b - t) wave •
            wholeStateVorticityNonlinearCoefficientAt
              (trajectory t) wave := by
  have finiteMild :=
    finiteGalerkinWave_mild_identity
      (integerWaveFrequencyCube radius) wave waveMem ν
      trajectory a b hab evolves
  rw [finiteMild]
  congr 1
  apply intervalIntegral.integral_congr
  intro t tMem
  have tInInterval : t ∈ Icc a b := by
    rwa [uIcc_of_le hab] at tMem
  change
    finiteStateVorticityHeatMultiplier ν (b - t) wave •
        finiteStateVorticityNonlinearCoefficientAt
          (integerWaveFrequencyCube radius) (trajectory t) wave =
      finiteStateVorticityHeatMultiplier ν (b - t) wave •
        wholeStateVorticityNonlinearCoefficientAt
          (trajectory t) wave
  rw [← wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
    (integerWaveFrequencyCube radius) (trajectory t)
    (supported t tInInterval) wave]

/-- At every fixed wave, the canonical Galerkin mild identities eventually
become exact full-lattice infinite-row identities.  No coverage hypothesis is
accepted: membership is produced by integer-cube exhaustion. -/
theorem canonicalCubeWave_eventually_infiniteRow_mild_identity
    (ν : ℝ)
    (trajectories : ℕ → ℝ → ComplexVorticityHilbertState)
    (a b : ℝ)
    (hab : a ≤ b)
    (evolves :
      ∀ radius t, t ∈ Icc a b →
        HasDerivAt (trajectories radius)
          (finiteStateVorticityGenerator
            (integerWaveFrequencyCube radius) ν
            (trajectories radius t)) t)
    (supported :
      ∀ radius t, t ∈ Icc a b →
        ∀ output : IntegerWavevector,
          output ∉ integerWaveFrequencyCube radius →
            trajectories radius t output = 0)
    (wave : IntegerWavevector) :
    ∀ᶠ radius : ℕ in atTop,
      trajectories radius b wave =
        finiteStateVorticityHeatMultiplier ν (b - a) wave •
            trajectories radius a wave +
          ∫ t in a..b,
            finiteStateVorticityHeatMultiplier ν (b - t) wave •
              wholeStateVorticityNonlinearCoefficientAt
                (trajectories radius t) wave := by
  filter_upwards
    [integerWave_eventually_mem_frequencyCube wave] with radius waveMem
  exact
    canonicalCubeWave_infiniteRow_mild_identity
      radius wave waveMem ν (trajectories radius) a b hab
      (fun t tMem => evolves radius t tMem)
      (fun t tMem => supported radius t tMem)

end

end ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
end NavierStokes
end SaturationMonoid
