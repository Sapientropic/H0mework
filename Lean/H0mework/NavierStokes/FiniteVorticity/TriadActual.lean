import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# An actual finite Fourier--Galerkin vorticity triad

This module constructs the first non-laminar Navier--Stokes calibration in
the repository.  The retained Fourier support is

```text
± {(1, 0), (1, 1), (-2, -1)}.
```

It is a two-dimensional periodic vorticity slice, equivalently a
`z`-independent incompressible three-dimensional slice.  The nonlinear
generator is not introduced as a table of desired coefficients: it is
computed from the complete `6 × 6` ordered Fourier-vorticity convolution on
that support.  The resulting three positive-mode coordinates are then proved
to be

```text
(-3/10 x₁x₂, 4/5 x₂x₀, -1/2 x₀x₁).
```

Adding the diagonal viscous multiplier gives the actual finite-dimensional
Navier--Stokes Galerkin tangent.  This is an infinitesimal Galerkin producer,
not an exact finite-time PDE flow or a vortex-stretching theorem.
-/

namespace SaturationMonoid.NavierStokes
namespace TwoDimensionalVorticityTriadActual

open scoped BigOperators

abbrev WaveVector := ℤ × ℤ
abbrev TriadState := Fin 3 → ℚ
abbrev SignedTriadState := Fin 6 → ℚ

def waveAdd (left right : WaveVector) : WaveVector :=
  (left.1 + right.1, left.2 + right.2)

def waveNeg (wave : WaveVector) : WaveVector :=
  (-wave.1, -wave.2)

def waveDet (left right : WaveVector) : ℤ :=
  left.1 * right.2 - left.2 * right.1

def waveNormSq (wave : WaveVector) : ℤ :=
  wave.1 ^ 2 + wave.2 ^ 2

def triadWaveZero : WaveVector := (1, 0)
def triadWaveOne : WaveVector := (1, 1)
def triadWaveTwo : WaveVector := (-2, -1)

def positiveTriadWave : Fin 3 → WaveVector :=
  ![triadWaveZero, triadWaveOne, triadWaveTwo]

theorem triadWave_sum_zero :
    waveAdd (waveAdd triadWaveZero triadWaveOne) triadWaveTwo =
      (0, 0) := by
  norm_num [waveAdd, triadWaveZero, triadWaveOne, triadWaveTwo]

@[simp] theorem triadWaveZero_normSq :
    waveNormSq triadWaveZero = 1 := by
  norm_num [waveNormSq, triadWaveZero]

@[simp] theorem triadWaveOne_normSq :
    waveNormSq triadWaveOne = 2 := by
  norm_num [waveNormSq, triadWaveOne]

@[simp] theorem triadWaveTwo_normSq :
    waveNormSq triadWaveTwo = 5 := by
  norm_num [waveNormSq, triadWaveTwo]

/-- The six retained signed modes. -/
def signedTriadWave : Fin 6 → WaveVector :=
  ![triadWaveZero, triadWaveOne, triadWaveTwo,
    waveNeg triadWaveZero, waveNeg triadWaveOne, waveNeg triadWaveTwo]

/-- Real-even Fourier amplitudes on the signed support.  Opposite modes carry
the same rational amplitude. -/
def signedRealitySlice (state : TriadState) : SignedTriadState :=
  ![state 0, state 1, state 2, state 0, state 1, state 2]

/-- Ordered coefficient in the Fourier vorticity nonlinearity

`-((p × q) / |p|²) ωₚ ω_q`.
-/
def orderedVorticityInteractionCoefficient
    (advecting transported : WaveVector) : ℚ :=
  -(waveDet advecting transported : ℚ) /
    (waveNormSq advecting : ℚ)

/-- Full ordered convolution on the six-mode Galerkin support. -/
def signedVorticityConvolution
    (state : TriadState) (output : Fin 6) : ℚ :=
  ∑ advecting : Fin 6, ∑ transported : Fin 6,
    if waveAdd (signedTriadWave advecting)
          (signedTriadWave transported) =
        signedTriadWave output
    then
      orderedVorticityInteractionCoefficient
          (signedTriadWave advecting)
          (signedTriadWave transported) *
        signedRealitySlice state advecting *
        signedRealitySlice state transported
    else 0

/-- Positive retained coordinates of the actual six-mode convolution. -/
def triadNonlinearGenerator (state : TriadState) : TriadState :=
  ![signedVorticityConvolution state 0,
    signedVorticityConvolution state 1,
    signedVorticityConvolution state 2]

/-! ## Machine reduction of the complete convolution -/

theorem signedVorticityConvolution_mode_zero
    (state : TriadState) :
    signedVorticityConvolution state 0 =
      (-3 / 10 : ℚ) * state 1 * state 2 := by
  simp [signedVorticityConvolution, Fin.sum_univ_six,
    signedTriadWave, signedRealitySlice,
    orderedVorticityInteractionCoefficient, waveAdd, waveNeg,
    waveDet, waveNormSq, triadWaveZero, triadWaveOne, triadWaveTwo]
  ring

theorem signedVorticityConvolution_mode_one
    (state : TriadState) :
    signedVorticityConvolution state 1 =
      (4 / 5 : ℚ) * state 2 * state 0 := by
  simp [signedVorticityConvolution, Fin.sum_univ_six,
    signedTriadWave, signedRealitySlice,
    orderedVorticityInteractionCoefficient, waveAdd, waveNeg,
    waveDet, waveNormSq, triadWaveZero, triadWaveOne, triadWaveTwo]
  ring

theorem signedVorticityConvolution_mode_two
    (state : TriadState) :
    signedVorticityConvolution state 2 =
      (-1 / 2 : ℚ) * state 0 * state 1 := by
  simp [signedVorticityConvolution, Fin.sum_univ_six,
    signedTriadWave, signedRealitySlice,
    orderedVorticityInteractionCoefficient, waveAdd, waveNeg,
    waveDet, waveNormSq, triadWaveZero, triadWaveOne, triadWaveTwo]
  ring

theorem signedVorticityConvolution_reality_zero
    (state : TriadState) :
    signedVorticityConvolution state 3 =
      signedVorticityConvolution state 0 := by
  simp [signedVorticityConvolution, Fin.sum_univ_six,
    signedTriadWave, signedRealitySlice,
    orderedVorticityInteractionCoefficient, waveAdd, waveNeg,
    waveDet, waveNormSq, triadWaveZero, triadWaveOne, triadWaveTwo]

theorem signedVorticityConvolution_reality_one
    (state : TriadState) :
    signedVorticityConvolution state 4 =
      signedVorticityConvolution state 1 := by
  simp [signedVorticityConvolution, Fin.sum_univ_six,
    signedTriadWave, signedRealitySlice,
    orderedVorticityInteractionCoefficient, waveAdd, waveNeg,
    waveDet, waveNormSq, triadWaveZero, triadWaveOne, triadWaveTwo]

theorem signedVorticityConvolution_reality_two
    (state : TriadState) :
    signedVorticityConvolution state 5 =
      signedVorticityConvolution state 2 := by
  simp [signedVorticityConvolution, Fin.sum_univ_six,
    signedTriadWave, signedRealitySlice,
    orderedVorticityInteractionCoefficient, waveAdd, waveNeg,
    waveDet, waveNormSq, triadWaveZero, triadWaveOne, triadWaveTwo]

theorem triadNonlinearGenerator_coordinates
    (state : TriadState) :
    triadNonlinearGenerator state =
      ![(-3 / 10 : ℚ) * state 1 * state 2,
        (4 / 5 : ℚ) * state 2 * state 0,
        (-1 / 2 : ℚ) * state 0 * state 1] := by
  funext mode
  fin_cases mode
  · exact signedVorticityConvolution_mode_zero state
  · exact signedVorticityConvolution_mode_one state
  · exact signedVorticityConvolution_mode_two state

/-! ## Incompressible velocity readout and viscous Galerkin tangent -/

/-- Biot--Savart velocity coefficient `ωₖ k⊥ / |k|²`. -/
def vorticityToVelocityCoefficient
    (wave : WaveVector) (amplitude : ℚ) : ℚ × ℚ :=
  (amplitude * (-(wave.2 : ℚ)) / (waveNormSq wave : ℚ),
    amplitude * (wave.1 : ℚ) / (waveNormSq wave : ℚ))

def waveVelocityDot
    (wave : WaveVector) (velocity : ℚ × ℚ) : ℚ :=
  (wave.1 : ℚ) * velocity.1 + (wave.2 : ℚ) * velocity.2

/-- Every retained mode is divergence-free before any special source is
selected. -/
theorem vorticityToVelocityCoefficient_divergenceFree
    (wave : WaveVector) (amplitude : ℚ) :
    waveVelocityDot wave
      (vorticityToVelocityCoefficient wave amplitude) = 0 := by
  simp [waveVelocityDot, vorticityToVelocityCoefficient]
  ring

/-- Diagonal viscous vorticity tangent `-ν |k|² ωₖ`. -/
def triadViscousGenerator
    (ν : ℚ) (state : TriadState) : TriadState :=
  ![-ν * state 0, -(2 * ν) * state 1, -(5 * ν) * state 2]

/-- Actual Navier--Stokes Galerkin tangent on the retained reality slice. -/
def triadNavierStokesGalerkinGenerator
    (ν : ℚ) (state : TriadState) : TriadState :=
  triadNonlinearGenerator state + triadViscousGenerator ν state

/-- Canonical source used later to generate a positive cross-scale flux. -/
def canonicalTriadSource : TriadState :=
  ![1, 1, -1]

@[simp] theorem canonicalTriadSource_zero :
    canonicalTriadSource 0 = 1 := by rfl

@[simp] theorem canonicalTriadSource_one :
    canonicalTriadSource 1 = 1 := by rfl

@[simp] theorem canonicalTriadSource_two :
    canonicalTriadSource 2 = -1 := by rfl

/-- Zero high mode is retained as a negative control. -/
def zeroHighTriadSource : TriadState :=
  ![1, 1, 0]

@[simp] theorem zeroHighTriadSource_zero :
    zeroHighTriadSource 0 = 1 := by rfl

@[simp] theorem zeroHighTriadSource_one :
    zeroHighTriadSource 1 = 1 := by rfl

@[simp] theorem zeroHighTriadSource_two :
    zeroHighTriadSource 2 = 0 := by rfl

/-- Mirroring the high-mode sign reverses the nonlinear transfer. -/
def backscatterTriadSource : TriadState :=
  ![1, 1, 1]

@[simp] theorem backscatterTriadSource_zero :
    backscatterTriadSource 0 = 1 := by rfl

@[simp] theorem backscatterTriadSource_one :
    backscatterTriadSource 1 = 1 := by rfl

@[simp] theorem backscatterTriadSource_two :
    backscatterTriadSource 2 = 1 := by rfl

end TwoDimensionalVorticityTriadActual
end SaturationMonoid.NavierStokes
