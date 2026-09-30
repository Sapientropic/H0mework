import H0mework.NavierStokes.FiniteVorticity.TriadActual

/-!
# An actual two-scale Fourier--Galerkin vorticity chain

The isolated three-mode triad has only one nontrivial adjacent sharp-filter
commutator.  This module enlarges the retained reality slice to

```text
± {(1, 0), (1, 1), (2, 1), (3, 1)}.
```

The two exact resonances

```text
k₀ + k₁ = k₂,
k₀ + k₂ = k₃
```

cross the squared-norm thresholds

```text
{1, 2} ⊂ {1, 2, 5} ⊂ {1, 2, 5, 10}.
```

As in the one-triad producer, the nonlinear vector field is computed from
the complete ordered Fourier-vorticity convolution, now on all `8 × 8`
signed pairs.  No interaction coefficient or desired flux is supplied as a
premise.
-/

namespace SaturationMonoid.NavierStokes
namespace TwoDimensionalVorticityDoubleTriadActual

open scoped BigOperators

open TwoDimensionalVorticityTriadActual

abbrev DoubleTriadState := Fin 4 → ℚ
abbrev SignedDoubleTriadState := Fin 8 → ℚ

def doubleTriadWaveZero : WaveVector := (1, 0)
def doubleTriadWaveOne : WaveVector := (1, 1)
def doubleTriadWaveTwo : WaveVector := (2, 1)
def doubleTriadWaveThree : WaveVector := (3, 1)

def positiveDoubleTriadWave : Fin 4 → WaveVector :=
  ![doubleTriadWaveZero, doubleTriadWaveOne,
    doubleTriadWaveTwo, doubleTriadWaveThree]

theorem doubleTriad_first_resonance :
    waveAdd doubleTriadWaveZero doubleTriadWaveOne =
      doubleTriadWaveTwo := by
  norm_num [waveAdd, doubleTriadWaveZero,
    doubleTriadWaveOne, doubleTriadWaveTwo]

theorem doubleTriad_second_resonance :
    waveAdd doubleTriadWaveZero doubleTriadWaveTwo =
      doubleTriadWaveThree := by
  norm_num [waveAdd, doubleTriadWaveZero,
    doubleTriadWaveTwo, doubleTriadWaveThree]

@[simp] theorem doubleTriadWaveZero_normSq :
    waveNormSq doubleTriadWaveZero = 1 := by
  norm_num [waveNormSq, doubleTriadWaveZero]

@[simp] theorem doubleTriadWaveOne_normSq :
    waveNormSq doubleTriadWaveOne = 2 := by
  norm_num [waveNormSq, doubleTriadWaveOne]

@[simp] theorem doubleTriadWaveTwo_normSq :
    waveNormSq doubleTriadWaveTwo = 5 := by
  norm_num [waveNormSq, doubleTriadWaveTwo]

@[simp] theorem doubleTriadWaveThree_normSq :
    waveNormSq doubleTriadWaveThree = 10 := by
  norm_num [waveNormSq, doubleTriadWaveThree]

/-- The eight retained signed modes. -/
def signedDoubleTriadWave : Fin 8 → WaveVector :=
  ![doubleTriadWaveZero, doubleTriadWaveOne,
    doubleTriadWaveTwo, doubleTriadWaveThree,
    waveNeg doubleTriadWaveZero, waveNeg doubleTriadWaveOne,
    waveNeg doubleTriadWaveTwo, waveNeg doubleTriadWaveThree]

/-- Real-even Fourier amplitudes on the signed support. -/
def signedDoubleTriadRealitySlice
    (state : DoubleTriadState) : SignedDoubleTriadState :=
  ![state 0, state 1, state 2, state 3,
    state 0, state 1, state 2, state 3]

/-- Complete ordered convolution on the eight-mode Galerkin support. -/
def signedDoubleTriadVorticityConvolution
    (state : DoubleTriadState) (output : Fin 8) : ℚ :=
  ∑ advecting : Fin 8, ∑ transported : Fin 8,
    if waveAdd (signedDoubleTriadWave advecting)
          (signedDoubleTriadWave transported) =
        signedDoubleTriadWave output
    then
      orderedVorticityInteractionCoefficient
          (signedDoubleTriadWave advecting)
          (signedDoubleTriadWave transported) *
        signedDoubleTriadRealitySlice state advecting *
        signedDoubleTriadRealitySlice state transported
    else 0

/-- Positive retained coordinates of the complete signed convolution. -/
def doubleTriadNonlinearGenerator
    (state : DoubleTriadState) : DoubleTriadState :=
  ![signedDoubleTriadVorticityConvolution state 0,
    signedDoubleTriadVorticityConvolution state 1,
    signedDoubleTriadVorticityConvolution state 2,
    signedDoubleTriadVorticityConvolution state 3]

/-! ## Machine reduction of the complete convolution -/

theorem signedDoubleTriadVorticityConvolution_mode_zero
    (state : DoubleTriadState) :
    signedDoubleTriadVorticityConvolution state 0 =
      (-3 / 10 : ℚ) * state 1 * state 2 +
        (-1 / 10 : ℚ) * state 2 * state 3 := by
  simp [signedDoubleTriadVorticityConvolution, Fin.sum_univ_eight,
    signedDoubleTriadWave, signedDoubleTriadRealitySlice,
    orderedVorticityInteractionCoefficient, waveAdd, waveNeg,
    waveDet, waveNormSq, doubleTriadWaveZero, doubleTriadWaveOne,
    doubleTriadWaveTwo, doubleTriadWaveThree]
  ring

theorem signedDoubleTriadVorticityConvolution_mode_one
    (state : DoubleTriadState) :
    signedDoubleTriadVorticityConvolution state 1 =
      (4 / 5 : ℚ) * state 0 * state 2 := by
  simp [signedDoubleTriadVorticityConvolution, Fin.sum_univ_eight,
    signedDoubleTriadWave, signedDoubleTriadRealitySlice,
    orderedVorticityInteractionCoefficient, waveAdd, waveNeg,
    waveDet, waveNormSq, doubleTriadWaveZero, doubleTriadWaveOne,
    doubleTriadWaveTwo, doubleTriadWaveThree]
  ring

theorem signedDoubleTriadVorticityConvolution_mode_two
    (state : DoubleTriadState) :
    signedDoubleTriadVorticityConvolution state 2 =
      (-1 / 2 : ℚ) * state 0 * state 1 +
        (9 / 10 : ℚ) * state 0 * state 3 := by
  simp [signedDoubleTriadVorticityConvolution, Fin.sum_univ_eight,
    signedDoubleTriadWave, signedDoubleTriadRealitySlice,
    orderedVorticityInteractionCoefficient, waveAdd, waveNeg,
    waveDet, waveNormSq, doubleTriadWaveZero, doubleTriadWaveOne,
    doubleTriadWaveTwo, doubleTriadWaveThree]
  ring

theorem signedDoubleTriadVorticityConvolution_mode_three
    (state : DoubleTriadState) :
    signedDoubleTriadVorticityConvolution state 3 =
      (-4 / 5 : ℚ) * state 0 * state 2 := by
  simp [signedDoubleTriadVorticityConvolution, Fin.sum_univ_eight,
    signedDoubleTriadWave, signedDoubleTriadRealitySlice,
    orderedVorticityInteractionCoefficient, waveAdd, waveNeg,
    waveDet, waveNormSq, doubleTriadWaveZero, doubleTriadWaveOne,
    doubleTriadWaveTwo, doubleTriadWaveThree]
  ring

theorem doubleTriadNonlinearGenerator_coordinates
    (state : DoubleTriadState) :
    doubleTriadNonlinearGenerator state =
      ![(-3 / 10 : ℚ) * state 1 * state 2 +
          (-1 / 10 : ℚ) * state 2 * state 3,
        (4 / 5 : ℚ) * state 0 * state 2,
        (-1 / 2 : ℚ) * state 0 * state 1 +
          (9 / 10 : ℚ) * state 0 * state 3,
        (-4 / 5 : ℚ) * state 0 * state 2] := by
  funext mode
  fin_cases mode
  · exact signedDoubleTriadVorticityConvolution_mode_zero state
  · exact signedDoubleTriadVorticityConvolution_mode_one state
  · exact signedDoubleTriadVorticityConvolution_mode_two state
  · exact signedDoubleTriadVorticityConvolution_mode_three state

theorem signedDoubleTriadVorticityConvolution_reality_zero
    (state : DoubleTriadState) :
    signedDoubleTriadVorticityConvolution state 4 =
      signedDoubleTriadVorticityConvolution state 0 := by
  simp [signedDoubleTriadVorticityConvolution, Fin.sum_univ_eight,
    signedDoubleTriadWave, signedDoubleTriadRealitySlice,
    orderedVorticityInteractionCoefficient, waveAdd, waveNeg,
    waveDet, waveNormSq, doubleTriadWaveZero, doubleTriadWaveOne,
    doubleTriadWaveTwo, doubleTriadWaveThree]
  ring

theorem signedDoubleTriadVorticityConvolution_reality_one
    (state : DoubleTriadState) :
    signedDoubleTriadVorticityConvolution state 5 =
      signedDoubleTriadVorticityConvolution state 1 := by
  simp [signedDoubleTriadVorticityConvolution, Fin.sum_univ_eight,
    signedDoubleTriadWave, signedDoubleTriadRealitySlice,
    orderedVorticityInteractionCoefficient, waveAdd, waveNeg,
    waveDet, waveNormSq, doubleTriadWaveZero, doubleTriadWaveOne,
    doubleTriadWaveTwo, doubleTriadWaveThree]
  ring

theorem signedDoubleTriadVorticityConvolution_reality_two
    (state : DoubleTriadState) :
    signedDoubleTriadVorticityConvolution state 6 =
      signedDoubleTriadVorticityConvolution state 2 := by
  simp [signedDoubleTriadVorticityConvolution, Fin.sum_univ_eight,
    signedDoubleTriadWave, signedDoubleTriadRealitySlice,
    orderedVorticityInteractionCoefficient, waveAdd, waveNeg,
    waveDet, waveNormSq, doubleTriadWaveZero, doubleTriadWaveOne,
    doubleTriadWaveTwo, doubleTriadWaveThree]
  ring

theorem signedDoubleTriadVorticityConvolution_reality_three
    (state : DoubleTriadState) :
    signedDoubleTriadVorticityConvolution state 7 =
      signedDoubleTriadVorticityConvolution state 3 := by
  simp [signedDoubleTriadVorticityConvolution, Fin.sum_univ_eight,
    signedDoubleTriadWave, signedDoubleTriadRealitySlice,
    orderedVorticityInteractionCoefficient, waveAdd, waveNeg,
    waveDet, waveNormSq, doubleTriadWaveZero, doubleTriadWaveOne,
    doubleTriadWaveTwo, doubleTriadWaveThree]

/-! ## Viscous Galerkin tangent and fixed source -/

/-- Diagonal viscous tangent `-ν |k|² ωₖ`. -/
def doubleTriadViscousGenerator
    (ν : ℚ) (state : DoubleTriadState) : DoubleTriadState :=
  ![-ν * state 0, -(2 * ν) * state 1,
    -(5 * ν) * state 2, -(10 * ν) * state 3]

/-- Actual Navier--Stokes Galerkin tangent on the connected two-triad
reality slice. -/
def doubleTriadNavierStokesGalerkinGenerator
    (ν : ℚ) (state : DoubleTriadState) : DoubleTriadState :=
  doubleTriadNonlinearGenerator state +
    doubleTriadViscousGenerator ν state

/-- Fixed source at which both adjacent scale fluxes will be generated
without a sign or nonzero premise. -/
def canonicalDoubleTriadSource : DoubleTriadState :=
  ![1, 1, -1, 1 / 2]

@[simp] theorem canonicalDoubleTriadSource_zero :
    canonicalDoubleTriadSource 0 = 1 := by rfl

@[simp] theorem canonicalDoubleTriadSource_one :
    canonicalDoubleTriadSource 1 = 1 := by rfl

@[simp] theorem canonicalDoubleTriadSource_two :
    canonicalDoubleTriadSource 2 = -1 := by rfl

@[simp] theorem canonicalDoubleTriadSource_three :
    canonicalDoubleTriadSource 3 = 1 / 2 := by rfl

/-- Removing the outer mode is a control for the second adjacent flux. -/
def zeroOuterDoubleTriadSource : DoubleTriadState :=
  ![1, 1, -1, 0]

@[simp] theorem zeroOuterDoubleTriadSource_zero :
    zeroOuterDoubleTriadSource 0 = 1 := by rfl

@[simp] theorem zeroOuterDoubleTriadSource_one :
    zeroOuterDoubleTriadSource 1 = 1 := by rfl

@[simp] theorem zeroOuterDoubleTriadSource_two :
    zeroOuterDoubleTriadSource 2 = -1 := by rfl

@[simp] theorem zeroOuterDoubleTriadSource_three :
    zeroOuterDoubleTriadSource 3 = 0 := by rfl

/-- Removing the middle amplitude silences both energy-flux readouts.  The
upper commutator can still create a middle-mode tangent, so this is not a
zero-trace control. -/
def zeroMiddleDoubleTriadSource : DoubleTriadState :=
  ![1, 1, 0, 1 / 2]

@[simp] theorem zeroMiddleDoubleTriadSource_zero :
    zeroMiddleDoubleTriadSource 0 = 1 := by rfl

@[simp] theorem zeroMiddleDoubleTriadSource_one :
    zeroMiddleDoubleTriadSource 1 = 1 := by rfl

@[simp] theorem zeroMiddleDoubleTriadSource_two :
    zeroMiddleDoubleTriadSource 2 = 0 := by rfl

@[simp] theorem zeroMiddleDoubleTriadSource_three :
    zeroMiddleDoubleTriadSource 3 = 1 / 2 := by rfl

/-- Reversing only the outer amplitude reverses the upper adjacent flux. -/
def backscatterOuterDoubleTriadSource : DoubleTriadState :=
  ![1, 1, -1, -1 / 2]

@[simp] theorem backscatterOuterDoubleTriadSource_zero :
    backscatterOuterDoubleTriadSource 0 = 1 := by rfl

@[simp] theorem backscatterOuterDoubleTriadSource_one :
    backscatterOuterDoubleTriadSource 1 = 1 := by rfl

@[simp] theorem backscatterOuterDoubleTriadSource_two :
    backscatterOuterDoubleTriadSource 2 = -1 := by rfl

@[simp] theorem backscatterOuterDoubleTriadSource_three :
    backscatterOuterDoubleTriadSource 3 = -1 / 2 := by rfl

/-- Reversing the second low amplitude reverses the middle adjacent flux. -/
def backscatterMiddleDoubleTriadSource : DoubleTriadState :=
  ![1, -1, -1, 1 / 2]

@[simp] theorem backscatterMiddleDoubleTriadSource_zero :
    backscatterMiddleDoubleTriadSource 0 = 1 := by rfl

@[simp] theorem backscatterMiddleDoubleTriadSource_one :
    backscatterMiddleDoubleTriadSource 1 = -1 := by rfl

@[simp] theorem backscatterMiddleDoubleTriadSource_two :
    backscatterMiddleDoubleTriadSource 2 = -1 := by rfl

@[simp] theorem backscatterMiddleDoubleTriadSource_three :
    backscatterMiddleDoubleTriadSource 3 = 1 / 2 := by rfl

end TwoDimensionalVorticityDoubleTriadActual
end SaturationMonoid.NavierStokes
