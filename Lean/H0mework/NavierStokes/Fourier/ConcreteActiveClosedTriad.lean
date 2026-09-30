import H0mework.NavierStokes.Energy.ClosedEnstrophyTriad
import H0mework.NavierStokes.Fourier.ConcreteActivePair

/-!
# A concrete source-generated active closed enstrophy triad

This module extends the fixed active stretching-pair calibration by one raw
testing-vorticity mode.  Its three primitive waves are

```text
p = ( 1,  0, 0),
q = ( 0,  1, 0),
r = (-1, -1, 0).
```

The raw source mouth contains only this finite inventory and its unconstrained
coefficient table.  Reality symmetrization, transverse projection,
Biot--Savart inversion, the complete ordered-pair inventory, and closed-triad
filtering remain source-generated.

For the generated occurrence `(r, (p, q))`, the source produces

```text
omega_r = (1/2, -1/2, 0),
B_(p,q) = (-1/4, 0, 0),
omega_r dot B_(p,q) = -1/8.
```

Thus the occurrence is active, escapes its exact coordinate-observer kernel,
and carries squared-magnitude quantum `1/64`.  The module deliberately makes
no claim that this coordinate survives the downstream total zero-frequency
sum.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientConcreteActiveClosedTriad

open Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientClosedEnstrophyTriad
open ThreeDimensionalVorticityCoefficientConcreteActivePair

noncomputable section

/-! ## Premise-free concrete raw source -/

/-- The testing-vorticity wave `r = -(p + q)`. -/
def concreteTestingWave : IntegerWavevector :=
  ![-1, -1, 0]

/-- A raw coefficient already transverse to the testing wave. -/
def concreteTestingRawVorticity : ComplexCoordinateVector :=
  ![1, -1, 0]

/-- The unconstrained raw coefficient table for the closed-triad calibration. -/
def concreteClosedTriadRawVorticity
    (wave : IntegerWavevector) : ComplexCoordinateVector :=
  if wave = concreteAdvectingWave then
    concreteAdvectingRawVorticity
  else if wave = concreteTransportedWave then
    concreteTransportedRawVorticity
  else if wave = concreteTestingWave then
    concreteTestingRawVorticity
  else 0

/--
The source stores no closure witness, selected triad, nonvanishing fact, or
observer target.  Those are generated below from its raw finite table.
-/
def concreteActiveClosedTriadSource : RawVorticityFourierSource where
  activeModes :=
    {concreteAdvectingWave, concreteTransportedWave, concreteTestingWave}
  rawVorticity := concreteClosedTriadRawVorticity

/-- The fixed triple later found in the complete generated inventory. -/
def concreteClosedEnstrophyTriad : EnstrophyTriad :=
  (concreteTestingWave, concreteStretchingPair)

@[simp] theorem concreteTestingWave_ne_zero :
    concreteTestingWave ≠ 0 := by
  intro equality
  have := congrFun equality 0
  norm_num [concreteTestingWave] at this

@[simp] theorem concreteAdvectingWave_mem_closedTriadSupport :
    concreteAdvectingWave ∈
        generatedSupport concreteActiveClosedTriadSource := by
  simp [generatedSupport, concreteActiveClosedTriadSource,
    concreteAdvectingWave, concreteTransportedWave,
    concreteTestingWave]

@[simp] theorem concreteTransportedWave_mem_closedTriadSupport :
    concreteTransportedWave ∈
        generatedSupport concreteActiveClosedTriadSource := by
  simp [generatedSupport, concreteActiveClosedTriadSource,
    concreteAdvectingWave, concreteTransportedWave,
    concreteTestingWave]

@[simp] theorem concreteTestingWave_mem_closedTriadSupport :
    concreteTestingWave ∈
        generatedSupport concreteActiveClosedTriadSource := by
  simp [generatedSupport, concreteActiveClosedTriadSource,
    concreteAdvectingWave, concreteTransportedWave,
    concreteTestingWave]

/-! ## Exact source-generated coefficients -/

theorem concreteClosedTriad_generatedVorticity_advecting :
    generatedVorticityCoefficient concreteActiveClosedTriadSource
        concreteAdvectingWave =
      ![0, (1 / 2 : ℂ), 0] := by
  rw [generatedVorticityCoefficient,
    if_pos concreteAdvectingWave_mem_closedTriadSupport]
  funext coordinate
  fin_cases coordinate <;>
    simp [transverseProjection,
      realitySymmetrizedVorticity, supportedRawVorticity,
      concreteActiveClosedTriadSource, concreteClosedTriadRawVorticity,
      concreteAdvectingRawVorticity,
      concreteAdvectingWave, concreteTransportedWave,
      concreteTestingWave, waveNeg, complexWavevector,
      integerWaveNormSq, dotProduct, Fin.sum_univ_succ]

theorem concreteClosedTriad_generatedVorticity_transported :
    generatedVorticityCoefficient concreteActiveClosedTriadSource
        concreteTransportedWave =
      ![0, 0, (1 / 2 : ℂ)] := by
  rw [generatedVorticityCoefficient,
    if_pos concreteTransportedWave_mem_closedTriadSupport]
  funext coordinate
  fin_cases coordinate <;>
    simp [transverseProjection,
      realitySymmetrizedVorticity, supportedRawVorticity,
      concreteActiveClosedTriadSource, concreteClosedTriadRawVorticity,
      concreteTransportedRawVorticity,
      concreteAdvectingWave, concreteTransportedWave,
      concreteTestingWave, waveNeg, complexWavevector,
      integerWaveNormSq, dotProduct, Fin.sum_univ_succ]

theorem concreteClosedTriad_generatedVorticity_testing :
    generatedVorticityCoefficient concreteActiveClosedTriadSource
        concreteTestingWave =
      ![(1 / 2 : ℂ), -1 / 2, 0] := by
  rw [generatedVorticityCoefficient,
    if_pos concreteTestingWave_mem_closedTriadSupport]
  funext coordinate
  fin_cases coordinate <;>
    simp [transverseProjection,
      realitySymmetrizedVorticity, supportedRawVorticity,
      concreteActiveClosedTriadSource, concreteClosedTriadRawVorticity,
      concreteTestingRawVorticity,
      concreteAdvectingWave, concreteTransportedWave,
      concreteTestingWave, waveNeg, complexWavevector,
      integerWaveNormSq, dotProduct, Fin.sum_univ_succ] <;>
    norm_num

theorem concreteClosedTriad_generatedVelocity_transported :
    generatedVelocityCoefficient concreteActiveClosedTriadSource
        concreteTransportedWave =
      ![(Complex.I / (((4 : ℝ) * Real.pi : ℝ) : ℂ)), 0, 0] := by
  rw [generatedVelocityCoefficient,
    concreteClosedTriad_generatedVorticity_transported]
  funext coordinate
  fin_cases coordinate
  all_goals
    simp [biotSavartVelocityCoefficient,
      concreteTransportedWave, complexWavevector,
      integerWaveNormSq, cross_apply, Fin.sum_univ_succ]
  all_goals ring_nf

/-! ## Generated closed occurrence and exact quantum -/

@[simp] theorem concreteClosedTriadStretchingPair_mem_generatedTable :
    concreteStretchingPair ∈
        generatedStretchingPairTable concreteActiveClosedTriadSource := by
  rw [mem_generatedStretchingPairTable_iff]
  exact
    And.intro concreteAdvectingWave_mem_closedTriadSupport
      concreteTransportedWave_mem_closedTriadSupport

theorem concreteClosedTriadStretchingPair_contribution :
    generatedStretchingPairContribution concreteActiveClosedTriadSource
        concreteStretchingPair =
      ![(-1 / 4 : ℂ), 0, 0] := by
  simp only [concreteStretchingPair]
  rw [generatedStretchingPairContribution,
    concreteClosedTriad_generatedVorticity_advecting,
    concreteClosedTriad_generatedVelocity_transported]
  funext coordinate
  fin_cases coordinate
  all_goals
    simp [concreteTransportedWave, complexWavevector, dotProduct,
      Fin.sum_univ_succ]
  all_goals field_simp [Real.pi_ne_zero]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]

@[simp] theorem concreteClosedEnstrophyTriad_mem_inventory :
    concreteClosedEnstrophyTriad ∈
        generatedClosedEnstrophyTriadInventory
          concreteActiveClosedTriadSource := by
  rw [mem_generatedClosedEnstrophyTriadInventory_iff]
  refine And.intro concreteTestingWave_mem_closedTriadSupport ?_
  refine And.intro concreteAdvectingWave_mem_closedTriadSupport ?_
  refine And.intro concreteTransportedWave_mem_closedTriadSupport ?_
  funext coordinate
  fin_cases coordinate <;>
    norm_num [concreteClosedEnstrophyTriad, concreteStretchingPair,
      concreteTestingWave, concreteAdvectingWave,
      concreteTransportedWave]

theorem concreteClosedEnstrophyTriad_contribution :
    closedEnstrophyTriadContribution concreteActiveClosedTriadSource
        concreteClosedEnstrophyTriad =
      (-1 / 8 : ℂ) := by
  simp only [concreteClosedEnstrophyTriad]
  rw [closedEnstrophyTriadContribution,
    concreteClosedTriad_generatedVorticity_testing,
    concreteClosedTriadStretchingPair_contribution]
  norm_num [dotProduct, Fin.sum_univ_succ]

theorem concreteClosedEnstrophyTriad_contribution_ne_zero :
    closedEnstrophyTriadContribution concreteActiveClosedTriadSource
        concreteClosedEnstrophyTriad ≠ 0 := by
  rw [concreteClosedEnstrophyTriad_contribution]
  norm_num

/-- The exact generated occurrence retains the source inventory proof. -/
def concreteGeneratedClosedEnstrophyTriadOccurrence :
    GeneratedClosedEnstrophyTriadOccurrence
      concreteActiveClosedTriadSource :=
  Subtype.mk concreteClosedEnstrophyTriad
    concreteClosedEnstrophyTriad_mem_inventory

@[simp] theorem concreteGeneratedClosedEnstrophyTriadOccurrence_triad :
    concreteGeneratedClosedEnstrophyTriadOccurrence.1 =
      concreteClosedEnstrophyTriad :=
  rfl

theorem concreteGeneratedClosedEnstrophyTriadOccurrence_coordinate :
    closedEnstrophyTriadCoordinateObserver
        concreteActiveClosedTriadSource
        concreteGeneratedClosedEnstrophyTriadOccurrence
        (generatedClosedEnstrophyTriadFrame
          concreteActiveClosedTriadSource) =
      (-1 / 8 : ℂ) := by
  rw [closedEnstrophyTriadCoordinateObserver_generatedFrame,
    concreteGeneratedClosedEnstrophyTriadOccurrence_triad,
    concreteClosedEnstrophyTriad_contribution]

@[simp] theorem concreteGeneratedClosedEnstrophyTriadOccurrence_mem_active :
    concreteGeneratedClosedEnstrophyTriadOccurrence ∈
        activeClosedEnstrophyTriadOccurrences
          concreteActiveClosedTriadSource := by
  rw [mem_activeClosedEnstrophyTriadOccurrences_iff]
  change
    closedEnstrophyTriadContribution concreteActiveClosedTriadSource
        concreteClosedEnstrophyTriad ≠ 0
  exact concreteClosedEnstrophyTriad_contribution_ne_zero

/--
The source-generated active occurrence.  No occurrence or nonzero evidence is
accepted from a caller.
-/
def concreteActiveClosedEnstrophyTriadOccurrence :
    ActiveClosedEnstrophyTriadOccurrence
      concreteActiveClosedTriadSource :=
  Subtype.mk concreteGeneratedClosedEnstrophyTriadOccurrence
    concreteGeneratedClosedEnstrophyTriadOccurrence_mem_active

@[simp] theorem concreteActiveClosedEnstrophyTriadOccurrence_generated :
    concreteActiveClosedEnstrophyTriadOccurrence.1 =
      concreteGeneratedClosedEnstrophyTriadOccurrence :=
  rfl

theorem concreteActiveClosedEnstrophyTriadOccurrence_quantum :
    activeClosedEnstrophyTriadQuantum concreteActiveClosedTriadSource
        concreteActiveClosedEnstrophyTriadOccurrence = 1 / 64 := by
  rw [activeClosedEnstrophyTriadQuantum]
  change Complex.normSq
    (closedEnstrophyTriadContribution concreteActiveClosedTriadSource
      concreteClosedEnstrophyTriad) = 1 / 64
  rw [concreteClosedEnstrophyTriad_contribution]
  norm_num [Complex.normSq]

theorem concreteActiveClosedEnstrophyTriadOccurrence_quantum_pos :
    0 < activeClosedEnstrophyTriadQuantum concreteActiveClosedTriadSource
      concreteActiveClosedEnstrophyTriadOccurrence :=
  activeClosedEnstrophyTriadQuantum_pos _ _

/-- The actual generated frame avoids its occurrence-coordinate kernel. -/
theorem concreteActiveClosedEnstrophyTriadOccurrence_escapes_coordinateKernel :
    generatedClosedEnstrophyTriadFrame concreteActiveClosedTriadSource ∉
      LinearMap.ker
        (closedEnstrophyTriadCoordinateObserver
          concreteActiveClosedTriadSource
          concreteActiveClosedEnstrophyTriadOccurrence.1) :=
  generatedClosedEnstrophyTriadFrame_not_mem_coordinateKernel _ _

end

end ThreeDimensionalVorticityCoefficientConcreteActiveClosedTriad
end NavierStokes
end SaturationMonoid
