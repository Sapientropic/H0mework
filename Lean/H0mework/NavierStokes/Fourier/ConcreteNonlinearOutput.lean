import H0mework.NavierStokes.Fourier.ConcreteActiveClosedTriad
import H0mework.NavierStokes.Fourier.NonlinearPairGenerator

/-!
# Concrete complete nonlinear output fiber

The premise-free closed-triad calibration source generates six signed waves.
At the fixed output `k = p + q`, its complete ordered-pair fiber consists of
exactly `(p,q)` and `(q,p)`.  This module computes both rows and the aggregate
full-vorticity nonlinear coefficient.

The selected `(p,q)` row has zero advection and retains its stretching value
`(-1/4,0,0)`.  The reverse row contributes `(0,1/4,0)`, so the complete output
coefficient is `(-1/4,1/4,0)`: its first coordinate is the actual selected
occurrence and is not canceled by the reverse row.  Nonvanishing and the
positive norm-square quantum are conclusions.  No pair, output, nonzero fact,
or target is accepted at a theorem mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientConcreteNonlinearOutput

open scoped BigOperators Matrix

open Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientClosedEnstrophyTriad
open ThreeDimensionalVorticityCoefficientConcreteActiveClosedTriad
open ThreeDimensionalVorticityCoefficientConcreteActivePair
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable

noncomputable section

/-! ## Fixed complete output fiber -/

/-- The reverse row in the same concrete output fiber. -/
def concreteReverseStretchingPair : StretchingPair :=
  (concreteTransportedWave, concreteAdvectingWave)

@[simp] theorem concreteReverseStretchingPair_output :
    stretchingPairOutput concreteReverseStretchingPair =
      concreteStretchingOutput := by
  rw [show concreteReverseStretchingPair =
      stretchingPairSwap concreteStretchingPair by rfl,
    stretchingPairOutput_swap,
    concreteStretchingPair_output]

theorem concreteClosedTriad_generatedSupport_eq :
    generatedSupport concreteActiveClosedTriadSource =
      {concreteAdvectingWave, concreteTransportedWave,
        concreteTestingWave, waveNeg concreteAdvectingWave,
        waveNeg concreteTransportedWave, waveNeg concreteTestingWave} := by
  decide

/-- The actual complete output fiber contains precisely the selected and
reverse ordered rows; no pair is supplied by a caller. -/
theorem concreteNonlinearOutput_fiber_eq :
    generatedStretchingPairFiber concreteActiveClosedTriadSource
        concreteStretchingOutput =
      {concreteStretchingPair, concreteReverseStretchingPair} := by
  decide

/-! ## Exact row coefficients -/

theorem concreteClosedTriad_generatedVelocity_advecting :
    generatedVelocityCoefficient concreteActiveClosedTriadSource
        concreteAdvectingWave =
      ![0, 0, (Complex.I / (((4 : ℝ) * Real.pi : ℝ) : ℂ))] := by
  rw [generatedVelocityCoefficient,
    concreteClosedTriad_generatedVorticity_advecting]
  funext coordinate
  fin_cases coordinate
  all_goals
    simp [biotSavartVelocityCoefficient,
      concreteAdvectingWave, complexWavevector,
      integerWaveNormSq, cross_apply, Fin.sum_univ_succ]
  all_goals ring_nf

/-- The selected ordered row has no vorticity-advection contribution. -/
theorem concreteStretchingPair_advectionContribution :
    generatedVorticityAdvectionPairContribution
        concreteActiveClosedTriadSource concreteStretchingPair = 0 := by
  rw [generatedVorticityAdvectionPairContribution]
  simp only [concreteStretchingPair,
    concreteClosedTriad_generatedVelocity_advecting,
    concreteClosedTriad_generatedVorticity_transported]
  funext coordinate
  fin_cases coordinate <;>
    simp [concreteTransportedWave, complexWavevector,
      dotProduct, Fin.sum_univ_succ]

/-- The selected ordered nonlinear row retains the full stretching vector. -/
theorem concreteStretchingPair_nonlinearContribution :
    generatedVorticityNonlinearPairContribution
        concreteActiveClosedTriadSource concreteStretchingPair =
      ![(-1 / 4 : ℂ), 0, 0] := by
  rw [generatedVorticityNonlinearPairContribution,
    concreteStretchingPair_advectionContribution,
    sub_zero,
    concreteClosedTriadStretchingPair_contribution]

theorem concreteReverseStretchingPair_stretchingContribution :
    generatedStretchingPairContribution concreteActiveClosedTriadSource
        concreteReverseStretchingPair = 0 := by
  rw [generatedStretchingPairContribution]
  simp only [concreteReverseStretchingPair,
    concreteClosedTriad_generatedVorticity_transported,
    concreteClosedTriad_generatedVelocity_advecting]
  funext coordinate
  fin_cases coordinate <;>
    simp [concreteAdvectingWave, complexWavevector,
      dotProduct, Fin.sum_univ_succ]

theorem concreteReverseStretchingPair_advectionContribution :
    generatedVorticityAdvectionPairContribution
        concreteActiveClosedTriadSource concreteReverseStretchingPair =
      ![0, (-1 / 4 : ℂ), 0] := by
  rw [generatedVorticityAdvectionPairContribution]
  simp only [concreteReverseStretchingPair,
    concreteClosedTriad_generatedVelocity_transported,
    concreteClosedTriad_generatedVorticity_advecting]
  funext coordinate
  fin_cases coordinate
  all_goals
    simp [concreteAdvectingWave, complexWavevector,
      dotProduct, Fin.sum_univ_succ]
  all_goals field_simp [Real.pi_ne_zero]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]

theorem concreteReverseStretchingPair_nonlinearContribution :
    generatedVorticityNonlinearPairContribution
        concreteActiveClosedTriadSource concreteReverseStretchingPair =
      ![0, (1 / 4 : ℂ), 0] := by
  rw [generatedVorticityNonlinearPairContribution,
    concreteReverseStretchingPair_stretchingContribution,
    concreteReverseStretchingPair_advectionContribution]
  norm_num

/-- The reverse row cannot cancel the selected row's first coordinate. -/
theorem concreteReverseStretchingPair_nonlinearContribution_coordinate_zero :
    generatedVorticityNonlinearPairContribution
        concreteActiveClosedTriadSource concreteReverseStretchingPair 0 = 0 := by
  rw [concreteReverseStretchingPair_nonlinearContribution]
  rfl

/-! ## Complete aggregate output and quantum -/

theorem concreteNonlinearOutput_coefficient :
    generatedVorticityNonlinearCoefficientAt
        concreteActiveClosedTriadSource concreteStretchingOutput =
      ![(-1 / 4 : ℂ), (1 / 4 : ℂ), 0] := by
  rw [generatedVorticityNonlinearCoefficientAt,
    concreteNonlinearOutput_fiber_eq]
  have pairNotMem :
      concreteStretchingPair ∉
        ({concreteReverseStretchingPair} : Finset StretchingPair) := by
    decide
  rw [Finset.sum_insert pairNotMem,
    Finset.sum_singleton,
    concreteStretchingPair_nonlinearContribution,
    concreteReverseStretchingPair_nonlinearContribution]
  ext coordinate
  fin_cases coordinate <;> norm_num

/-- On the complete output fiber, coordinate zero is exactly the selected
row coordinate because the reverse row is silent there. -/
theorem concreteNonlinearOutput_coordinate_zero_eq_selectedRow :
    generatedVorticityNonlinearCoefficientAt
        concreteActiveClosedTriadSource concreteStretchingOutput 0 =
      generatedVorticityNonlinearPairContribution
        concreteActiveClosedTriadSource concreteStretchingPair 0 := by
  rw [concreteNonlinearOutput_coefficient,
    concreteStretchingPair_nonlinearContribution]
  rfl

theorem concreteNonlinearOutput_coefficient_ne_zero :
    generatedVorticityNonlinearCoefficientAt
        concreteActiveClosedTriadSource concreteStretchingOutput ≠ 0 := by
  rw [concreteNonlinearOutput_coefficient]
  intro equality
  have := congrFun equality 0
  norm_num at this

/-- Squared coordinate norm of the complete generated output coefficient. -/
def concreteNonlinearOutputQuantum : ℝ :=
  complexCoordinateVectorNormSq
    (generatedVorticityNonlinearCoefficientAt
      concreteActiveClosedTriadSource concreteStretchingOutput)

theorem concreteNonlinearOutput_quantum :
    concreteNonlinearOutputQuantum = 1 / 8 := by
  rw [concreteNonlinearOutputQuantum,
    concreteNonlinearOutput_coefficient]
  norm_num [complexCoordinateVectorNormSq, Complex.normSq,
    Fin.sum_univ_succ]

theorem concreteNonlinearOutput_quantum_pos :
    0 < concreteNonlinearOutputQuantum := by
  rw [concreteNonlinearOutput_quantum]
  norm_num

end

end ThreeDimensionalVorticityCoefficientConcreteNonlinearOutput
end NavierStokes
end SaturationMonoid
