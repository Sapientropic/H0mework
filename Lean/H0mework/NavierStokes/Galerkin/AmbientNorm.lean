import H0mework.NavierStokes.Galerkin.EnstrophyBalance

/-!
# Ambient `ℓ²` control by finite coefficient enstrophy

The finite Galerkin ODE is solved in the common carrier
`ℓ²(ℤ³; ℂ³_sup)`, while its cutoff-independent critical barrier controls the
Euclidean coefficient enstrophy.  This file proves the missing whole-carrier
comparison.  Its constant is one and does not depend on the Fourier cutoff:
the squared sup norm of each three-coordinate row is bounded by the sum of
the three coordinate squares.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm

open scoped BigOperators ENNReal

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance

noncomputable section

/-- The ambient sup norm on a three-coordinate Fourier row is dominated by
the Euclidean coefficient amplitude, with no dimension- or cutoff-dependent
constant. -/
theorem complexCoordinateVector_norm_sq_le_amplitudeSq
    (vector : ComplexCoordinateVector) :
    ‖vector‖ ^ 2 ≤ complexCoordinateAmplitudeSq vector := by
  have amplitudeNonneg : 0 ≤ complexCoordinateAmplitudeSq vector := by
    exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have coordinateLeSqrt :
      ∀ coordinate : Coordinate,
        ‖vector coordinate‖ ≤
          Real.sqrt (complexCoordinateAmplitudeSq vector) := by
    intro coordinate
    apply Real.le_sqrt_of_sq_le
    rw [← Complex.normSq_eq_norm_sq]
    exact Finset.single_le_sum
      (fun index _ => Complex.normSq_nonneg (vector index))
      (Finset.mem_univ coordinate)
  have normLeSqrt :
      ‖vector‖ ≤ Real.sqrt (complexCoordinateAmplitudeSq vector) :=
    (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 coordinateLeSqrt
  calc
    ‖vector‖ ^ 2 ≤ (Real.sqrt (complexCoordinateAmplitudeSq vector)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 normLeSqrt
    _ = complexCoordinateAmplitudeSq vector := Real.sq_sqrt amplitudeNonneg

/-- A sharply supported finite state has ambient `ℓ²` norm squared at most
its coefficient enstrophy.  The estimate is independent of the number and
size of the retained frequencies. -/
theorem complexVorticityHilbertState_norm_sq_le_coefficientEnstrophy
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave, wave ∉ modes → state wave = 0) :
    ‖state‖ ^ 2 ≤
      finiteStateVorticityCoefficientEnstrophy modes state := by
  have ambientNormSq :
      ‖state‖ ^ 2 = ∑' wave, ‖state wave‖ ^ 2 := by
    simpa using
      (lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) state)
  rw [ambientNormSq]
  rw [tsum_eq_sum (s := modes) (fun wave waveNotMem => by
    rw [supported wave waveNotMem]
    simp)]
  unfold finiteStateVorticityCoefficientEnstrophy
  exact Finset.sum_le_sum fun wave _ =>
    complexCoordinateVector_norm_sq_le_amplitudeSq (state wave)

end

end ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
end NavierStokes
end SaturationMonoid
