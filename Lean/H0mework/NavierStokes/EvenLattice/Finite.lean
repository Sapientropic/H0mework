import H0mework.NavierStokes.SourceGeometry.VectorWorkEvaluation
import H0mework.NavierStokes.SourceGeometry.VectorWorkFinite
import H0mework.NavierStokes.EvenLattice.Bound

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceFieldRenewal

open scoped Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance

noncomputable section

theorem finite_even_velocity_sq_le (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes) (even : ∀ k ∈ modes, 2 ∣ k 0)
    (state : ComplexVorticityHilbertState) (x : PhysicalSpace) :
    ‖finiteStateVelocityRealPartField modes state x‖ ^ 2 ≤
      (63 / (8 * (2 * Real.pi) ^ 2)) * finiteStateVorticityEnstrophyMass modes state := by
  have h := finite_velocity_norm_sq_le_of_testGram modes zeroNotMem state (63 / 8)
    (by norm_num) (fun a => by simpa only [testGramRow] using EvenGram.finite_quadratic_le modes even a) x
  convert h using 1
  ring

theorem finite_even_work_sq_le (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes) (negClosed : ∀ k ∈ modes, waveNeg k ∈ modes)
    (even : ∀ k ∈ modes, 2 ∣ k 0) (state : ComplexVorticityHilbertState)
    (supported : ∀ k, k ∉ modes → state k = 0)
    (transverse : ∀ k ∈ modes, complexWavevector k ⬝ᵥ state k = 0)
    (reality : FiniteStateFourierReality state) :
    finiteStateVorticityStretchingWork modes state ^ 2 ≤
      (63 / 8) * finiteStateVorticityCoefficientEnstrophy modes state *
        finiteStateVorticityEnstrophyMass modes state ^ 2 := by
  let U := Real.sqrt ((63 / (8 * (2 * Real.pi) ^ 2)) *
    finiteStateVorticityEnstrophyMass modes state)
  have bound := finite_work_sq_le_velocity_sup modes zeroNotMem negClosed state supported transverse reality U
    (fun x => Real.le_sqrt_of_sq_le (finite_even_velocity_sq_le modes zeroNotMem even state x))
  have nonneg : 0 ≤ (63 / (8 * (2 * Real.pi) ^ 2)) *
      finiteStateVorticityEnstrophyMass modes state :=
    mul_nonneg (by positivity) (finiteStateVorticityEnstrophyMass_nonneg modes state)
  dsimp only [U] at bound
  rw [Real.sq_sqrt nonneg] at bound
  convert bound using 1
  field_simp [Real.pi_ne_zero]

end
end SaturationMonoid.NavierStokes.SourceFieldRenewal
