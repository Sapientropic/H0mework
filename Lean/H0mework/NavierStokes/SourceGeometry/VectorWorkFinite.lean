import H0mework.NavierStokes.SourceGeometry.VectorWorkReadout
import H0mework.NavierStokes.SourceGeometry.VectorWorkHolder

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceFieldRenewal

open MeasureTheory
open scoped Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicUnitCellDivergence
open ThreeDimensionalPeriodicFullVorticityStretching
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFinitePhysicalStateRestart
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientClosedEnstrophyPhysicalBridge

noncomputable section

variable (modes : Finset IntegerWavevector) (zeroNotMem : 0 ∉ modes)
  (negClosed : ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
  (state : ComplexVorticityHilbertState)
  (supported : ∀ wave, wave ∉ modes → state wave = 0)
  (transverse : ∀ wave ∈ modes, complexWavevector wave ⬝ᵥ state wave = 0)
  (reality : FiniteStateFourierReality state)

include zeroNotMem negClosed supported transverse reality

theorem finite_work_abs_le_velocity_sup (U : ℝ)
    (uBound : ∀ x, ‖finiteStateVelocityRealPartField modes state x‖ ≤ U) :
    |finiteStateVorticityStretchingWork modes state| ≤
      U * Real.sqrt (finiteStateVorticityCoefficientEnstrophy modes state) *
        Real.sqrt ((2 * Real.pi) ^ 2 * finiteStateVorticityEnstrophyMass modes state) := by
  let source := rawSourceOfFiniteVorticityState modes state
  have sourceBound : ∀ x, ‖physicalVelocity source x‖ ≤ U := by
    intro x
    rw [show physicalVelocity source = finiteStateVelocityRealPartField modes state from
      finiteSource_velocity_eq modes zeroNotMem negClosed state supported transverse reality]
    exact uBound x
  have holder := physicalUnitCell_transport_abs_le
    (physicalVelocity source) (physicalVorticity source)
    (physicalVelocity_contDiff source).continuous
    ((physicalVorticity_contDiff source).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) U sourceBound
  rw [← physicalUnitCell_enstrophyStretchingWork_rawFiniteSource_integral
    modes zeroNotMem negClosed state supported transverse reality]
  rw [physicalUnitCell_source_work_integral, abs_neg]
  dsimp only [source] at holder
  rw [finiteSource_vorticity_parseval modes zeroNotMem negClosed state supported transverse reality,
    finiteSource_gradient_parseval modes zeroNotMem negClosed state supported transverse reality,
    ← mul_assoc] at holder
  exact holder

theorem finite_work_sq_le_velocity_sup (U : ℝ)
    (uBound : ∀ x, ‖finiteStateVelocityRealPartField modes state x‖ ≤ U) :
    finiteStateVorticityStretchingWork modes state ^ 2 ≤
      U ^ 2 * finiteStateVorticityCoefficientEnstrophy modes state *
        ((2 * Real.pi) ^ 2 * finiteStateVorticityEnstrophyMass modes state) := by
  have U0 : 0 ≤ U := (norm_nonneg _).trans (uBound 0)
  have M0 : 0 ≤ finiteStateVorticityCoefficientEnstrophy modes state :=
    Finset.sum_nonneg (fun _ _ => complexCoordinateAmplitudeSq_nonneg _)
  have D0 : 0 ≤ (2 * Real.pi) ^ 2 * finiteStateVorticityEnstrophyMass modes state :=
    mul_nonneg (sq_nonneg _) (finiteStateVorticityEnstrophyMass_nonneg modes state)
  have h := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg
    (mul_nonneg U0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))).2
      (finite_work_abs_le_velocity_sup modes zeroNotMem negClosed state supported transverse reality U uBound)
  rw [sq_abs, mul_pow, mul_pow, Real.sq_sqrt M0, Real.sq_sqrt D0] at h
  exact h

end
end SaturationMonoid.NavierStokes.SourceFieldRenewal
