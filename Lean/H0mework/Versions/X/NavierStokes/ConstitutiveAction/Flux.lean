import H0mework.Versions.X.NavierStokes.ConstitutiveAction.Color

set_option autoImplicit false
open scoped Matrix BigOperators Matrix.Norms.Elementwise

namespace SaturationMonoid.NavierStokes.NativeConstitutiveFlux

open PhysicsCore DiracExteriorMatterAction
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePauliCoframeAction NativeCartanConstitutive NativeCartanStressLaw
open NativeMatterCoframeStress NativeSourceCoframeStress

noncomputable section

def increment (velocity : PhysicalSpace) : Fin 4 → DiracExteriorMatterCarrier :=
  fun direction => NativeCartanCompensation.compensatedIncrement velocity direction +
    NativeSourceColorAction.increment velocity (NativeConstitutiveColor.coefficients velocity) direction

theorem vector_zero (velocity : PhysicalSpace) :
    gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity) (increment velocity) = 0 := by
  have split : gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity) (increment velocity) =
      gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity)
        (NativeCartanCompensation.compensatedIncrement velocity) +
      gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity)
        (NativeSourceColorAction.increment velocity (NativeConstitutiveColor.coefficients velocity)) := by
    simp only [increment, gaugeVectorAt, map_add, Finset.sum_add_distrib, smul_add]
  rw [split, NativeCartanCompensation.compensated_vector_zero,
    NativeConstitutiveColor.source_vector_zero, add_zero]

def current (velocity : PhysicalSpace) : LorentzianCoframe :=
  kineticCoefficients (NativeCanonicalFluidCoframe.dual velocity) (increment velocity)

def stress (velocity : PhysicalSpace) : LorentzianCoframe →L[ℝ] ℝ :=
  responseCovector velocity (current velocity)

theorem stress_split (velocity : PhysicalSpace) :
    stress velocity = NativeCartanStress.reactionStress velocity + NativeConstitutiveColor.stress velocity := by
  have split : current velocity = NativeCartanStress.reactionCurrent velocity +
      kineticCoefficients (NativeCanonicalFluidCoframe.dual velocity)
        (NativeSourceColorAction.increment velocity (NativeConstitutiveColor.coefficients velocity)) := by
    ext direction internal
    simp only [current, kineticCoefficients, increment, NativeCartanStress.reactionCurrent,
      map_add, smul_add, Complex.add_re, Matrix.add_apply]
  rw [stress, split, responseCovector_add]
  rfl

theorem stress_hasFDerivAt (velocity : PhysicalSpace) :
    HasFDerivAt (density (current velocity) 0) (stress velocity)
      (NativeCanonicalFluidCoframe.coframe velocity) := by
  apply density_hasFDerivAt_of_inner_zero _ _ _ (NativeCanonicalFluidCoframe.coframe_nondegenerate velocity)
  rw [add_zero, current, pairing_eq_kinetic]
  change (NativeCanonicalFluidCoframe.dual _ (gaugeVectorAt _ _)).re = 0
  rw [vector_zero, map_zero, Complex.zero_re]

def isotropicPressure (velocity : PhysicalSpace) : ℝ :=
  let s := squared (normalizedVelocity velocity)
  16 * s * (1 - s)^2 / (3 + 2 * s + 3 * s^2)

/-- The actual source-generated constitutive stress has the original negative momentum flux, modulo scalar pressure. -/
theorem stress_spatial (velocity : PhysicalSpace) (first second : Fin 3) :
    stress velocity (Matrix.single first.succ second.succ 1) =
      -(velocity first * velocity second) + isotropicPressure velocity * (if first = second then 1 else 0) := by
  rw [stress_split, add_apply, reaction_stress, NativeConstitutiveColor.stress_spatial]
  unfold NativeConstitutiveColor.correctionScale
  have nonzero := (fluxFactor_pos (normalizedVelocity velocity)).ne'
  have scale := (NativeCanonicalFluidCoframe.scale_pos velocity).ne'
  have normalize (direction : Fin 3) : velocity direction = 4 * normalizedVelocity velocity direction := by
    simp [normalizedVelocity]
    ring
  rw [normalize first, normalize second]
  have positive : 0 < 3 + 2 * squared (normalizedVelocity velocity) +
      3 * squared (normalizedVelocity velocity)^2 := by
    have nonnegative : 0 ≤ squared (normalizedVelocity velocity) := Finset.sum_nonneg fun _ _ => sq_nonneg _
    positivity
  unfold isotropicPressure fluxFactor pressure
  field_simp [(NativePauliControl.denominator_pos (normalizedVelocity velocity)).ne']
  ring

theorem isotropicPressure_nonnegative (velocity : PhysicalSpace) : 0 ≤ isotropicPressure velocity := by
  have nonnegative : 0 ≤ squared (normalizedVelocity velocity) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  unfold isotropicPressure
  positivity

theorem isotropicPressure_le (velocity : PhysicalSpace) : isotropicPressure velocity ≤ ‖velocity‖ ^ 2 / 3 := by
  have nonnegative : 0 ≤ squared (normalizedVelocity velocity) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have norm : ‖velocity‖ ^ 2 = 16 * squared (normalizedVelocity velocity) := by
    simp [EuclideanSpace.norm_sq_eq, squared, normalizedVelocity, Fin.sum_univ_three]
    ring
  rw [norm]
  unfold isotropicPressure
  apply (div_le_iff₀ (by positivity)).2
  nlinarith [sq_nonneg (squared (normalizedVelocity velocity))]

end
end SaturationMonoid.NavierStokes.NativeConstitutiveFlux
