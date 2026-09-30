import H0mework.Versions.X.NavierStokes.CartanAction.StressLaw
import H0mework.Versions.X.NavierStokes.MaterialAction.ColorAction

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativeConstitutiveColor

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineFullDiracAdjointMaterial
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePauliControl NativePauliMotherAction NativePauliCoframeAction
open NativePauliPairing NativeCartanConstitutive NativeCartanStressLaw
open NativeMatterCoframeStress NativeSourceCoframeStress

noncomputable section

def radial (velocity : Vector) : Fin 4 → Fin 3 → ℝ :=
  let beta := squared velocity * (squared velocity - 1) / denominator velocity
  let tau := -4 * squared velocity / denominator velocity
  !![tau * velocity 0, tau * velocity 1, tau * velocity 2;
     velocity 0 * velocity 0 + beta, velocity 0 * velocity 1, velocity 0 * velocity 2;
     velocity 1 * velocity 0, velocity 1 * velocity 1 + beta, velocity 1 * velocity 2;
     velocity 2 * velocity 0, velocity 2 * velocity 1, velocity 2 * velocity 2 + beta]

theorem radial_action_zero (velocity : Vector) : action velocity (radial velocity) = 0 := by
  ext row column
  fin_cases row <;> fin_cases column <;> apply Complex.ext <;>
    simp [action, spinPrincipal, hermitianBlock, pauli,
      Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four, Complex.mul_re, Complex.mul_im]
  all_goals simp [radial, squared, denominator, Fin.sum_univ_three]
  all_goals field_simp
  all_goals ring

theorem action_smul (velocity : Vector) (scale : ℝ) (coefficients : Fin 4 → Fin 3 → ℝ) :
    action velocity (scale • coefficients) = (scale : ℂ) • action velocity coefficients := by
  ext row column
  simp [action, Finset.mul_sum, mul_assoc]

def correctionScale (velocity : PhysicalSpace) : ℝ :=
  NativeCanonicalFluidCoframe.scale velocity ^ 2 / 2 * (-16 / fluxFactor (normalizedVelocity velocity) - 1)

def coefficients (velocity : PhysicalSpace) : Fin 4 → Fin 3 → ℝ :=
  correctionScale velocity • radial (normalizedVelocity velocity)

theorem source_vector_zero (velocity : PhysicalSpace) :
    gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity)
      (NativeSourceColorAction.increment velocity (coefficients velocity)) = 0 := by
  rw [NativeSourceColorAction.vector_eq, wholeAction_eq, coefficients, action_smul,
    radial_action_zero, smul_zero, map_zero, map_zero]

theorem source_dual_zero (velocity : PhysicalSpace) (candidate : DiracExteriorMatterCarrier) :
    (∑ direction, NativeCanonicalFluidCoframe.dual velocity
      (NativeMaterialAdjointPrincipal.principal velocity direction
        (NativeSourceColorAction.operator velocity (coefficients velocity) direction candidate))) = 0 := by
  rw [NativeSourceColorAction.dual_eq_adjoint, source_vector_zero, fullCanonicalDiracAdjoint_zero,
    LinearMap.zero_apply]

theorem color_current (velocity : PhysicalSpace) (coefficients : Fin 4 → Fin 3 → ℝ)
    (direction : Fin 4) (internal : Fin 3) :
    kineticCoefficients (NativeCanonicalFluidCoframe.dual velocity)
      (NativeSourceColorAction.increment velocity coefficients) direction internal.succ =
        -compensation velocity direction * ∑ color : Fin 3, coefficients direction color *
          (2 * ((1 - squared (normalizedVelocity velocity)) * (if color = internal then 1 else 0) +
            2 * normalizedVelocity velocity color * normalizedVelocity velocity internal)) := by
  simp only [kineticCoefficients, NativeSourceColorAction.increment_block,
    map_smul, map_sum, Finset.smul_sum, dual_gamma_block]
  simp only [smul_eq_mul, Complex.re_sum, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, add_zero, sub_zero, zero_sub, color_stress]
  simp only [Fin.sum_univ_three]
  ring

def stress (velocity : PhysicalSpace) : LorentzianCoframe →L[ℝ] ℝ :=
  responseCovector velocity (kineticCoefficients (NativeCanonicalFluidCoframe.dual velocity)
    (NativeSourceColorAction.increment velocity (coefficients velocity)))

theorem stress_hasFDerivAt (velocity : PhysicalSpace) :
    HasFDerivAt (density (kineticCoefficients (NativeCanonicalFluidCoframe.dual velocity)
      (NativeSourceColorAction.increment velocity (coefficients velocity))) 0)
      (stress velocity) (NativeCanonicalFluidCoframe.coframe velocity) := by
  apply density_hasFDerivAt_of_inner_zero _ _ _ (NativeCanonicalFluidCoframe.coframe_nondegenerate velocity)
  rw [add_zero, pairing_eq_kinetic]
  change (NativeCanonicalFluidCoframe.dual _ (gaugeVectorAt _ _)).re = 0
  rw [source_vector_zero, map_zero, Complex.zero_re]

theorem stress_spatial (velocity : PhysicalSpace) (first second : Fin 3) :
    stress velocity (Matrix.single first.succ second.succ 1) =
      (2 * correctionScale velocity / NativeCanonicalFluidCoframe.scale velocity ^ 2) *
        (fluxFactor (normalizedVelocity velocity) * normalizedVelocity velocity first * normalizedVelocity velocity second -
          pressure (normalizedVelocity velocity) * (if first = second then 1 else 0)) := by
  rw [stress, responseCovector_spatial, color_current]
  have spatial : compensation velocity first.succ = (NativeCanonicalFluidCoframe.density velocity)⁻¹ := by
    fin_cases first <;> rfl
  rw [spatial, ← NativeCanonicalFluidCoframe.scale_cube]
  have entry (direction : Fin 4) (color : Fin 3) : coefficients velocity direction color =
      correctionScale velocity * radial (normalizedVelocity velocity) direction color := rfl
  simp only [entry]
  unfold radial fluxFactor pressure
  fin_cases first <;> fin_cases second <;>
    simp [Fin.sum_univ_three, denominator, squared]
  all_goals field_simp [(NativeCanonicalFluidCoframe.scale_pos velocity).ne']
  all_goals ring

end
end SaturationMonoid.NavierStokes.NativeConstitutiveColor
