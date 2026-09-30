import H0mework.NavierStokes.MaterialJets.Densitized

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativeGaugeMomentum

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction StageNineHolonomicField
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePauliControl NativePauliMotherAction NativePauliCoframeAction NativePauliPairing
open NativeMaterialAdjointPrincipal NativeMaterialMomentumJet

noncomputable section

def generatorCurrent (velocity : PhysicalSpace) (direction : Fin 4) (color : Fin 3) : ℝ :=
  (NativeCanonicalFluidCoframe.dual velocity
    (Complex.I • diracMatrixMatterAction (diracGamma direction)
      (diracExteriorMotherLieAction (p286LieBlockEmbed (generator color))
        (NativeCanonicalFluidCoframe.matter velocity)))).re

theorem generatorCurrent_temporal (velocity : PhysicalSpace) (color : Fin 3) :
    generatorCurrent velocity 0 color = -velocity color := by
  rw [generatorCurrent, source_matter, generator_action, kinetic_block]
  fin_cases color <;>
    simp [blockPair, spinAction, spinPrincipal, hermitianBlock, colorAction, pauli, normalizedVelocity,
      Fin.sum_univ_two, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im, map_ofNat] <;> ring

theorem generatorCurrent_spatial (velocity : PhysicalSpace) (direction color : Fin 3) :
    generatorCurrent velocity direction.succ color =
      -2 * ((1 - NativeCartanConstitutive.squared (normalizedVelocity velocity)) *
        (if color = direction then 1 else 0) + 2 * normalizedVelocity velocity color * normalizedVelocity velocity direction) := by
  rw [generatorCurrent, source_matter, generator_action, kinetic_block, NativeCartanStressLaw.color_stress]
  ring

def current (velocity : PhysicalSpace) (variation : P286GaugeOneForm) : ℝ :=
  volumeFactor velocity * ∑ direction : Fin 4,
    (NativeCanonicalFluidCoframe.dual velocity (principal velocity direction
      (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (variation direction)))
        (NativeCanonicalFluidCoframe.matter velocity)))).re

def momentumScale (velocity : PhysicalSpace) (direction : Fin 4) : ℝ :=
  if direction = 0 then NativeCanonicalFluidCoframe.density velocity else 4

/-- This is a source-dependent tangent direction of the original gauge variation, with the physical clock fixed. -/
def momentumVariation (velocity : PhysicalSpace) (direction : Fin 4) (color : Fin 3) : P286GaugeOneForm :=
  Pi.single direction (momentumScale velocity direction • p286CoordinateEquiv (generator color))

theorem current_single (velocity : PhysicalSpace) (direction : Fin 4) (color : Fin 3) :
    current velocity (momentumVariation velocity direction color) =
      coefficient velocity direction * momentumScale velocity direction * generatorCurrent velocity direction color := by
  have each (index : Fin 4) :
      diracExteriorMotherLieAction
        (p286LieBlockEmbed (p286CoordinateEquiv.symm (momentumVariation velocity direction color index)))
          (NativeCanonicalFluidCoframe.matter velocity) =
        if index = direction then (momentumScale velocity direction : ℂ) •
          diracExteriorMotherLieAction (p286LieBlockEmbed (generator color)) (NativeCanonicalFluidCoframe.matter velocity)
        else 0 := by
    by_cases same : index = direction
    · subst index
      simp only [momentumVariation, Pi.single_eq_same, p286CoordinateEquiv.symm.map_smul, p286CoordinateEquiv.symm_apply_apply,
        p286LieBlockEmbed_real_smul, diracExteriorMotherLieAction_real_smul, LinearMap.smul_apply]
      rfl
    · simp [momentumVariation, same, p286LieBlockEmbed_zero]
  simp only [current, each, apply_ite, map_smul, map_zero, Complex.zero_re,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [principal_gamma, LinearMap.smul_apply, map_smul]
  simp only [generatorCurrent, coefficient, map_smul, ← Complex.ofReal_inv, smul_eq_mul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem momentum_temporal (velocity : PhysicalSpace) (color : Fin 3) :
    current velocity (momentumVariation velocity 0 color) = -velocity color := by
  rw [current_single, coefficient_eq, generatorCurrent_temporal]
  simp [momentumScale, (NativeCanonicalFluidCoframe.density_pos velocity).ne']

def isotropicTerm (velocity : PhysicalSpace) : ℝ := ‖velocity‖ ^ 2 / 2 - 8

theorem momentum_spatial (velocity : PhysicalSpace) (direction color : Fin 3) :
    current velocity (momentumVariation velocity direction.succ color) =
      -velocity direction * velocity color + isotropicTerm velocity * (if direction = color then 1 else 0) := by
  rw [current_single, NativeDensitizedMaterial.spatial_coefficient, one_mul, generatorCurrent_spatial]
  have scale : momentumScale velocity direction.succ = 4 := by
    simp [momentumScale]
  rw [scale]
  by_cases same : direction = color
  · subst color
    simp [isotropicTerm, NativeCartanConstitutive.squared, normalizedVelocity,
      EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    ring
  · simp [same, Ne.symm same, normalizedVelocity]
    ring

end
end SaturationMonoid.NavierStokes.NativeGaugeMomentum
