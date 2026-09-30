import H0mework.Versions.X.NavierStokes.MaterialAction.AdjointPrincipal

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativeMaterialMomentumJet

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineFullDiracAdjointMaterial
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePauliCoframeAction NativeMaterialJetAction NativeMaterialAdjointPrincipal

noncomputable section

def volumeFactor (velocity : PhysicalSpace) : ℝ := |Matrix.det (NativeCanonicalFluidCoframe.coframe velocity)|

def coefficient (velocity : PhysicalSpace) (direction : Fin 4) : ℝ :=
  volumeFactor velocity / NativeCanonicalFluidCoframe.diagonal velocity direction

theorem coefficient_eq (velocity : PhysicalSpace) (direction : Fin 4) :
    coefficient velocity direction = if direction = 0 then (NativeCanonicalFluidCoframe.density velocity)⁻¹ else 1 := by
  fin_cases direction <;>
    simp [coefficient, volumeFactor, NativeCanonicalFluidCoframe.coframe_volume,
      NativeCanonicalFluidCoframe.diagonal, ← NativeCanonicalFluidCoframe.scale_cube velocity,
      (NativeCanonicalFluidCoframe.scale_pos velocity).ne']
  field_simp

def coefficientDerivative (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) (direction : Fin 4) : ℝ :=
  if direction = 0 then
    -3 * NativePauliJet.logDerivative (normalizedVelocity velocity) (normalizedJet derivative) direction /
      NativeCanonicalFluidCoframe.density velocity else 0

/-- These are the derivatives of the actual volume times inverse-frame principal coefficients. -/
theorem coefficient_hasDerivAt {path : ℝ → PhysicalSpace} {time : ℝ}
    (derivative : Fin 4 → PhysicalSpace) (direction : Fin 4)
    (differentiable : HasDerivAt path (derivative direction) time) :
    HasDerivAt (fun actual => coefficient (path actual) direction)
      (coefficientDerivative (path time) derivative direction) time := by
  by_cases temporal : direction = 0
  · subst direction
    simp [coefficient_eq, coefficientDerivative]
    convert! (density_hasDerivAt _ differentiable).inv (NativeCanonicalFluidCoframe.density_pos (path time)).ne' using 1
    simp only [NativePauliJet.logDerivative, normalizedJet, ← source_density]
    field_simp
  · simpa only [coefficient_eq, coefficientDerivative, if_neg temporal] using hasDerivAt_const time (1 : ℝ)

theorem weighted_principal (velocity : PhysicalSpace) (direction : Fin 4)
    (matter candidate : DiracExteriorMatterCarrier) :
    (volumeFactor velocity : ℂ) * fullCanonicalDiracAdjoint matter (principal velocity direction candidate) =
      (coefficient velocity direction : ℂ) * fullCanonicalDiracAdjoint matter
        (Complex.I • diracMatrixMatterAction (diracGamma direction) candidate) := by
  rw [principal_gamma]
  simp only [LinearMap.smul_apply, map_smul, smul_eq_mul, coefficient]
  push_cast
  ring

theorem principal_divergence (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace)
    (matter candidate : DiracExteriorMatterCarrier) :
    (∑ direction, (coefficientDerivative velocity derivative direction : ℂ) *
      fullCanonicalDiracAdjoint matter (Complex.I • diracMatrixMatterAction (diracGamma direction) candidate)) =
      (-3 * NativePauliJet.logDerivative (normalizedVelocity velocity) (normalizedJet derivative) 0 : ℂ) *
        ((volumeFactor velocity : ℂ) * fullCanonicalDiracAdjoint matter (principal velocity 0 candidate)) := by
  rw [weighted_principal]
  simp [coefficientDerivative, Fin.sum_univ_four, coefficient_eq]
  ring

end
end SaturationMonoid.NavierStokes.NativeMaterialMomentumJet
