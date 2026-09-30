import H0mework.NavierStokes.MaterialGauge.Momentum

set_option autoImplicit false
open scoped BigOperators

namespace SaturationMonoid.NavierStokes.NativeGaugeCurrentAction

open PhysicsCore DiracExteriorMatterAction StageNineHolonomicField
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open ThreeDimensionalPeriodicCoarseFilterCore NativeGaugeMomentum
open NativeMaterialAdjointPrincipal NativeMaterialMomentumJet NativeMatterCoframeStress

noncomputable section

def variedJet (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace)
    (variation : P286GaugeOneForm) (direction : Fin 4) : DiracExteriorMatterCarrier :=
  NativeBalancedMaterialJet.derivative velocity derivative direction +
    diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (variation direction)))
      (NativeCanonicalFluidCoframe.matter velocity)

/-- The already identified original matter-sector density, evaluated on the source gauge variation. -/
def gaugeDensity (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) (variation : P286GaugeOneForm) : ℝ :=
  density (kineticCoefficients (NativeCanonicalFluidCoframe.dual velocity) (variedJet velocity derivative variation))
    0 (NativeCanonicalFluidCoframe.coframe velocity)

theorem density_split (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) (variation : P286GaugeOneForm) :
    gaugeDensity velocity derivative variation = gaugeDensity velocity derivative 0 + current velocity variation := by
  simp only [gaugeDensity, density, pairing_eq_kinetic, add_zero, variedJet, map_add,
    Finset.sum_add_distrib, smul_add, Complex.add_re, Pi.zero_apply, map_zero,
    p286LieBlockEmbed_zero, diracExteriorMotherLieAction_zero_matrix, add_zero,
    current, principal, LinearMap.smul_apply, Finset.smul_sum, map_sum, Complex.re_sum, volumeFactor]
  ring

theorem current_smul (velocity : PhysicalSpace) (variation : P286GaugeOneForm) (parameter : ℝ) :
    current velocity (parameter • variation) = parameter * current velocity variation := by
  simp only [current, Pi.smul_apply, p286CoordinateEquiv.symm.map_smul,
    p286LieBlockEmbed_real_smul, diracExteriorMotherLieAction_real_smul, LinearMap.smul_apply]
  simp only [map_smul, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, ← Finset.mul_sum]
  ring

theorem gaugeDensity_affine (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace)
    (variation : P286GaugeOneForm) (parameter : ℝ) :
    gaugeDensity velocity derivative (parameter • variation) =
      gaugeDensity velocity derivative 0 + parameter * current velocity variation := by
  rw [density_split, current_smul]

/-- The native momentum current is a true derivative of the original source matter action. -/
theorem gaugeDensity_hasDerivAt (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace)
    (variation : P286GaugeOneForm) :
    HasDerivAt (fun parameter : ℝ => gaugeDensity velocity derivative (parameter • variation))
      (current velocity variation) 0 := by
  have expression : (fun parameter : ℝ => gaugeDensity velocity derivative (parameter • variation)) =
      fun parameter => gaugeDensity velocity derivative 0 + parameter * current velocity variation :=
    funext (gaugeDensity_affine velocity derivative variation)
  rw [expression]
  convert! (((hasDerivAt_id (0 : ℝ)).mul_const (current velocity variation)).const_add
    (gaugeDensity velocity derivative 0)) using 1
  simp

end
end SaturationMonoid.NavierStokes.NativeGaugeCurrentAction
