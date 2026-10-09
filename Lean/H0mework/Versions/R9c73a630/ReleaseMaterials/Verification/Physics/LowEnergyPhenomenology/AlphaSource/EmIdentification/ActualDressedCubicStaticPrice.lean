import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCubicLaplacePrice
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCubicNoetherPrice
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFiniteStaticRead

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedCubicPrice
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift
open PreparationVacuumGaugeSourceInjection PreparationVacuumPhysicalHalfAxis
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedCubicPrice
open ActualDressedFiniteStaticRead ActualDressedSylvester
open Set Filter MeasureTheory
open scoped Topology
attribute [local irreducible] completeCubicNoetherPrice dressedNoetherJet dressedStaticPolarization
  finiteConstantFieldSlope laplaceWeight

/-- The unchanged actual Pi directly consumes the complete source-owned five-term observation price. -/
theorem actual_static_polarization_cubic_laplace_price (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0<lambda.re) (i j : Fin 289) :
    ‖dressedStaticPolarization event transfer lambda i j‖≤
      completeCubicNoetherPrice event transfer (fieldUnit i) (fieldUnit j)*
        (∫t : ℝ in Ioi 0,Real.exp (-(lambda.re*t))*(1+t)^3) := by
  rw [dressed_static_polarization_finite event transfer lambda positive i j]
  have paid:=finite_static_integrand_integrable event transfer (fieldUnit j) lambda positive i
  have majorant:=(cubic_laplace_integrable lambda.re positive).const_mul
    (completeCubicNoetherPrice event transfer (fieldUnit i) (fieldUnit j))
  calc
    _≤∫t : ℝ in Ioi 0,‖laplaceWeight lambda t*finiteConstantFieldSlope event transfer (fieldUnit j) t i‖ :=
      norm_integral_le_integral_norm _
    _≤∫t : ℝ in Ioi 0,completeCubicNoetherPrice event transfer (fieldUnit i) (fieldUnit j)*
        (Real.exp (-(lambda.re*t))*(1+t)^3) := by
      apply integral_mono_ae paid.norm majorant
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t future
      rw [norm_mul,laplace_norm,finite_constant_field_slope_actual]
      have source:=actual_complete_noether_cubic_jet_price event transfer (fieldUnit j) t i
      rw [abs_of_pos future] at source
      exact (mul_le_mul_of_nonneg_left source (Real.exp_nonneg _)).trans_eq (by ring)
    _=_ := integral_const_mul _ _

def observedCubicStaticSourcePrice (event : DressedEvent) (transfer : PhysicalMomentum)
    (i j : Fin 289) : ℝ := 56*completeCubicNoetherPrice event transfer (fieldUnit i) (fieldUnit j)

attribute [local irreducible] observedCubicStaticSourcePrice

theorem observed_cubic_static_source_price_nonneg (event : DressedEvent) (transfer : PhysicalMomentum)
    (i j : Fin 289) : 0≤observedCubicStaticSourcePrice event transfer i j := by
  unfold observedCubicStaticSourcePrice
  exact mul_nonneg (by norm_num) (complete_cubic_noether_price_nonneg event transfer _ _)

/-- The full observed static matrix has a fourth-order damping price generated from its actual source. -/
theorem actual_static_polarization_sigma_four_price (event : DressedEvent) (transfer : PhysicalMomentum)
    (sigma : ℝ) (positive : 0<sigma) (small : sigma≤1) (i j : Fin 289) :
    sigma^4*‖dressedStaticPolarization event transfer (sigma:ℂ) i j‖≤
      observedCubicStaticSourcePrice event transfer i j := by
  have source:=actual_static_polarization_cubic_laplace_price event transfer (sigma:ℂ) positive i j
  have positivePrice:=complete_cubic_noether_price_nonneg event transfer (fieldUnit i) (fieldUnit j)
  calc
    _ ≤ sigma^4*(completeCubicNoetherPrice event transfer (fieldUnit i) (fieldUnit j)*
        (∫t : ℝ in Ioi 0,Real.exp (-(sigma*t))*(1+t)^3)) :=
      mul_le_mul_of_nonneg_left source (pow_nonneg positive.le 4)
    _ = completeCubicNoetherPrice event transfer (fieldUnit i) (fieldUnit j)*
        (sigma^4*(∫t : ℝ in Ioi 0,Real.exp (-(sigma*t))*(1+t)^3)) := by ring
    _ ≤ completeCubicNoetherPrice event transfer (fieldUnit i) (fieldUnit j)*56 :=
      mul_le_mul_of_nonneg_left (cubic_laplace_sigma_four_price sigma positive small) positivePrice
    _=_ := by unfold observedCubicStaticSourcePrice;ring


end LowEnergy.GaussComposite.ActualDressedCubicPrice
