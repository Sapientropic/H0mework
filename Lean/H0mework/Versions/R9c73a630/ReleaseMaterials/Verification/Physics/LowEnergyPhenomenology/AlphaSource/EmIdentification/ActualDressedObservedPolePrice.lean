import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFifthLaplacePrice
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCompleteNoetherPrice
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFiniteStaticRead
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticPoleRead

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedObservedPolePrice
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift
open PreparationVacuumGaugeSourceInjection PreparationVacuumPhysicalHalfAxis
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedCompletePrice
open ActualDressedFiniteStaticRead ActualDressedSylvester ActualDressedStaticPole
open Set Filter MeasureTheory
open scoped Topology
attribute [local irreducible] completeNoetherPrice dressedNoetherJet dressedStaticPolarization
  finiteConstantFieldSlope dressedStaticPoleOrder dressedStaticPoleLeading laplaceWeight

/-- The unchanged actual Pi directly consumes the complete source-owned five-term observation price. -/
theorem actual_static_polarization_laplace_price (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0<lambda.re) (i j : Fin 289) :
    ‖dressedStaticPolarization event transfer lambda i j‖≤
      completeNoetherPrice event transfer (fieldUnit i) (fieldUnit j)*
        (∫t : ℝ in Ioi 0,Real.exp (-(lambda.re*t))*(1+t)^5) := by
  rw [dressed_static_polarization_finite event transfer lambda positive i j]
  have paid:=finite_static_integrand_integrable event transfer (fieldUnit j) lambda positive i
  have majorant:=(fifth_laplace_integrable lambda.re positive).const_mul
    (completeNoetherPrice event transfer (fieldUnit i) (fieldUnit j))
  calc
    _≤∫t : ℝ in Ioi 0,‖laplaceWeight lambda t*finiteConstantFieldSlope event transfer (fieldUnit j) t i‖ :=
      norm_integral_le_integral_norm _
    _≤∫t : ℝ in Ioi 0,completeNoetherPrice event transfer (fieldUnit i) (fieldUnit j)*
        (Real.exp (-(lambda.re*t))*(1+t)^5) := by
      apply integral_mono_ae paid.norm majorant
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t future
      rw [norm_mul,laplace_norm,finite_constant_field_slope_actual]
      have source:=actual_complete_noether_jet_price event transfer (fieldUnit j) t i
      rw [abs_of_pos future] at source
      exact (mul_le_mul_of_nonneg_left source (Real.exp_nonneg _)).trans_eq (by ring)
    _=_ := integral_const_mul _ _

def observedStaticSourcePrice (event : DressedEvent) (transfer : PhysicalMomentum)
    (i j : Fin 289) : ℝ := 3872*completeNoetherPrice event transfer (fieldUnit i) (fieldUnit j)

attribute [local irreducible] observedStaticSourcePrice

theorem observed_static_source_price_nonneg (event : DressedEvent) (transfer : PhysicalMomentum)
    (i j : Fin 289) : 0≤observedStaticSourcePrice event transfer i j := by
  unfold observedStaticSourcePrice
  exact mul_nonneg (by norm_num) (complete_noether_price_nonneg event transfer _ _)

/-- The full observed static matrix has a sixth-order damping price generated from its actual source. -/
theorem actual_static_polarization_sigma_six_price (event : DressedEvent) (transfer : PhysicalMomentum)
    (sigma : ℝ) (positive : 0<sigma) (small : sigma≤1) (i j : Fin 289) :
    sigma^6*‖dressedStaticPolarization event transfer (sigma:ℂ) i j‖≤
      observedStaticSourcePrice event transfer i j := by
  have source:=actual_static_polarization_laplace_price event transfer (sigma:ℂ) positive i j
  have positivePrice:=complete_noether_price_nonneg event transfer (fieldUnit i) (fieldUnit j)
  calc
    _ ≤ sigma^6*(completeNoetherPrice event transfer (fieldUnit i) (fieldUnit j)*
        (∫t : ℝ in Ioi 0,Real.exp (-(sigma*t))*(1+t)^5)) :=
      mul_le_mul_of_nonneg_left source (pow_nonneg positive.le 6)
    _ = completeNoetherPrice event transfer (fieldUnit i) (fieldUnit j)*
        (sigma^6*(∫t : ℝ in Ioi 0,Real.exp (-(sigma*t))*(1+t)^5)) := by ring
    _ ≤ completeNoetherPrice event transfer (fieldUnit i) (fieldUnit j)*3872 :=
      mul_le_mul_of_nonneg_left (fifth_laplace_sigma_six_price sigma positive small) positivePrice
    _=_ := by unfold observedStaticSourcePrice;ring

/-- Higher operator pole order may cancel under the unchanged complete physical observer. -/
theorem actual_static_pole_leading_zero_of_order_gt_three (event : DressedEvent)
    (high : 3<dressedStaticPoleOrder event) (i j : Fin 289) :
    dressedStaticPoleLeading event i j=0 := by
  let order:=2*dressedStaticPoleOrder event
  let sourcePrice:=observedStaticSourcePrice event 0 i j
  have gap : 0<order-6 := by dsimp only [order];omega
  have power : Tendsto (fun sigma : ℝ=>sigma^(order-6)*sourcePrice)
      (nhdsWithin 0 (Ioi (0:ℝ))) (𝓝 0) := by
    have identity : Tendsto (fun sigma : ℝ=>sigma) (nhdsWithin 0 (Ioi (0:ℝ))) (𝓝 (0:ℝ)) :=
      tendsto_id.mono_left inf_le_left
    simpa only [zero_pow gap.ne',zero_mul] using
      (identity.pow (order-6)).mul_const sourcePrice
  have small : ∀ᶠsigma : ℝ in nhdsWithin 0 (Ioi (0:ℝ)),sigma<1 :=
    (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono inf_le_left
  have zero : Tendsto (fun sigma : ℝ=>(sigma:ℂ)^order*
      dressedStaticPolarization event 0 (sigma:ℂ) i j)
      (nhdsWithin 0 (Ioi (0:ℝ))) (𝓝 0) := by
    apply squeeze_zero_norm' _ power
    filter_upwards [self_mem_nhdsWithin,small] with sigma positive near
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
    have split : order=(order-6)+6 := by omega
    rw [split,pow_add,mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (actual_static_polarization_sigma_six_price event 0 sigma positive near.le i j)
      (pow_nonneg positive.le _)
  exact tendsto_nhds_unique (dressed_static_pole_leading_limit event i j) zero

end LowEnergy.GaussComposite.ActualDressedObservedPolePrice
