import H0mework.Versions.X.NavierStokes.WindowSchurFrozen.Kernel
import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.Green
import H0mework.Versions.X.NavierStokes.StressTimeControl.DualCurl

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryHeatDual
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeResolventAdjoint NativeWindowOperatorGreen
open NativeWholeH1Mixed (modes modes_zero modes_closed)
noncomputable section
variable {nu : Viscosity}

def heatMap (nu : Viscosity) (M : ℕ) : Module.End ℝ (physicalSpace (modes M)) :=
  LinearMap.id+nu.coeff • laplacian (modes M) (modes_zero M) (modes_closed M) nu

def form (nu : Viscosity) (M : ℕ) : physicalSpace (modes M) →ₗ[ℝ] physicalSpace (modes M) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => pairing (modes M) x (heatMap nu M y))
    (fun _ _ _ => by simp only [map_add,LinearMap.add_apply])
    (fun _ _ _ => by simp only [map_smul,LinearMap.smul_apply,smul_eq_mul])
    (fun _ _ _ => by simp only [map_add])
    (fun _ _ _ => by simp only [map_smul,smul_eq_mul])

def energy (nu : Viscosity) (M : ℕ) (v : physicalSpace (modes M)) : ℝ :=
  ‖coefficients (modes M) v‖^2+nu.coeff*curlPair (modes M) v.1 v.1

theorem energy_nonnegative (nu : Viscosity) (M : ℕ) (v : physicalSpace (modes M)) : 0≤energy nu M v := by
  have gradient : 0≤curlPair (modes M) v.1 v.1 := by
    rw [← NativeDualCurlResolvent.gradient_norm_sq (modes M) (modes_zero M)]
    exact sq_nonneg _
  exact add_nonneg (sq_nonneg _) (mul_nonneg nu.coeff_pos.le gradient)

theorem form_self (nu : Viscosity) (M : ℕ) (v : physicalSpace (modes M)) : form nu M v v=energy nu M v := by
  simp only [form,LinearMap.mk₂_apply,heatMap,LinearMap.add_apply,LinearMap.id_apply,LinearMap.smul_apply,
    map_add,map_smul,smul_eq_mul,laplacian_pairing]
  exact congrArg (fun x : ℝ => x+nu.coeff*curlPair (modes M) v.1 v.1) (real_inner_self_eq_norm_sq (coefficients (modes M) v))

theorem form_symmetric (nu : Viscosity) (M : ℕ) (x y : physicalSpace (modes M)) : form nu M x y=form nu M y x := by
  simp only [form,LinearMap.mk₂_apply,heatMap,LinearMap.add_apply,LinearMap.id_apply,LinearMap.smul_apply,
    map_add,map_smul,smul_eq_mul]
  rw [← NativeWindowAugmentedGreen.laplacian_adjoint (modes M) (modes_zero M) (modes_closed M) x y,
    pairing_symmetric (modes M) x y,pairing_symmetric (modes M) (laplacian (modes M) (modes_zero M) (modes_closed M) nu x) y]

theorem energy_faithful (nu : Viscosity) (M : ℕ) (v : physicalSpace (modes M)) (zero : energy nu M v=0) : v=0 := by
  apply pairing_faithful (modes M)
  have gradient : 0≤curlPair (modes M) v.1 v.1 := by
    rw [← NativeDualCurlResolvent.gradient_norm_sq (modes M) (modes_zero M)]
    exact sq_nonneg _
  have mass : pairing (modes M) v v=‖coefficients (modes M) v‖^2 := real_inner_self_eq_norm_sq (coefficients (modes M) v)
  unfold energy at zero
  have signed := mul_nonneg nu.coeff_pos.le gradient
  linarith only [zero,mass,signed]

private theorem positive_cauchy {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (symmetric : ∀ x y,B x y=B y x) (positive : ∀ x,0≤B x x)
    (x y : V) (ypos : 0<B y y) : (B x y)^2≤B x x*B y y := by
  let t:=B x y/B y y
  have source := positive (x-t • y)
  have original : B (x-t • y) (x-t • y)=B x x-(B x y)^2/B y y := by
    simp only [map_sub,LinearMap.sub_apply,map_smul,LinearMap.smul_apply,smul_eq_mul,symmetric y x]
    dsimp only [t]
    field_simp [ypos.ne']
    ring
  rw [original] at source
  apply (div_le_iff₀ ypos).mp
  linarith only [source]

theorem form_cauchy (nu : Viscosity) (M : ℕ) (x y : physicalSpace (modes M)) :
    (form nu M x y)^2≤energy nu M x*energy nu M y := by
  by_cases zero : energy nu M y=0
  · have actual := energy_faithful nu M y zero
    have paired : form nu M x y=0 := by rw [actual,map_zero]
    rw [paired,zero,mul_zero]
    norm_num
  · have positive : 0<form nu M y y := by rw [form_self]; exact lt_of_le_of_ne (energy_nonnegative nu M y) (Ne.symm zero)
    simpa only [form_self] using positive_cauchy (form nu M) (form_symmetric nu M)
      (fun v => (energy_nonnegative nu M v).trans_eq (form_self nu M v).symm) x y positive

def heat (nu : Viscosity) (M : ℕ) : physicalSpace (modes M) ≃L[ℝ] physicalSpace (modes M) :=
  (physicalResolver (modes M) (modes_zero M) (modes_closed M) nu 0 zero_reality 1 (by norm_num)).toContinuousLinearEquiv

theorem heat_write (nu : Viscosity) (M : ℕ) (f : physicalSpace (modes M)) : heatMap nu M (heat nu M f)=f := by
  have original := resolver_write (dissipative (modes M) (modes_zero M) (modes_closed M) nu)
    (pairing (modes M)) (pairing_faithful (modes M))
    (physicalOperator_dissipative (modes M) (modes_zero M) (modes_closed M) nu 0 zero_reality) 1 (by norm_num) f
  change heat nu M f-(1:ℝ) • dissipative (modes M) (modes_zero M) (modes_closed M) nu (heat nu M f)=f at original
  simpa only [heatMap,LinearMap.add_apply,LinearMap.id_apply,LinearMap.smul_apply,one_smul,
    dissipative_laplacian,neg_smul,sub_neg_eq_add] using original

def heatEnergy (nu : Viscosity) (M : ℕ) (f : physicalSpace (modes M)) : ℝ := pairing (modes M) (heat nu M f) f

theorem heatEnergy_self (nu : Viscosity) (M : ℕ) (f : physicalSpace (modes M)) : heatEnergy nu M f=energy nu M (heat nu M f) := by
  have paired := congrArg (pairing (modes M) (heat nu M f)) (heat_write nu M f)
  change form nu M (heat nu M f) (heat nu M f)=heatEnergy nu M f at paired
  exact paired.symm.trans (form_self nu M (heat nu M f))

theorem heatEnergy_nonnegative (nu : Viscosity) (M : ℕ) (f : physicalSpace (modes M)) : 0≤heatEnergy nu M f :=
  (energy_nonnegative nu M (heat nu M f)).trans_eq (heatEnergy_self nu M f).symm

theorem dual_pairing_bound (nu : Viscosity) (M : ℕ) (u f : physicalSpace (modes M)) :
    (pairing (modes M) u f)^2≤energy nu M u*heatEnergy nu M f := by
  have paired := congrArg (pairing (modes M) u) (heat_write nu M f)
  change form nu M u (heat nu M f)=pairing (modes M) u f at paired
  exact (congrArg (fun x : ℝ => x^2) paired).symm.trans_le
    ((form_cauchy nu M u (heat nu M f)).trans_eq (congrArg (fun x : ℝ => energy nu M u*x) (heatEnergy_self nu M f).symm))

theorem source_energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (f : physicalSpace (modes M)) :
    energy nu M (NativeWindowHistoryFrozenInverse.physical seed M time f)=
      pairing (modes M) (NativeWindowHistoryFrozenInverse.physical seed M time f) f := by
  have source := NativeDualCurlResolvent.resolver_energy (modes M) (modes_zero M) (modes_closed M) nu
    (NativeWindowTraceAdjoint.advector seed M time) (NativeWindowTraceAdjoint.advector_reality seed M time) 1 (by norm_num) f
  simpa only [one_mul,energy,pairing_symmetric] using! source

theorem source_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (f : physicalSpace (modes M)) :
    energy nu M (NativeWindowHistoryFrozenInverse.physical seed M time f)≤heatEnergy nu M f := by
  let u:=NativeWindowHistoryFrozenInverse.physical seed M time f
  have bound := dual_pairing_bound nu M u f
  have read := source_energy seed M time f
  change energy nu M u=pairing (modes M) u f at read
  rw [← read] at bound
  by_cases zero : energy nu M u=0
  · rw [zero]
    exact heatEnergy_nonnegative nu M f
  · have positive : 0<energy nu M u := lt_of_le_of_ne (energy_nonnegative nu M u) (Ne.symm zero)
    change energy nu M u≤heatEnergy nu M f
    by_contra falseBound
    have strictly := mul_pos positive (sub_pos.mpr (lt_of_not_ge falseBound))
    nlinarith only [bound,strictly]

theorem form_bound (nu : Viscosity) (M : ℕ) (u v : physicalSpace (modes M)) :
    |form nu M u v|≤Real.sqrt (energy nu M u)*Real.sqrt (energy nu M v) := by
  have source := Real.sqrt_le_sqrt (form_cauchy nu M u v)
  simpa only [Real.sqrt_sq_eq_abs,Real.sqrt_mul (energy_nonnegative nu M u)] using source

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryHeatDual
