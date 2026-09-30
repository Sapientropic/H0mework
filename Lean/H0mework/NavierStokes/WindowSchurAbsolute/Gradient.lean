import H0mework.NavierStokes.WindowSchurAbsolute.Source
import H0mework.NavierStokes.WindowSchurDynamic.CrossBudget
import H0mework.NavierStokes.WindowSchurDynamic.JacobianSpatial

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimeGradient
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativePhysicalPairing (includeCLM include_norm)
open NativeWindowTraceWholeHistory (original)
open NativeWindowHistorySpatialWords (fiber)
open NativeWindowHistoryCrossBudget (pointEnergy energyBudget)
open NativeWindowAbsoluteTimeSource (H history rate)
open NativeWindowKernelHalfDensity (rootKernel)
noncomputable section
variable {nu : Viscosity}

def spatial (M : ℕ) (j : Coordinate) : H →L[ℝ] H :=
  (fiber M [j]).compLpL 2 (volume : Measure ℝ)

theorem point_spatial (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (j : Coordinate) (sample : ℝ) :
    nu.coeff*‖fiber M [j] (original seed sample)‖^2 ≤ pointEnergy seed M sample := by
  let v:=NativeWindowTraceAdjoint.value seed M sample
  have same:=NativeWindowHistoryCreationGeometry.derivative_mass
    (modes M) (modes_zero M) (modes_closed M) v
  simp only [NativeFiniteActionResolvent.pairing,LinearMap.mk₂_apply,
    real_inner_self_eq_norm_sq] at same
  have one:=Finset.single_le_sum (s := (Finset.univ : Finset Coordinate))
    (f := fun j => ‖NativeFiniteActionResolvent.coefficients (modes M)
      (NativeWindowAugmentedGradient.derivative (modes M) (modes_zero M) (modes_closed M) j v)‖^2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  rw [same] at one
  have scaled:=mul_le_mul_of_nonneg_left one nu.coeff_pos.le
  rw [NativeWindowHistoryJacobianSpatial.fiber_original,
    NativeWindowHistoryOseen.restrict_original_total,include_norm (modes M) (modes_zero M)]
  change nu.coeff*‖NativeFiniteActionResolvent.coefficients (modes M)
    (NativeWindowAugmentedGradient.derivative (modes M) (modes_zero M) (modes_closed M) j v)‖^2 ≤
      ‖NativeFiniteActionResolvent.coefficients (modes M) v‖^2+
        nu.coeff*NativeCommonAdvectorAction.curlPair (modes M) v.1 v.1
  linarith only [scaled,sq_nonneg ‖NativeFiniteActionResolvent.coefficients (modes M) v‖]

private theorem norm_square {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : Lp E 2 (volume : Measure ℝ)) : ‖v‖^2=∫sample,‖v sample‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem field_square (a : ℝ → ℝ) (aMem : MemLp a 2 (volume : Measure ℝ))
    (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ) :
    ‖spatial M j (NativeWindowAbsoluteTimeCarrier.field a aMem (original seed)
      (NativeWindowAbsoluteTimeSource.original_memLp seed) time)‖^2=
        ∫sample,a (time-sample)^2*‖fiber M [j] (original seed sample)‖^2 := by
  let v:=NativeWindowAbsoluteTimeCarrier.field a aMem (original seed)
    (NativeWindowAbsoluteTimeSource.original_memLp seed) time
  rw [norm_square (E := wholePhysical)]
  apply integral_congr_ae
  filter_upwards [(fiber M [j]).coeFn_compLpL (μ := (volume : Measure ℝ)) v,
    NativeWindowAbsoluteTimeCarrier.field_ae a aMem (original seed)
      (NativeWindowAbsoluteTimeSource.original_memLp seed) time] with sample acted raw
  change spatial M j v sample=fiber M [j] (v sample) at acted
  change v sample=a (time-sample) • original seed sample at raw
  change ‖spatial M j v sample‖^2=_
  rw [acted,raw,map_smul,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]

theorem field_integrable (a : ℝ → ℝ) (aMem : MemLp a 2 (volume : Measure ℝ))
    (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ) :
    Integrable (fun sample => a (time-sample)^2*‖fiber M [j] (original seed sample)‖^2) volume := by
  let v:=NativeWindowAbsoluteTimeCarrier.field a aMem (original seed)
    (NativeWindowAbsoluteTimeSource.original_memLp seed) time
  apply ((Lp.memLp (spatial M j v)).integrable_norm_pow (by norm_num : (2:ℕ)≠0)).congr
  filter_upwards [(fiber M [j]).coeFn_compLpL (μ := (volume : Measure ℝ)) v,
    NativeWindowAbsoluteTimeCarrier.field_ae a aMem (original seed)
      (NativeWindowAbsoluteTimeSource.original_memLp seed) time] with sample acted raw
  change spatial M j v sample=fiber M [j] (v sample) at acted
  change v sample=a (time-sample) • original seed sample at raw
  rw [acted,raw,map_smul,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]

theorem source_field_bound (a : ℝ → ℝ) (aMem : MemLp a 2 (volume : Measure ℝ))
    (supported : ∀ x,x∉Icc (-2:ℝ) (-1) → a x=0)
    (C : ℝ) (bounded : ∀ x,‖a x‖ ≤ C)
    (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ) (j : Coordinate)
    (time : ℝ) (inside : time∈Icc 0 horizon) :
    ‖spatial M j (NativeWindowAbsoluteTimeCarrier.field a aMem (original seed)
      (NativeWindowAbsoluteTimeSource.original_memLp seed) time)‖^2 ≤
        (C^2/nu.coeff)*energyBudget seed horizon := by
  classical
  let F:=fun sample : ℝ => a (time-sample)^2*‖fiber M [j] (original seed sample)‖^2
  let G:=fun sample : ℝ => (C^2/nu.coeff)*pointEnergy seed M sample
  have Gint:IntegrableOn G (Icc (time+1) (time+2)) volume :=
    ((NativeWindowHistoryCrossBudget.pointEnergy_continuous seed M).const_mul (C^2/nu.coeff)).continuousOn.integrableOn_compact isCompact_Icc
  have majorant:Integrable ((Icc (time+1) (time+2)).indicator G) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr Gint
  have dom (sample : ℝ) : F sample ≤ (Icc (time+1) (time+2)).indicator G sample := by
    by_cases member:sample∈Icc (time+1) (time+2)
    · rw [Set.indicator_of_mem member]
      have square : a (time-sample)^2 ≤ C^2 := by
        simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg _) (bounded (time-sample)) 2
      have first:=mul_le_mul_of_nonneg_right square (sq_nonneg ‖fiber M [j] (original seed sample)‖)
      have lower:‖fiber M [j] (original seed sample)‖^2 ≤ pointEnergy seed M sample/nu.coeff :=
        (le_div_iff₀ nu.coeff_pos).mpr (by nlinarith only [point_spatial seed M j sample])
      have last:=mul_le_mul_of_nonneg_left lower (sq_nonneg C)
      change _ ≤ (C^2/nu.coeff)*pointEnergy seed M sample
      exact first.trans (last.trans_eq (by ring))
    · have outside:time-sample∉Icc (-2:ℝ) (-1) := by
        intro belongs
        apply member
        constructor <;> linarith [belongs.1,belongs.2]
      simp only [F,supported _ outside,zero_pow (by decide : (2:ℕ)≠0),zero_mul,
        Set.indicator_of_notMem member,le_refl]
  have paid:=integral_mono_ae (field_integrable a aMem seed M j time) majorant (Eventually.of_forall dom)
  rw [field_square]
  have window:∫sample,(Icc (time+1) (time+2)).indicator G sample=
      (C^2/nu.coeff)*(∫sample in time+1..time+2,pointEnergy seed M sample) := by
    rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : time+1 ≤ time+2),intervalIntegral.integral_const_mul]
  exact paid.trans (window.trans_le (mul_le_mul_of_nonneg_left
    (NativeWindowHistoryCrossBudget.source_window_energy seed horizon M time inside)
    (div_nonneg (sq_nonneg C) nu.coeff_pos.le)))

theorem source_rate_spatial_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧∀ M j,∀ time∈Icc 0 horizon,
      ‖spatial M j (rate seed time)‖^2 ≤ C := by
  obtain ⟨C,_,bounded⟩:=NativeWindowKernelHalfDensity.source_derivative_bound
  refine ⟨max 0 ((C^2/nu.coeff)*energyBudget seed horizon),le_max_left _ _,fun M j time inside => ?_⟩
  exact (source_field_bound (deriv rootKernel) (NativeWindowKernelHalfDensity.derivative_memLp 2)
    NativeWindowAbsoluteTimeSource.rate_zero_outside C bounded seed horizon M j time inside).trans (le_max_right _ _)

theorem source_spatial_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (j : Coordinate) (time : ℝ) :
    HasDerivAt (fun t => spatial M j (history seed t)) (spatial M j (rate seed time)) time :=
  HasFDerivAt.comp_hasDerivAt (E := H) (F := H) time (spatial M j).hasFDerivAt
    (NativeWindowAbsoluteTimeSource.source_hasDerivAt seed time)

end
end SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimeGradient
