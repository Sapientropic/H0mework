import H0mework.Versions.X.NavierStokes.WindowSourceGreen.MassReciprocal

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowMassField
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open NativePhysicalFourier (Torus)
open NativeWindowMassReciprocal (value value_nonnegative value_bound)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

abbrev State := Lp PhysicalSpace 2 (volume : Measure Torus)
abbrev Scalar (p : ℝ≥0∞) := Lp ℝ p (volume : Measure Torus)

theorem value_memLp (v : State) (p : ℝ≥0∞) : MemLp (fun x => value (v x)) p (volume : Measure Torus) :=
  MemLp.of_bound (NativeWindowMassReciprocal.value_continuous.comp_aestronglyMeasurable (Lp.memLp v).1) (1/2)
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (value_nonnegative _)]; exact value_bound _)

def field (p : ℝ≥0∞) (v : State) : Scalar p := (value_memLp v p).toLp (fun x => value (v x))

theorem field_ae (p : ℝ≥0∞) (v : State) : field p v=ᵐ[volume] fun x => value (v x) :=
  (value_memLp v p).coeFn_toLp

def coefficientValue (v : PhysicalSpace) : ℝ := -(value v)^2/4

theorem coefficient_memLp (v : State) : MemLp (fun x => coefficientValue (v x)) ∞ (volume : Measure Torus) := by
  apply MemLp.of_bound (C := 1/16)
  · apply Continuous.comp_aestronglyMeasurable _ (Lp.memLp v).1
    exact ((NativeWindowMassReciprocal.value_continuous.pow 2).neg).div_const 4
  · filter_upwards with x
    change ‖-(value (v x))^2/4‖≤1/16
    rw [norm_div,norm_neg,Real.norm_eq_abs,abs_sq]
    norm_num only [Real.norm_ofNat]
    nlinarith only [value_nonnegative (v x),value_bound (v x)]

def coefficient (v : State) : Scalar ∞ :=
  (coefficient_memLp v).toLp (fun x => coefficientValue (v x))

theorem coefficient_ae (v : State) : coefficient v=ᵐ[volume] fun x => coefficientValue (v x) :=
  (coefficient_memLp v).coeFn_toLp

def pair : State →L[ℝ] State →L[ℝ] Scalar 1 := (innerSL ℝ (E := PhysicalSpace)).holderL volume 2 2 1

def derivative (v : State) : State →L[ℝ] Scalar 1 :=
  ((ContinuousLinearMap.mul ℝ ℝ).holderL volume ∞ 1 1 (coefficient v)).comp (pair v)

theorem derivative_ae (v h : State) : derivative v h=ᵐ[volume]
    fun x => NativeWindowMassReciprocal.derivative (v x) (h x) := by
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 1) (coefficient v) (pair v h),
    coefficient_ae v,(innerSL ℝ (E := PhysicalSpace)).coeFn_holder (r := 1) v h] with x applied coeff paired
  change derivative v h x=_ at applied
  change pair v h x=inner ℝ (v x) (h x) at paired
  rw [applied,coeff,paired]
  rfl

theorem remainder_bound (v h : State) : ‖field 1 (v+h)-field 1 v-derivative v h‖≤‖h‖^2/16 := by
  let error:=field 1 (v+h)-field 1 v-derivative v h
  have actual : error=ᵐ[volume] fun x => value (v x+h x)-value (v x)-NativeWindowMassReciprocal.derivative (v x) (h x) := by
    filter_upwards [Lp.coeFn_sub (field 1 (v+h)-field 1 v) (derivative v h),
      Lp.coeFn_sub (field 1 (v+h)) (field 1 v),field_ae 1 (v+h),field_ae 1 v,
      derivative_ae v h,Lp.coeFn_add v h] with x diff source first last action sum
    change error x=_ at diff
    rw [diff,Pi.sub_apply,source,Pi.sub_apply,first,last,action,sum,Pi.add_apply]
  have paid : Integrable (fun x : Torus => ‖h x‖^2/16) :=
    ((Lp.memLp h).integrable_norm_pow (by norm_num : (2:ℕ)≠0)).div_const 16
  have bounded : ∀ᵐ x : Torus,‖error x‖≤‖h x‖^2/16 := by
    filter_upwards [actual] with x same
    rw [same,Real.norm_eq_abs]
    exact NativeWindowMassReciprocal.taylor_bound (v x) (h x)
  change ‖error‖≤_
  rw [L1.norm_eq_integral_norm]
  calc
    _≤∫ x : Torus,‖h x‖^2/16 := integral_mono_ae (memLp_one_iff_integrable.mp (Lp.memLp error)).norm paid bounded
    _=‖h‖^2/16 := by
      simp only [div_eq_mul_inv,integral_mul_const]
      rw [← real_inner_self_eq_norm_sq,L2.inner_def]
      simp only [real_inner_self_eq_norm_sq]

theorem hasFDerivAt (v : State) : HasFDerivAt (field 1) (derivative v) v := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro epsilon positive
  have small : ∀ᶠ h : State in 𝓝 0,‖h‖<16*epsilon :=
    (continuous_norm.continuousAt.tendsto).eventually (gt_mem_nhds (by simpa using mul_pos (by norm_num : (0:ℝ)<16) positive))
  filter_upwards [small] with h bounded
  have paid:=remainder_bound v h
  have normPositive:=norm_nonneg h
  nlinarith only [paid,bounded,normPositive,mul_nonneg normPositive (sub_nonneg.mpr bounded.le)]

end
end SaturationMonoid.NavierStokes.NativeWindowMassField
