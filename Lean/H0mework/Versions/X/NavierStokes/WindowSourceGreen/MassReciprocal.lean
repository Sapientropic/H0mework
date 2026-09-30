import H0mework.Versions.X.NavierStokes.WindowSourceGreen.SpatialForm
import Mathlib.MeasureTheory.Function.Holder

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowMassReciprocal
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open NativeCanonicalFluidCoframe (density density_pos)
noncomputable section

def value (v : PhysicalSpace) : ℝ := (density v)⁻¹

theorem density_lower (v : PhysicalSpace) : 2≤density v := by
  unfold density
  linarith only [sq_nonneg ‖v‖]

theorem norm_density (v : PhysicalSpace) : ‖v‖≤density v := by
  unfold density
  nlinarith only [sq_nonneg (‖v‖-4)]

theorem value_nonnegative (v : PhysicalSpace) : 0≤value v := (inv_pos.mpr (density_pos v)).le

theorem value_bound (v : PhysicalSpace) : value v≤1/2 := by
  simpa only [value,one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) (density_lower v)

theorem value_continuous : Continuous value := by
  apply Continuous.inv₀
  · unfold density
    fun_prop
  · exact fun v => (density_pos v).ne'

theorem difference (u v : PhysicalSpace) : value u-value v=(density v-density u)/(density u*density v) := by
  unfold value
  field_simp [(density_pos u).ne',(density_pos v).ne']

theorem lipschitz_bound (u v : PhysicalSpace) : |value u-value v|≤‖u-v‖/8 := by
  have sum:‖u‖+‖v‖≤density u*density v := by
    have first:=norm_density u
    have last:=norm_density v
    have lowFirst:=density_lower u
    have lowLast:=density_lower v
    nlinarith only [first,last,lowFirst,lowLast,mul_nonneg (sub_nonneg.mpr lowFirst) (sub_nonneg.mpr lowLast)]
  have read:density v-density u=(‖v‖-‖u‖)*(‖v‖+‖u‖)/8 := by unfold density; ring
  rw [difference,abs_div,abs_of_pos (mul_pos (density_pos u) (density_pos v)),read,
    abs_div,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg v) (norm_nonneg u))]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<8)]
  apply (div_le_iff₀ (mul_pos (density_pos u) (density_pos v))).mpr
  have changeNorm:|‖v‖-‖u‖|≤‖u-v‖ := (abs_norm_sub_norm_le v u).trans_eq (norm_sub_rev v u)
  calc
    _≤‖u-v‖*(‖v‖+‖u‖)/8 := by gcongr
    _≤‖u-v‖*(density u*density v)/8 := by gcongr; linarith only [sum]
    _=_ := by ring

def derivative (v : PhysicalSpace) : PhysicalSpace →L[ℝ] ℝ :=
  (-(value v)^2/4) • innerSL ℝ v

theorem derivative_apply (v h : PhysicalSpace) : derivative v h=-(value v)^2/4*inner ℝ v h := rfl

theorem derivative_bound (v h : PhysicalSpace) : |derivative v h|≤‖h‖/8 := by
  have scalar:‖v‖/(4*density v^2)≤1/8 := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<4) (sq_pos_of_pos (density_pos v)))).mpr
    nlinarith only [norm_density v,density_lower v,sq_nonneg (density v-2)]
  have read:derivative v h=-(inner ℝ v h)/(4*density v^2) := by
    rw [derivative_apply,value]
    field_simp [(density_pos v).ne']
  rw [read,abs_div,abs_neg,abs_of_pos (mul_pos (by norm_num) (sq_pos_of_pos (density_pos v)))]
  calc
    _≤(‖v‖*‖h‖)/(4*density v^2) :=
      div_le_div_of_nonneg_right (abs_real_inner_le_norm v h) (by positivity [density_pos v])
    _=(‖v‖/(4*density v^2))*‖h‖ := by ring
    _≤(1/8:ℝ)*‖h‖ := mul_le_mul_of_nonneg_right scalar (norm_nonneg h)
    _=_ := by ring

theorem taylor_identity (v h : PhysicalSpace) :
    value (v+h)-value v-derivative v h=
      (inner ℝ v h)/(4*density v)*(value v-value (v+h))-
        ‖h‖^2/(8*density v*density (v+h)) := by
  rw [derivative_apply]
  have expansion:density (v+h)=density v+inner ℝ v h/4+‖h‖^2/8 := by
    unfold density
    rw [norm_add_sq_real]
    ring
  unfold value
  field_simp [(density_pos v).ne',(density_pos (v+h)).ne']
  rw [expansion]
  ring

theorem taylor_bound (v h : PhysicalSpace) :
    |value (v+h)-value v-derivative v h|≤‖h‖^2/16 := by
  have left:|(inner ℝ v h)/(4*density v)|≤‖h‖/4 := by
    rw [abs_div,abs_of_pos (mul_pos (by norm_num) (density_pos v))]
    apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<4) (density_pos v))).mpr
    exact (abs_real_inner_le_norm v h).trans ((mul_le_mul_of_nonneg_right (norm_density v) (norm_nonneg h)).trans_eq (by ring))
  have difference:|value v-value (v+h)|≤‖h‖/8 := by
    simpa only [sub_add_cancel_left,norm_neg] using lipschitz_bound v (v+h)
  have right:|‖h‖^2/(8*density v*density (v+h))|≤‖h‖^2/32 := by
    rw [abs_div,abs_sq,abs_of_pos (mul_pos (mul_pos (by norm_num) (density_pos v)) (density_pos (v+h)))]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num : (0:ℝ)<32)
    nlinarith only [density_lower v,density_lower (v+h),
      mul_nonneg (sub_nonneg.mpr (density_lower v)) (sub_nonneg.mpr (density_lower (v+h)))]
  rw [taylor_identity]
  calc
    _≤|(inner ℝ v h)/(4*density v)*(value v-value (v+h))|+
        |‖h‖^2/(8*density v*density (v+h))| := abs_sub _ _
    _=|(inner ℝ v h)/(4*density v)| * |value v-value (v+h)|+
        |‖h‖^2/(8*density v*density (v+h))| := by rw [abs_mul]
    _≤(‖h‖/4)*(‖h‖/8)+‖h‖^2/32 :=
      add_le_add (mul_le_mul left difference (abs_nonneg _) (by positivity)) right
    _=_ := by ring

end
end SaturationMonoid.NavierStokes.NativeWindowMassReciprocal
