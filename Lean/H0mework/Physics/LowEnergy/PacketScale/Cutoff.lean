import H0mework.Physics.LowEnergy.PacketField.Spatial
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! A scale acts on the same physical Fourier field by an actual L²
orthogonal cutoff. Neither the original packet nor its norm is changed. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace Classical
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketScale
open FullQuantum FullSpace PacketField
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def scaleSet (radius : ℝ) : Set Position := {frequency | ‖(2*Real.pi) • frequency‖≤radius}

theorem scaleSet_measurable (radius : ℝ) : MeasurableSet (scaleSet radius) :=
  (isClosed_le (by fun_prop) continuous_const).measurableSet

def cutoffValue (radius : ℝ) (field : FieldSpace E) : FieldSpace E :=
  ((Lp.memLp field).indicator (scaleSet_measurable radius)).toLp _

omit [NormedSpace ℂ E] in
theorem cutoffValue_ae (radius : ℝ) (field : FieldSpace E) :
    cutoffValue radius field=ᵐ[volume] fun frequency =>
      if frequency∈scaleSet radius then field frequency else 0 :=
  ((Lp.memLp field).indicator (scaleSet_measurable radius)).coeFn_toLp

def cutoffLinear (radius : ℝ) : FieldSpace E →ₗ[ℂ] FieldSpace E where
  toFun := cutoffValue radius
  map_add' left right := by
    apply Lp.ext
    filter_upwards [cutoffValue_ae radius (left+right),cutoffValue_ae radius left,
      cutoffValue_ae radius right,Lp.coeFn_add left right,
      Lp.coeFn_add (cutoffValue radius left) (cutoffValue radius right)] with frequency both first second source target
    rw [both,target]
    simp only [Pi.add_apply]
    rw [first,second]
    by_cases inside : frequency∈scaleSet radius
    · simp only [if_pos inside,source,Pi.add_apply]
    · simp only [if_neg inside,add_zero]
  map_smul' scalar field := by
    apply Lp.ext
    filter_upwards [cutoffValue_ae radius (scalar • field),cutoffValue_ae radius field,
      Lp.coeFn_smul scalar field,Lp.coeFn_smul scalar (cutoffValue radius field)] with frequency both original source target
    simp only [RingHom.id_apply]
    rw [both,target]
    simp only [Pi.smul_apply]
    rw [original]
    by_cases inside : frequency∈scaleSet radius
    · simp only [if_pos inside,source,Pi.smul_apply]
    · simp only [if_neg inside,smul_zero]

omit [NormedSpace ℂ E] in
theorem cutoffValue_bound (radius : ℝ) (field : FieldSpace E) : ‖cutoffValue radius field‖≤‖field‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [cutoffValue_ae radius field] with frequency value
  rw [value]
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (field frequency)

def cutoff (radius : ℝ) : FieldSpace E →L[ℂ] FieldSpace E :=
  (cutoffLinear radius).mkContinuous 1 (fun field => by
    change ‖cutoffValue radius field‖≤1*‖field‖
    simpa only [one_mul] using cutoffValue_bound radius field)

theorem cutoff_ae (radius : ℝ) (field : FieldSpace E) :
    cutoff radius field=ᵐ[volume] fun frequency =>
      if frequency∈scaleSet radius then field frequency else 0 := cutoffValue_ae radius field

theorem cutoff_bound (radius : ℝ) (field : FieldSpace E) : ‖cutoff radius field‖≤‖field‖ := cutoffValue_bound radius field

theorem cutoff_nested (first second : ℝ) (field : FieldSpace E) :
    cutoff first (cutoff second field)=cutoff (min first second) field := by
  apply Lp.ext
  filter_upwards [cutoff_ae first (cutoff second field),cutoff_ae second field,
    cutoff_ae (min first second) field] with frequency outer inner both
  rw [outer,both]
  by_cases inFirst : frequency∈scaleSet first
  · rw [if_pos inFirst,inner]
    by_cases inSecond : frequency∈scaleSet second
    · have inBoth : frequency∈scaleSet (min first second) := by
        change ‖(2*Real.pi) • frequency‖ ≤ min first second
        exact le_min inFirst inSecond
      rw [if_pos inSecond,if_pos inBoth]
    · have outside : frequency∉scaleSet (min first second) := by
        intro h
        apply inSecond
        exact le_trans h (min_le_right first second)
      rw [if_neg inSecond,if_neg outside]
  · have outside : frequency∉scaleSet (min first second) := by
      intro h
      apply inFirst
      exact le_trans h (min_le_left first second)
    rw [if_neg inFirst,if_neg outside]

theorem cutoff_idempotent (radius : ℝ) (field : FieldSpace E) :
    cutoff radius (cutoff radius field)=cutoff radius field := by rw [cutoff_nested,min_self]

def shell (innerRadius outerRadius : ℝ) : FieldSpace E →L[ℂ] FieldSpace E := cutoff outerRadius-cutoff innerRadius

theorem shell_decomposition (innerRadius outerRadius : ℝ) (field : FieldSpace E) :
    cutoff outerRadius field=cutoff innerRadius field+shell innerRadius outerRadius field := by
  change cutoff outerRadius field=cutoff innerRadius field+(cutoff outerRadius field-cutoff innerRadius field)
  abel

theorem shell_ae (innerRadius outerRadius : ℝ) (ordered : innerRadius≤outerRadius) (field : FieldSpace E) :
    shell innerRadius outerRadius field=ᵐ[volume] fun frequency =>
      if frequency∈scaleSet outerRadius ∧ frequency∉scaleSet innerRadius then field frequency else 0 := by
  filter_upwards [cutoff_ae innerRadius field,cutoff_ae outerRadius field,
    Lp.coeFn_sub (cutoff outerRadius field) (cutoff innerRadius field)] with frequency small large difference
  change (cutoff outerRadius field-cutoff innerRadius field) frequency=_
  rw [difference]
  simp only [Pi.sub_apply]
  rw [small,large]
  by_cases inside : frequency∈scaleSet innerRadius
  · have bigger : frequency∈scaleSet outerRadius := inside.trans ordered
    simp [inside,bigger]
  · simp [inside]

section Inner
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem cutoff_selfAdjoint (radius : ℝ) (left right : FieldSpace F) :
    inner ℂ (cutoff radius left) right=inner ℂ left (cutoff radius right) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cutoff_ae radius left,cutoff_ae radius right] with frequency first second
  rw [first,second]
  split_ifs <;> simp

theorem shell_low_orthogonal (innerRadius outerRadius : ℝ) (ordered : innerRadius≤outerRadius)
    (left right : FieldSpace F) : inner ℂ (cutoff innerRadius left) (shell innerRadius outerRadius right)=0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [cutoff_ae innerRadius left,shell_ae innerRadius outerRadius ordered right] with frequency small large
  rw [small,large]
  by_cases inside : frequency∈scaleSet innerRadius <;> simp [inside]

theorem low_shell_orthogonal (innerRadius outerRadius : ℝ) (ordered : innerRadius≤outerRadius)
    (left right : FieldSpace F) : inner ℂ (shell innerRadius outerRadius left) (cutoff innerRadius right)=0 := by
  rw [← inner_conj_symm]
  rw [shell_low_orthogonal innerRadius outerRadius ordered right left,map_zero]

end Inner
end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketScale
