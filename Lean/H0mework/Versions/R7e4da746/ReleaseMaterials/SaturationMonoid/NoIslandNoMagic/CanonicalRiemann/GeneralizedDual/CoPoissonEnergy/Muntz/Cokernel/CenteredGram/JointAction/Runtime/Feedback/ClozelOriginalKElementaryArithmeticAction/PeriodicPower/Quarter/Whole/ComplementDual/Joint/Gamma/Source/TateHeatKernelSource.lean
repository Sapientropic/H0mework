import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KappaConductorSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.TateGaussianClock
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace
import H0mework.Versions.R7e4da746.Arithmetic.MellinTateSource.Isometry
import H0mework.Versions.R7e4da746.Arithmetic.MellinTateSource.L2Raw

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.TateConductor
open Complex Filter FourierTransform MeasureTheory Set
open scoped Topology InnerProductSpace ENNReal
noncomputable section
local notation "T" => burnolTateReciprocalL2

macro "heatPaid% " field:ident : term => do
  let owner := Lean.Name.num `_private.H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.TateGaussianClock 0
  let scope := `SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalGamma.Source.TateConductor
  return Lean.mkIdent (owner.append (scope.append field.getId))

private theorem heat_kernel_real (time z : ℝ) :
    heatKernel time z = (‖heatKernel time z‖ : ℂ) := by
  change ((Real.sqrt (Real.pi / time) * Real.exp (-(Real.pi ^ 2 * z ^ 2 / time)) : ℝ) : ℂ) =
    (‖((Real.sqrt (Real.pi / time) * Real.exp (-(Real.pi ^ 2 * z ^ 2 / time)) : ℝ) : ℂ)‖ : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)]

private theorem heat_kernel_measured (time : ℝ) : Measurable (heatKernel time) := by
  change Measurable (fun z : ℝ =>
    ((Real.sqrt (Real.pi / time) * Real.exp (-(Real.pi ^ 2 * z ^ 2 / time)) : ℝ) : ℂ))
  fun_prop

private theorem heat_row_mem (time : ℝ) (positive : 0 < time) (x : ℝ) :
    MemLp (fun y : ℝ => heatKernel time (x - y)) 2 volume := by
  have source := (((gaussianPaid% sourceHeat) time positive).memLp 2 volume).comp_measurePreserving
    (volume.measurePreserving_sub_left x)
  convert source using 1
  funext y
  exact ((gaussianPaid% source_heat_physical) time positive (x-y)).symm

def heatKernelVector (time : ℝ) (positive : 0 < time) (x : ℝ) : BurnolL2 :=
  (heat_row_mem time positive x).toLp (fun y : ℝ => heatKernel time (x-y))

private theorem heat_row_raw (time : ℝ) (positive : 0 < time) (x : ℝ) :
    (heatKernelVector time positive x : ℝ → ℂ) =ᵐ[volume]
      fun y : ℝ => heatKernel time (x-y) := MemLp.coeFn_toLp _

private theorem heat_row_pairing (time : ℝ) (positive : 0 < time) (x : ℝ) (v : BurnolL2) :
    inner ℂ (heatKernelVector time positive x) v =
      ∫ y : ℝ, heatKernel time (x-y) * v y := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [heat_row_raw time positive x] with y raw
  rw [raw, RCLike.inner_apply]
  rw [starRingEnd_apply, heatPaid% heat_kernel_star, mul_comm]

private theorem heat_row_integrable (time : ℝ) (positive : 0 < time) (x : ℝ) (v : BurnolL2) :
    Integrable (fun y : ℝ => heatKernel time (x-y) * v y) := by
  apply (L2.integrable_inner (𝕜 := ℂ) (heatKernelVector time positive x) v).congr
  filter_upwards [heat_row_raw time positive x] with y raw
  rw [raw, RCLike.inner_apply]
  rw [starRingEnd_apply, heatPaid% heat_kernel_star, mul_comm]

private theorem physical_heat_row (time : ℝ) (positive : 0 < time) (v : BurnolL2) :
    (physicalHeatValue time v : ℝ → ℂ) =ᵐ[volume]
      fun x : ℝ => inner ℂ (heatKernelVector time positive x) v := by
  filter_upwards [original_physical_heat_raw time positive v] with x raw
  rw [raw, heat_row_pairing]
  have shifted := integral_sub_left_eq_self
    (fun y : ℝ => heatKernel time (x-y) * v y) volume x
  simpa only [sub_sub_cancel] using shifted

private theorem tate_inner (v w : BurnolL2) : inner ℂ (T v) (T w) = inner ℂ v w := by
  let actual : BurnolL2 →ₗᵢ[ℂ] BurnolL2 :=
    ⟨burnolTateReciprocalL2.toLinearMap, burnolTateReciprocalValue_norm⟩
  exact actual.inner_map_map v w

private theorem tate_pairing (v w : BurnolL2) : inner ℂ (T v) w = inner ℂ v (T w) := by
  simpa only [burnolTateReciprocalL2_involutive] using tate_inner v (T w)

def reciprocalHeatKernelVector (time : ℝ) (positive : 0 < time) (x : ℝ) : BurnolL2 :=
  (Complex.ofReal |x|)⁻¹ • T (heatKernelVector time positive x⁻¹)

private theorem reciprocal_row_raw (time : ℝ) (positive : 0 < time) (x : ℝ) :
    (reciprocalHeatKernelVector time positive x : ℝ → ℂ) =ᵐ[volume]
      fun y : ℝ => reciprocalHeat time x y := by
  have pulled := burnolTateReciprocalRaw_ae_congr
    (Lp.memLp (heatKernelVector time positive x⁻¹)) (heat_row_mem time positive x⁻¹)
    (heat_row_raw time positive x⁻¹)
  filter_upwards [Lp.coeFn_smul (Complex.ofReal |x|)⁻¹ (T (heatKernelVector time positive x⁻¹)),
    burnolTateReciprocalL2_coeFn (heatKernelVector time positive x⁻¹), pulled]
    with y scalar outer raw
  change ((Complex.ofReal |x|)⁻¹ • T (heatKernelVector time positive x⁻¹)) y = _
  rw [scalar, Pi.smul_apply, smul_eq_mul, outer, raw]
  unfold burnolTateReciprocalRaw reciprocalHeat
  ring

private theorem reciprocal_kernel_real (time x y : ℝ) :
    reciprocalHeat time x y = (‖reciprocalHeat time x y‖ : ℂ) := by
  unfold reciprocalHeat
  rw [norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_abs, abs_abs,
    heat_kernel_real time (x⁻¹-y⁻¹)]
  push_cast
  simp only [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]

private theorem reciprocal_row_pairing (time : ℝ) (positive : 0 < time) (x : ℝ) (v : BurnolL2) :
    inner ℂ (reciprocalHeatKernelVector time positive x) v =
      ∫ y : ℝ, reciprocalHeat time x y * v y := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [reciprocal_row_raw time positive x] with y raw
  rw [raw, RCLike.inner_apply, reciprocal_kernel_real]
  simp [mul_comm]

private theorem reciprocal_row_integrable (time : ℝ) (positive : 0 < time) (x : ℝ) (v : BurnolL2) :
    Integrable (fun y : ℝ => reciprocalHeat time x y * v y) := by
  apply (L2.integrable_inner (𝕜 := ℂ) (reciprocalHeatKernelVector time positive x) v).congr
  filter_upwards [reciprocal_row_raw time positive x] with y raw
  rw [raw, RCLike.inner_apply, reciprocal_kernel_real]
  simp [mul_comm]

private theorem reciprocal_heat_row (time : ℝ) (positive : 0 < time) (v : BurnolL2) :
    (T (physicalHeatValue time (T v)) : ℝ → ℂ) =ᵐ[volume]
      fun x : ℝ => inner ℂ (reciprocalHeatKernelVector time positive x) v := by
  have raw := physical_heat_row time positive (T v)
  have pulled := burnolTateReciprocalRaw_ae_congr
    (Lp.memLp (physicalHeatValue time (T v))) ((Lp.memLp _).ae_eq raw) raw
  filter_upwards [burnolTateReciprocalL2_coeFn (physicalHeatValue time (T v)), pulled]
    with x outer source
  rw [outer, source]
  unfold burnolTateReciprocalRaw reciprocalHeatKernelVector
  rw [inner_smul_left, starRingEnd_apply]
  change (Complex.ofReal |x|)⁻¹ * inner ℂ (heatKernelVector time positive x⁻¹) (T v) =
    star ((Complex.ofReal |x|)⁻¹) * inner ℂ (T (heatKernelVector time positive x⁻¹)) v
  have scalar : star ((Complex.ofReal |x|)⁻¹) = (Complex.ofReal |x|)⁻¹ := by simp
  rw [scalar, tate_pairing]

private def normField (v : BurnolL2) : BurnolL2 :=
  ((Lp.memLp v).norm.ofReal : MemLp (fun x : ℝ => (‖v x‖ : ℂ)) 2 volume).toLp
    (fun x : ℝ => (‖v x‖ : ℂ))

private theorem norm_field_raw (v : BurnolL2) :
    (normField v : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => (‖v x‖ : ℂ) := MemLp.coeFn_toLp _

private theorem norm_field_norm (v : BurnolL2) : ‖normField v‖ = ‖v‖ := by
  apply le_antisymm
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [norm_field_raw v] with x raw
    rw [raw, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [norm_field_raw v] with x raw
    rw [raw, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]

private theorem heat_norm_row (time : ℝ) (positive : 0 < time) (v : BurnolL2) (x : ℝ) :
    ‖inner ℂ (heatKernelVector time positive x) (normField v)‖ =
      ∫ y : ℝ, ‖heatKernel time (x-y)‖ * ‖v y‖ := by
  have point : inner ℂ (heatKernelVector time positive x) (normField v) =
      ((∫ y : ℝ, ‖heatKernel time (x-y)‖ * ‖v y‖ : ℝ) : ℂ) := by
    rw [heat_row_pairing, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [norm_field_raw v] with y raw
    rw [raw]
    conv_lhs => rw [heat_kernel_real]
    push_cast
    rfl
  rw [point, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg (fun y => by positivity))]

private theorem reciprocal_norm_row (time : ℝ) (positive : 0 < time) (v : BurnolL2) (x : ℝ) :
    ‖inner ℂ (reciprocalHeatKernelVector time positive x) (normField v)‖ =
      ∫ y : ℝ, ‖reciprocalHeat time x y‖ * ‖v y‖ := by
  have point : inner ℂ (reciprocalHeatKernelVector time positive x) (normField v) =
      ((∫ y : ℝ, ‖reciprocalHeat time x y‖ * ‖v y‖ : ℝ) : ℂ) := by
    rw [reciprocal_row_pairing, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [norm_field_raw v] with y raw
    rw [raw]
    conv_lhs => rw [reciprocal_kernel_real]
    push_cast
    rfl
  rw [point, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg (fun y => by positivity))]

private theorem heat_whole_section_norm (time : ℝ) (positive : 0 < time) (left v : BurnolL2) :
    (fun x : ℝ => ∫ y : ℝ, ‖star (left x) * v y * heatKernel time (x-y)‖) =ᵐ[volume]
      fun x : ℝ => ‖left x‖ * ‖physicalHeatValue time (normField v) x‖ := by
  filter_upwards [physical_heat_row time positive (normField v)] with x raw
  calc
    _ = ‖left x‖ * ∫ y : ℝ, ‖heatKernel time (x-y)‖ * ‖v y‖ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      simp only [norm_mul, norm_star]
      ring
    _ = _ := by rw [← heat_norm_row time positive v x, ← raw]

private theorem reciprocal_whole_section_norm (time : ℝ) (positive : 0 < time) (left v : BurnolL2) :
    (fun x : ℝ => ∫ y : ℝ, ‖star (left x) * v y * reciprocalHeat time x y‖) =ᵐ[volume]
      fun x : ℝ => ‖left x‖ * ‖T (physicalHeatValue time (T (normField v))) x‖ := by
  filter_upwards [reciprocal_heat_row time positive (normField v)] with x raw
  calc
    _ = ‖left x‖ * ∫ y : ℝ, ‖reciprocalHeat time x y‖ * ‖v y‖ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      simp only [norm_mul, norm_star]
      ring
    _ = _ := by rw [← reciprocal_norm_row time positive v x, ← raw]

theorem original_heat_whole_integrable (time : ℝ) (positive : 0 < time) (left v : BurnolL2) :
    Integrable (fun xy : ℝ × ℝ => star (left xy.1) * v xy.2 * heatKernel time (xy.1-xy.2))
      (volume.prod volume) := by
  have measured : Measurable (fun xy : ℝ × ℝ =>
      star (left xy.1) * v xy.2 * heatKernel time (xy.1-xy.2)) := by
    exact (((Lp.stronglyMeasurable left).star.measurable.comp measurable_fst).mul
      ((Lp.stronglyMeasurable v).measurable.comp measurable_snd)).mul
      ((heat_kernel_measured time).comp (by fun_prop))
  apply (integrable_prod_iff measured.aestronglyMeasurable).mpr
  constructor
  · filter_upwards with x
    apply ((heat_row_integrable time positive x v).const_mul (star (left x))).congr
    filter_upwards with y
    ring
  · exact ((heatPaid% norm_product_integrable) left (physicalHeatValue time (normField v))).congr
      (heat_whole_section_norm time positive left v).symm

theorem original_reciprocal_heat_whole_integrable (time : ℝ) (positive : 0 < time) (left v : BurnolL2) :
    Integrable (fun xy : ℝ × ℝ => star (left xy.1) * v xy.2 * reciprocalHeat time xy.1 xy.2)
      (volume.prod volume) := by
  have measured : Measurable (fun xy : ℝ × ℝ =>
      star (left xy.1) * v xy.2 * reciprocalHeat time xy.1 xy.2) := by
    exact (((Lp.stronglyMeasurable left).star.measurable.comp measurable_fst).mul
      ((Lp.stronglyMeasurable v).measurable.comp measurable_snd)).mul
      ((((continuous_abs.measurable.comp measurable_fst).complex_ofReal.inv).mul
        ((continuous_abs.measurable.comp measurable_snd).complex_ofReal.inv)).mul
        ((heat_kernel_measured time).comp (measurable_fst.inv.sub measurable_snd.inv)))
  apply (integrable_prod_iff measured.aestronglyMeasurable).mpr
  constructor
  · filter_upwards with x
    apply ((reciprocal_row_integrable time positive x v).const_mul (star (left x))).congr
    filter_upwards with y
    ring
  · exact ((heatPaid% norm_product_integrable) left (T (physicalHeatValue time (T (normField v))))).congr
      (reciprocal_whole_section_norm time positive left v).symm

theorem original_heat_whole_norm (time : ℝ) (positive : 0 < time) (left v : BurnolL2) :
    (∫ x : ℝ, ∫ y : ℝ, ‖star (left x) * v y * heatKernel time (x-y)‖) ≤ ‖left‖ * ‖v‖ := by
  rw [integral_congr_ae (heat_whole_section_norm time positive left v)]
  calc
    _ ≤ ‖left‖ * ‖physicalHeatValue time (normField v)‖ :=
      (heatPaid% norm_product_bound) left (physicalHeatValue time (normField v))
    _ ≤ ‖left‖ * ‖normField v‖ := by
      gcongr
      exact original_physical_heat_norm time positive (normField v)
    _ = _ := by rw [norm_field_norm]

theorem original_reciprocal_heat_whole_norm (time : ℝ) (positive : 0 < time) (left v : BurnolL2) :
    (∫ x : ℝ, ∫ y : ℝ, ‖star (left x) * v y * reciprocalHeat time x y‖) ≤ ‖left‖ * ‖v‖ := by
  rw [integral_congr_ae (reciprocal_whole_section_norm time positive left v)]
  calc
    _ ≤ ‖left‖ * ‖T (physicalHeatValue time (T (normField v)))‖ :=
      (heatPaid% norm_product_bound) left (T (physicalHeatValue time (T (normField v))))
    _ ≤ ‖left‖ * ‖T (normField v)‖ := by
      change ‖left‖ * ‖burnolTateReciprocalValue (physicalHeatValue time (T (normField v)))‖ ≤ _
      rw [burnolTateReciprocalValue_norm]
      gcongr
      exact original_physical_heat_norm time positive (T (normField v))
    _ = _ := by
      change ‖left‖ * ‖burnolTateReciprocalValue (normField v)‖ = _
      rw [burnolTateReciprocalValue_norm, norm_field_norm]

theorem original_heat_whole_pairing (time : ℝ) (positive : 0 < time) (left v : BurnolL2) :
    (∫ x : ℝ, ∫ y : ℝ, star (left x) * v y * heatKernel time (x-y)) =
      inner ℂ left (heatValue time positive.le v) := by
  rw [original_heat_physical_source time positive v, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [physical_heat_row time positive v] with x raw
  rw [raw, heat_row_pairing, RCLike.inner_apply, starRingEnd_apply]
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with y
  ring

theorem original_reciprocal_heat_whole_pairing (time : ℝ) (positive : 0 < time) (left v : BurnolL2) :
    (∫ x : ℝ, ∫ y : ℝ, star (left x) * v y * reciprocalHeat time x y) =
      inner ℂ left (T (heatValue time positive.le (T v))) := by
  rw [original_heat_physical_source time positive (T v), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [reciprocal_heat_row time positive v] with x raw
  rw [raw, reciprocal_row_pairing, RCLike.inner_apply, starRingEnd_apply]
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with y
  ring

def heatClockKernelRead (time : ℝ) (left v : BurnolL2) (xy : ℝ × ℝ) : ℂ :=
  (time : ℂ)⁻¹ * (star (left xy.1) * v xy.2 * reciprocalHeat time xy.1 xy.2 -
    star (left xy.1) * v xy.2 * heatKernel time (xy.1-xy.2))

private theorem heat_clock_read_measured (left v : BurnolL2) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => heatClockKernelRead p.1 left v p.2) := by
  have kernel : Measurable (fun p : ℝ × ℝ => heatKernel p.1 p.2) := by
    change Measurable (fun p : ℝ × ℝ =>
      ((Real.sqrt (Real.pi / p.1) * Real.exp (-(Real.pi ^ 2 * p.2 ^ 2 / p.1)) : ℝ) : ℂ))
    fun_prop
  have leftRead : Measurable (fun p : ℝ × (ℝ × ℝ) => star (left p.2.1)) :=
    (Lp.stronglyMeasurable left).star.measurable.comp (measurable_fst.comp measurable_snd)
  have rightRead : Measurable (fun p : ℝ × (ℝ × ℝ) => v p.2.2) :=
    (Lp.stronglyMeasurable v).measurable.comp (measurable_snd.comp measurable_snd)
  have direct : Measurable (fun p : ℝ × (ℝ × ℝ) => heatKernel p.1 (p.2.1-p.2.2)) :=
    kernel.comp (show Measurable (fun p : ℝ × (ℝ × ℝ) => (p.1, p.2.1-p.2.2)) from by fun_prop)
  have reciprocal : Measurable (fun p : ℝ × (ℝ × ℝ) => reciprocalHeat p.1 p.2.1 p.2.2) := by
    exact (((continuous_abs.measurable.comp (measurable_fst.comp measurable_snd)).complex_ofReal.inv).mul
      ((continuous_abs.measurable.comp (measurable_snd.comp measurable_snd)).complex_ofReal.inv)).mul
        (kernel.comp (show Measurable (fun p : ℝ × (ℝ × ℝ) => (p.1, p.2.1⁻¹-p.2.2⁻¹)) from by fun_prop))
  exact (measurable_fst.complex_ofReal.inv).mul
    (((leftRead.mul rightRead).mul reciprocal).sub ((leftRead.mul rightRead).mul direct))

private theorem heat_clock_read_integrable (time : ℝ) (positive : 0 < time) (left v : BurnolL2) :
    Integrable (heatClockKernelRead time left v) (volume.prod volume) :=
  ((original_reciprocal_heat_whole_integrable time positive left v).sub
    (original_heat_whole_integrable time positive left v)).const_mul (time : ℂ)⁻¹

private theorem heat_clock_read_norm (time : ℝ) (positive : 0 < time) (left v : BurnolL2) :
    (∫ xy : ℝ × ℝ, ‖heatClockKernelRead time left v xy‖ ∂volume.prod volume) ≤
      (2 * ‖left‖ * ‖v‖) * time⁻¹ := by
  let R := fun xy : ℝ × ℝ => star (left xy.1) * v xy.2 * reciprocalHeat time xy.1 xy.2
  let H := fun xy : ℝ × ℝ => star (left xy.1) * v xy.2 * heatKernel time (xy.1-xy.2)
  have rInt : Integrable R (volume.prod volume) := original_reciprocal_heat_whole_integrable time positive left v
  have hInt : Integrable H (volume.prod volume) := original_heat_whole_integrable time positive left v
  have rBound : (∫ xy : ℝ × ℝ, ‖R xy‖ ∂volume.prod volume) ≤ ‖left‖ * ‖v‖ := by
    rw [integral_prod _ rInt.norm]
    exact original_reciprocal_heat_whole_norm time positive left v
  have hBound : (∫ xy : ℝ × ℝ, ‖H xy‖ ∂volume.prod volume) ≤ ‖left‖ * ‖v‖ := by
    rw [integral_prod _ hInt.norm]
    exact original_heat_whole_norm time positive left v
  calc
    _ ≤ ∫ xy : ℝ × ℝ, time⁻¹ * (‖R xy‖ + ‖H xy‖) ∂volume.prod volume := by
      apply integral_mono_ae (heat_clock_read_integrable time positive left v).norm
        ((rInt.norm.add hInt.norm).const_mul time⁻¹)
      filter_upwards with xy
      rw [heatClockKernelRead, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos positive]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr positive.le)
    _ = time⁻¹ * ((∫ xy : ℝ × ℝ, ‖R xy‖ ∂volume.prod volume) +
        (∫ xy : ℝ × ℝ, ‖H xy‖ ∂volume.prod volume)) := by
      rw [integral_const_mul, integral_add rInt.norm hInt.norm]
    _ ≤ time⁻¹ * (2 * ‖left‖ * ‖v‖) := by
      gcongr
      linarith
    _ = _ := by ring

private theorem positive_inverse_interval (lower upper : ℝ) (lowerPos : 0 < lower) (upperPos : 0 < upper) :
    IntervalIntegrable (fun time : ℝ => time⁻¹) volume lower upper := by
  have continuous : ContinuousOn (fun time : ℝ => time⁻¹) (Ioi 0) :=
    fun time positive => (continuousAt_id.inv₀ (ne_of_gt positive)).continuousWithinAt
  apply (continuous.mono ?_).intervalIntegrable
  intro time inside
  exact lt_of_lt_of_le (lt_min lowerPos upperPos) inside.1

theorem original_heat_clock_whole_integrable (lower upper : ℝ) (lowerPos : 0 < lower)
    (upperPos : 0 < upper) (left v : BurnolL2) :
    Integrable (fun p : ℝ × (ℝ × ℝ) => heatClockKernelRead p.1 left v p.2)
      ((volume.restrict (uIoc lower upper)).prod (volume.prod volume)) := by
  have measured := (heat_clock_read_measured left v).stronglyMeasurable
  apply (integrable_prod_iff measured.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with time inside
    exact heat_clock_read_integrable time
      (lt_of_lt_of_le (lt_min lowerPos upperPos) inside.1.le) left v
  · apply ((positive_inverse_interval lower upper lowerPos upperPos).def'.const_mul
        (2 * ‖left‖ * ‖v‖)).mono'
      measured.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with time inside
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact heat_clock_read_norm time
      (lt_of_lt_of_le (lt_min lowerPos upperPos) inside.1.le) left v

private theorem heat_clock_read_pairing (time : ℝ) (positive : 0 < time) (left v : BurnolL2) :
    (∫ xy : ℝ × ℝ, heatClockKernelRead time left v xy ∂volume.prod volume) =
      (time : ℂ)⁻¹ * (inner ℂ left (T (physicalHeatValue time (T v))) -
        inner ℂ left (physicalHeatValue time v)) := by
  change (∫ xy : ℝ × ℝ, (time : ℂ)⁻¹ * (_ - _) ∂volume.prod volume) = _
  rw [integral_const_mul, integral_sub
    (original_reciprocal_heat_whole_integrable time positive left v)
    (original_heat_whole_integrable time positive left v),
    integral_prod _ (original_reciprocal_heat_whole_integrable time positive left v),
    integral_prod _ (original_heat_whole_integrable time positive left v),
    original_reciprocal_heat_whole_pairing time positive left v, original_heat_whole_pairing time positive left v,
    original_heat_physical_source time positive (T v), original_heat_physical_source time positive v]

theorem original_heat_clock_fubini (lower upper : ℝ) (lowerPos : 0 < lower)
    (upperPos : 0 < upper) (left v : BurnolL2) :
    (∫ time : ℝ in lower..upper, (time : ℂ)⁻¹ *
      (inner ℂ left (T (physicalHeatValue time (T v))) - inner ℂ left (physicalHeatValue time v))) =
      ∫ xy : ℝ × ℝ, star (left xy.1) * v xy.2 *
        (∫ time : ℝ in lower..upper, (time : ℂ)⁻¹ *
          (reciprocalHeat time xy.1 xy.2 - heatKernel time (xy.1-xy.2))) ∂volume.prod volume := by
  have whole := original_heat_clock_whole_integrable lower upper lowerPos upperPos left v
  calc
    _ = ∫ time : ℝ in lower..upper, ∫ xy : ℝ × ℝ, heatClockKernelRead time left v xy ∂volume.prod volume := by
      apply intervalIntegral.integral_congr
      intro time inside
      exact (heat_clock_read_pairing time
        (lt_of_lt_of_le (lt_min lowerPos upperPos) inside.1) left v).symm
    _ = ∫ xy : ℝ × ℝ, (∫ time : ℝ in lower..upper, heatClockKernelRead time left v xy) ∂volume.prod volume := by
      exact intervalIntegral_integral_swap (f := fun time xy => heatClockKernelRead time left v xy) whole
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with xy
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro time _inside
      unfold heatClockKernelRead
      ring

theorem original_heat_clock_boundary (lower upper : ℝ) (lowerPos : 0 < lower)
    (upperPos : 0 < upper) (left v : BurnolL2) :
    (∫ time : ℝ in lower..upper, (time : ℂ)⁻¹ *
      (inner ℂ left (T (physicalHeatValue time (T v))) - inner ℂ left (physicalHeatValue time v))) =
      ∫ xy : ℝ × ℝ, star (left xy.1) * v xy.2 *
        (clockBand upper (upper * (xy.1 * xy.2)^2) (xy.1-xy.2) -
          clockBand lower (lower * (xy.1 * xy.2)^2) (xy.1-xy.2)) ∂volume.prod volume := by
  rw [original_heat_clock_fubini lower upper lowerPos upperPos left v]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (volume.ae_ne (0 : ℝ)),
    Measure.quasiMeasurePreserving_snd.ae (volume.ae_ne (0 : ℝ))] with xy xne yne
  rw [original_inverse_clock_boundary lower upper xy.1 xy.2 lowerPos upperPos xne yne]

end
end OriginalGamma.Source.TateConductor
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
