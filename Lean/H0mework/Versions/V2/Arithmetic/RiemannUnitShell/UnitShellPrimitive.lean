import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.StepClosedRange

/-! Actual unit counting and reciprocal tails generate the same strongly continuous scale family. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section

def burnolUnitCountingPrimitiveRaw (x : ℝ) : ℂ :=
  if x = 0 then -1 else (((⌈|x|⌉₊ : ℝ) - 1) / |x| - 1 : ℝ)

def burnolUnitReciprocalPrimitiveRaw (x : ℝ) : ℂ :=
  if 1 < |x| then ((|x| : ℝ) : ℂ)⁻¹ else 0

def burnolUnitReciprocalPrimitiveL2 : BurnolL2 :=
  let tail := burnolRadiusMellinTailKernelL2 1 (by norm_num) 1 (by norm_num)
  tail + reflectL2 tail

theorem burnolUnitReciprocalPrimitive_coeFn :
    (burnolUnitReciprocalPrimitiveL2 : ℝ → ℂ) =ᵐ[volume] burnolUnitReciprocalPrimitiveRaw := by
  let tail := burnolRadiusMellinTailKernelL2 1 (by norm_num) 1 (by norm_num)
  have tailRead : (tail : ℝ → ℂ) =ᵐ[volume] burnolRadiusMellinTailKernelRaw 1 1 :=
    (burnolRadiusMellinTailKernelRaw_memLp (by norm_num : (0 : ℝ) < 1) 1 (by norm_num)).coeFn_toLp
  filter_upwards [Lp.coeFn_add tail (reflectL2 tail),
    Lp.coeFn_compMeasurePreserving tail negMeasurePreserving, tailRead,
    negMeasurePreserving.quasiMeasurePreserving.ae tailRead] with x addAt reflectionAt leftAt rightAt
  change (tail + reflectL2 tail : BurnolL2) x = _
  rw [addAt]
  change tail x + reflectL2 tail x = _
  have reflected : reflectL2 tail x = tail (-x) := reflectionAt
  rw [reflected, leftAt, rightAt]
  unfold burnolRadiusMellinTailKernelRaw burnolUnitReciprocalPrimitiveRaw
  simp only [star_one, Complex.cpow_neg_one, mem_Ioi]
  by_cases nonnegative : 0 ≤ x
  · rw [abs_of_nonneg nonnegative, if_neg (by linarith : ¬ (1 : ℝ) < -x), add_zero]
  · rw [abs_of_neg (lt_of_not_ge nonnegative), if_neg (by linarith : ¬ (1 : ℝ) < x), zero_add]

theorem burnolUnitCountingPrimitive_small (x : ℝ) (small : |x| ≤ 1) :
    burnolUnitCountingPrimitiveRaw x = -1 := by
  by_cases zero : x = 0
  · simp [burnolUnitCountingPrimitiveRaw, zero]
  have ceiling : ⌈|x|⌉₊ = 1 := (Nat.ceil_eq_iff (by decide : (1 : ℕ) ≠ 0)).mpr
    ⟨by simpa using abs_pos.mpr zero, by simpa using small⟩
  simp [burnolUnitCountingPrimitiveRaw, zero, ceiling]

theorem burnolUnitCountingPrimitive_bound (x : ℝ) (nonzero : x ≠ 0) :
    ‖burnolUnitCountingPrimitiveRaw x‖ ≤ |x|⁻¹ := by
  have positive := abs_pos.mpr nonzero
  have low := Nat.le_ceil |x|
  have high := Nat.ceil_lt_add_one positive.le
  unfold burnolUnitCountingPrimitiveRaw
  rw [if_neg nonzero, Complex.norm_real, Real.norm_eq_abs]
  rw [inv_eq_one_div, abs_le]
  constructor
  · have scale : (↑⌈|x|⌉₊ - 1) / |x| * |x| = ↑⌈|x|⌉₊ - 1 :=
      div_mul_cancel₀ _ positive.ne'
    have unit : (1 / |x|) * |x| = 1 := one_div_mul_cancel positive.ne'
    apply (mul_le_mul_iff_left₀ positive).mp
    nlinarith
  · have scale : (↑⌈|x|⌉₊ - 1) / |x| * |x| = ↑⌈|x|⌉₊ - 1 :=
      div_mul_cancel₀ _ positive.ne'
    have unit : (1 / |x|) * |x| = 1 := one_div_mul_cancel positive.ne'
    apply (mul_le_mul_iff_left₀ positive).mp
    nlinarith

theorem burnolUnitCountingPrimitive_memLp : MemLp burnolUnitCountingPrimitiveRaw 2 volume := by
  have measured : Measurable burnolUnitCountingPrimitiveRaw := by
    apply Measurable.ite (measurableSet_singleton (0 : ℝ)) measurable_const
    fun_prop
  have rawMem : MemLp burnolUnitReciprocalPrimitiveRaw 2 volume :=
    (Lp.memLp burnolUnitReciprocalPrimitiveL2).ae_eq burnolUnitReciprocalPrimitive_coeFn
  have headMem : MemLp ((symmetricInterval 1).indicator (fun _ : ℝ => (1 : ℂ))) 2 volume :=
    memLp_indicator_const 2 (measurableSet_symmetricInterval 1) 1 (Or.inr (by simp [symmetricInterval]))
  apply (headMem.add rawMem).mono measured.aestronglyMeasurable
  filter_upwards with x
  by_cases small : |x| ≤ 1
  · rw [burnolUnitCountingPrimitive_small x small, norm_neg, norm_one]
    change _ ≤ ‖(symmetricInterval 1).indicator (fun _ : ℝ => (1 : ℂ)) x + burnolUnitReciprocalPrimitiveRaw x‖
    rw [indicator_of_mem (show x ∈ symmetricInterval 1 from abs_le.mp small)]
    simp only [burnolUnitReciprocalPrimitiveRaw, if_neg (not_lt.mpr small), add_zero, norm_one]
    exact le_rfl
  · have outside : (1 : ℝ) < |x| := lt_of_not_ge small
    change _ ≤ ‖(symmetricInterval 1).indicator (fun _ : ℝ => (1 : ℂ)) x + burnolUnitReciprocalPrimitiveRaw x‖
    rw [indicator_of_notMem (show x ∉ symmetricInterval 1 from fun h => small (abs_le.mpr h)), zero_add]
    rw [burnolUnitReciprocalPrimitiveRaw, if_pos outside, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_abs]
    exact burnolUnitCountingPrimitive_bound x (abs_pos.mp ((by norm_num : (0 : ℝ) < 1).trans outside))

def burnolUnitCountingPrimitiveL2 : BurnolL2 := burnolUnitCountingPrimitive_memLp.toLp _

def burnolSourceScalePrimitive (value : BurnolL2) (scale : ℝ) : BurnolL2 :=
  Real.sqrt scale • burnolMultiplicativeDilation (Real.log scale) value

theorem burnolSourceScalePrimitive_coeFn (value : BurnolL2) (raw : ℝ → ℂ)
    (rawRead : value =ᵐ[volume] raw) (scale : ℝ) (positive : 0 < scale) :
    (burnolSourceScalePrimitive value scale : ℝ → ℂ) =ᵐ[volume]
      fun x : ℝ => (scale : ℂ) * raw (scale * x) := by
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => scale * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := scale) positive.ne')
  filter_upwards [Lp.coeFn_smul (Real.sqrt scale)
    (burnolMultiplicativeDilation (Real.log scale) value),
    burnolMultiplicativeDilation_coeFn (Real.log scale) value, qmp.ae rawRead]
      with x smulAt dilationAt sourceAt
  change (Real.sqrt scale • burnolMultiplicativeDilation (Real.log scale) value : BurnolL2) x = _
  rw [smulAt]
  change (Real.sqrt scale : ℂ) * burnolMultiplicativeDilation (Real.log scale) value x = _
  rw [dilationAt]
  unfold burnolL2RawNormalizedDilation
  rw [Real.exp_log positive, sourceAt]
  have sqrtRead : Real.exp (Real.log scale / 2) = Real.sqrt scale := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos positive]
    congr 1
    ring
  rw [sqrtRead, ← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt positive.le]

theorem burnolSourceScalePrimitive_continuous (value : BurnolL2) :
    ContinuousOn (burnolSourceScalePrimitive value) (Ioi 0) := by
  exact Real.continuous_sqrt.continuousOn.smul
    ((burnolMultiplicativeDilation_stronglyContinuous value).comp_continuousOn
      (Real.continuousOn_log.mono (fun _ positive => (ne_of_gt positive))))

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
