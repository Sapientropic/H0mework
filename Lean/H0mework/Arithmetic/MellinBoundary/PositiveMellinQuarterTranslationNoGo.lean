import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import H0mework.Arithmetic.Mellin.QuarterEnergy
import H0mework.Arithmetic.MellinBoundary.PositiveMellinQuarterMaterial

/-!
# Translation-orbit obstruction on the quarter `L²` carrier

The source low correction and its scale-three raw dilation form a compact
log-quarter shell.  Its translates by the same actual scale are disjoint.
After normalization this gives an orthonormal orbit, so a continuous
functional carrying a unit-modulus translation character must vanish on the
shell.  The Mellin readback of that shell is nonzero for `Re z > 0`; the
extension contradiction is assembled in the companion module.

This is a representation diagnostic.  It does not produce a radial-zero
incidence and it does not alter the living-law root or its ledger.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Bessel's inequality turns a unit-modulus character on an orthonormal
orbit into a zero readout at the orbit base. -/
theorem continuousFunctional_zero_on_unitOrthonormalOrbit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (orbit : ℕ → E) (orthonormal : Orthonormal ℂ orbit)
    (functional : E →L[ℂ] ℂ) (character : ℂ)
    (characterNorm : ‖character‖ = 1)
    (orbitRead : ∀ n, functional (orbit n) =
      character ^ n * functional (orbit 0)) :
    functional (orbit 0) = 0 := by
  let representing : E := (InnerProductSpace.toDual ℂ E).symm functional
  have summableInner : Summable fun n : ℕ =>
      ‖inner ℂ (orbit n) representing‖ ^ 2 :=
    orthonormal.inner_products_summable representing
  have valueNorm (n : ℕ) :
      ‖inner ℂ (orbit n) representing‖ ^ 2 =
        ‖functional (orbit 0)‖ ^ 2 := by
    rw [norm_inner_symm]
    rw [InnerProductSpace.toDual_symm_apply]
    rw [orbitRead]
    rw [norm_mul, norm_pow, characterNorm, one_pow, one_mul]
  have summableConst : Summable fun _n : ℕ =>
      ‖functional (orbit 0)‖ ^ 2 := by
    simpa only [valueNorm] using summableInner
  have squareZero : ‖functional (orbit 0)‖ ^ 2 = 0 := by
    simpa only [summable_const_iff] using summableConst
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp squareZero)

/-- The first q-rich successor scale, specialized to its actual stage-zero
value.  Keeping the literal value `3` makes the support arithmetic explicit;
the q-rich source theorem identifies this value with `stage + 3`. -/
def positiveMellinQuarterNoGoScale : ℝ := 3

theorem positiveMellinQuarterNoGoScale_pos :
    0 < positiveMellinQuarterNoGoScale := by
  norm_num [positiveMellinQuarterNoGoScale]

theorem positiveMellinQuarterNoGoScale_log_pos :
    0 < Real.log positiveMellinQuarterNoGoScale := by
  exact Real.log_pos (by norm_num [positiveMellinQuarterNoGoScale])

def positiveMellinQuarterNoGoRawLow : ClozelPositiveMellinFunction :=
  positiveMellinRawDilation positiveMellinQuarterNoGoScale
    positiveMellinQuarterNoGoScale_pos positiveClozelLowCorrection

theorem positiveMellinQuarterNoGoRawLow_mem_quarterL2 :
    positiveMellinQuarterNoGoRawLow ∈ positiveMellinQuarterL2Submodule := by
  have normalized := positiveQuarterNormalizedDilation_mem_quarterL2
    positiveMellinQuarterNoGoScale positiveMellinQuarterNoGoScale_pos
    positiveClozelLowCorrection positiveClozelLowCorrection_mem_quarterL2
  have weightNe : positiveMellinQuarterDilationWeight
      positiveMellinQuarterNoGoScale ≠ 0 :=
    positiveMellinQuarterDilationWeight_ne_zero _
  have rawEq : positiveMellinQuarterNoGoRawLow =
      (positiveMellinQuarterDilationWeight
        positiveMellinQuarterNoGoScale)⁻¹ •
        positiveMellinQuarterNormalizedDilation
          positiveMellinQuarterNoGoScale positiveMellinQuarterNoGoScale_pos
          positiveClozelLowCorrection := by
    funext t
    simp [positiveMellinQuarterNoGoRawLow,
      positiveMellinQuarterNormalizedDilation, smul_eq_mul, weightNe]
  rw [rawEq]
  change MemLp
    (positiveMellinLogQuarterTransform
      ((positiveMellinQuarterDilationWeight
        positiveMellinQuarterNoGoScale)⁻¹ •
        positiveMellinQuarterNormalizedDilation
          positiveMellinQuarterNoGoScale positiveMellinQuarterNoGoScale_pos
          positiveClozelLowCorrection))
      (2 : ℝ≥0∞) (volume : Measure ℝ)
  rw [map_smul]
  exact normalized.const_smul _

def positiveMellinQuarterNoGoShell : ClozelPositiveMellinFunction :=
  positiveClozelLowCorrection - positiveMellinQuarterNoGoRawLow

theorem positiveMellinQuarterNoGoShell_mem_quarterL2 :
    positiveMellinQuarterNoGoShell ∈ positiveMellinQuarterL2Submodule := by
  change MemLp
    (positiveMellinLogQuarterTransform
      (positiveClozelLowCorrection - positiveMellinQuarterNoGoRawLow))
      (2 : ℝ≥0∞) (volume : Measure ℝ)
  rw [map_sub]
  exact positiveClozelLowCorrection_mem_quarterL2.sub
    positiveMellinQuarterNoGoRawLow_mem_quarterL2

theorem positiveMellinQuarterNoGoRawLow_logQuarterTransform (x : ℝ) :
    positiveMellinLogQuarterTransform
        positiveMellinQuarterNoGoRawLow x =
      (Iic (-Real.log positiveMellinQuarterNoGoScale)).indicator
        (fun y : ℝ => (Real.exp (y / 4) : ℂ)) x := by
  unfold positiveMellinQuarterNoGoRawLow positiveMellinRawDilation
    positiveMellinLogQuarterTransform positiveClozelLowCorrection
    clozelLowCorrection
  change (Real.exp (x / 4) : ℂ) *
      (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ))
        (positiveMellinQuarterNoGoScale * Real.exp x) = _
  by_cases hx : x ≤ -Real.log positiveMellinQuarterNoGoScale
  · have harg : positiveMellinQuarterNoGoScale * Real.exp x ≤ 1 := by
      calc
        positiveMellinQuarterNoGoScale * Real.exp x =
            Real.exp (Real.log positiveMellinQuarterNoGoScale) * Real.exp x := by
              rw [Real.exp_log positiveMellinQuarterNoGoScale_pos]
        _ = Real.exp (Real.log positiveMellinQuarterNoGoScale + x) := by
          rw [Real.exp_add]
        _ ≤ Real.exp 0 := (Real.exp_le_exp).mpr (by linarith)
        _ = 1 := Real.exp_zero
    have hargpos : 0 < positiveMellinQuarterNoGoScale * Real.exp x :=
      mul_pos positiveMellinQuarterNoGoScale_pos (Real.exp_pos x)
    rw [indicator_of_mem (show positiveMellinQuarterNoGoScale * Real.exp x ∈
        Ioc (0 : ℝ) 1 from ⟨hargpos, harg⟩),
      indicator_of_mem (show x ∈ Iic (-Real.log positiveMellinQuarterNoGoScale)
        from hx), mul_one]
  · have hx' : -Real.log positiveMellinQuarterNoGoScale < x := lt_of_not_ge hx
    have harg : 1 < positiveMellinQuarterNoGoScale * Real.exp x := by
      calc
        1 = Real.exp 0 := Real.exp_zero.symm
        _ < Real.exp (Real.log positiveMellinQuarterNoGoScale + x) :=
          (Real.exp_lt_exp).mpr (by linarith)
        _ = Real.exp (Real.log positiveMellinQuarterNoGoScale) * Real.exp x := by
          rw [Real.exp_add]
        _ = positiveMellinQuarterNoGoScale * Real.exp x := by
          rw [Real.exp_log positiveMellinQuarterNoGoScale_pos]
    have hnot : positiveMellinQuarterNoGoScale * Real.exp x ∉ Ioc (0 : ℝ) 1 :=
      notMem_Ioc_of_gt harg
    rw [indicator_of_notMem hnot,
      indicator_of_notMem (show x ∉ Iic (-Real.log positiveMellinQuarterNoGoScale)
        from not_le_of_gt hx'), mul_zero]

theorem positiveMellinQuarterNoGoShell_logQuarterTransform (x : ℝ) :
    positiveMellinLogQuarterTransform positiveMellinQuarterNoGoShell x =
      (Ioc (-Real.log positiveMellinQuarterNoGoScale) 0).indicator
        (fun y : ℝ => (Real.exp (y / 4) : ℂ)) x := by
  unfold positiveMellinQuarterNoGoShell
  rw [map_sub]
  simp only [Pi.sub_apply]
  rw [positiveMellinLogQuarterTransform_lowCorrection,
    positiveMellinQuarterNoGoRawLow_logQuarterTransform]
  by_cases hx0 : x ≤ 0
  · by_cases hxh : x ≤ -Real.log positiveMellinQuarterNoGoScale
    · have first : (Iic 0).indicator
          (fun y : ℝ => (Real.exp (y / 4) : ℂ)) x =
          (Real.exp (x / 4) : ℂ) :=
        indicator_of_mem (mem_Iic.mpr hx0) _
      have second : (Iic (-Real.log positiveMellinQuarterNoGoScale)).indicator
          (fun y : ℝ => (Real.exp (y / 4) : ℂ)) x =
          (Real.exp (x / 4) : ℂ) :=
        indicator_of_mem (mem_Iic.mpr hxh) _
      have hnotIoc : x ∉ Ioc (-Real.log positiveMellinQuarterNoGoScale) 0 := by
        intro h
        exact (not_lt_of_ge hxh) h.1
      rw [first, second, sub_self, indicator_of_notMem hnotIoc]
    · have hxh' : -Real.log positiveMellinQuarterNoGoScale < x := lt_of_not_ge hxh
      have first : (Iic 0).indicator
          (fun y : ℝ => (Real.exp (y / 4) : ℂ)) x =
          (Real.exp (x / 4) : ℂ) :=
        indicator_of_mem (mem_Iic.mpr hx0) _
      have second : (Iic (-Real.log positiveMellinQuarterNoGoScale)).indicator
          (fun y : ℝ => (Real.exp (y / 4) : ℂ)) x = 0 :=
        indicator_of_notMem (show x ∉ Iic (-Real.log positiveMellinQuarterNoGoScale)
          from not_le_of_gt hxh') _
      have rhs : (Ioc (-Real.log positiveMellinQuarterNoGoScale) 0).indicator
          (fun y : ℝ => (Real.exp (y / 4) : ℂ)) x =
          (Real.exp (x / 4) : ℂ) :=
        indicator_of_mem (show x ∈ Ioc (-Real.log positiveMellinQuarterNoGoScale) 0
          from ⟨hxh', hx0⟩) _
      rw [first, second, rhs, sub_zero]
  · have hx0' : 0 < x := lt_of_not_ge hx0
    have hnotIic0 : x ∉ Iic (0 : ℝ) := notMem_Iic.mpr hx0'
    have hnotIicScale : x ∉ Iic (-Real.log positiveMellinQuarterNoGoScale) :=
      notMem_Iic.mpr (by linarith [positiveMellinQuarterNoGoScale_log_pos])
    have hnotIoc : x ∉ Ioc (-Real.log positiveMellinQuarterNoGoScale) 0 := by
      intro h
      exact (not_le_of_gt hx0') h.2
    rw [indicator_of_notMem hnotIic0,
      indicator_of_notMem hnotIicScale,
      indicator_of_notMem hnotIoc]
    ring

def positiveMellinQuarterNoGoShellL2 : PositiveMellinQuarterL2 :=
  ⟨positiveMellinQuarterNoGoShell,
    positiveMellinQuarterNoGoShell_mem_quarterL2⟩

def positiveMellinQuarterNoGoShellLp : PositiveMellinQuarterEnergy :=
  positiveMellinQuarterLpValue positiveMellinQuarterNoGoShellL2

def positiveMellinQuarterNoGoShellUnit : PositiveMellinQuarterEnergy :=
  (‖positiveMellinQuarterNoGoShellLp‖⁻¹ : ℂ) •
    positiveMellinQuarterNoGoShellLp

theorem positiveMellinQuarterNoGoShellUnit_norm
    (baseNe : positiveMellinQuarterNoGoShellLp ≠ 0) :
    ‖positiveMellinQuarterNoGoShellUnit‖ = 1 := by
  unfold positiveMellinQuarterNoGoShellUnit
  rw [norm_smul]
  have hnorm : ‖(‖positiveMellinQuarterNoGoShellLp‖⁻¹ : ℂ)‖ =
      ‖positiveMellinQuarterNoGoShellLp‖⁻¹ := by
    simp [Complex.norm_real]
  rw [hnorm, inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr baseNe

theorem positiveMellinQuarterNoGoShellLp_coeFn_support :
    ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      x ∉ Ioc (-Real.log positiveMellinQuarterNoGoScale) 0 →
        positiveMellinQuarterNoGoShellLp x = 0 := by
  have hcoe := (positiveMellinQuarterL2_memLp
    positiveMellinQuarterNoGoShellL2).coeFn_toLp
  filter_upwards [hcoe] with x hx
  intro hnot
  change (positiveMellinQuarterLpValue
    positiveMellinQuarterNoGoShellL2) x = 0
  change (MemLp.toLp
      (positiveMellinLogQuarterTransform
        positiveMellinQuarterNoGoShellL2)
      (positiveMellinQuarterL2_memLp
        positiveMellinQuarterNoGoShellL2)) x = 0
  rw [hx]
  change positiveMellinLogQuarterTransform
    positiveMellinQuarterNoGoShell x = 0
  rw [positiveMellinQuarterNoGoShell_logQuarterTransform,
    indicator_of_notMem hnot]

theorem positiveMellinQuarterNoGoShellUnit_coeFn_support :
    ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      x ∉ Ioc (-Real.log positiveMellinQuarterNoGoScale) 0 →
        positiveMellinQuarterNoGoShellUnit x = 0 := by
  have hcoe := Lp.coeFn_smul
    (‖positiveMellinQuarterNoGoShellLp‖⁻¹ : ℂ)
    positiveMellinQuarterNoGoShellLp
  have hbase := positiveMellinQuarterNoGoShellLp_coeFn_support
  filter_upwards [hcoe, hbase] with x hx hbase
  intro hnot
  change ((‖positiveMellinQuarterNoGoShellLp‖⁻¹ : ℂ) •
    positiveMellinQuarterNoGoShellLp) x = 0
  rw [hx]
  simp only [Pi.smul_apply]
  rw [hbase hnot]
  simp

theorem positiveMellinQuarterNoGoRawLow_extension :
    positiveMellinExtension positiveMellinQuarterNoGoRawLow =
      (fun t : ℝ => positiveMellinExtension positiveClozelLowCorrection
        (positiveMellinQuarterNoGoScale * t)) := by
  funext t
  by_cases ht : 0 < t
  · simp [positiveMellinQuarterNoGoRawLow, positiveMellinRawDilation,
      positiveMellinExtension, positiveClozelLowCorrection, ht,
      mul_pos positiveMellinQuarterNoGoScale_pos ht]
  · have hnt : ¬ 0 < positiveMellinQuarterNoGoScale * t := by
      exact not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos
        positiveMellinQuarterNoGoScale_pos.le (le_of_not_gt ht))
    simp [positiveMellinQuarterNoGoRawLow, positiveMellinRawDilation,
      positiveMellinExtension, positiveClozelLowCorrection, ht, hnt]

def positiveMellinQuarterNoGoShellElement (z : ℂ) (hz : 0 < z.re) :
    positiveMellinConvergentSubmodule z := by
  have low : MellinConvergent
      (positiveMellinExtension positiveClozelLowCorrection) z :=
    positiveClozelLowCorrection_positiveMellinConvergent hz
  have raw : MellinConvergent
      (positiveMellinExtension positiveMellinQuarterNoGoRawLow) z := by
    rw [positiveMellinQuarterNoGoRawLow_extension]
    exact (MellinConvergent.comp_mul_left
      positiveMellinQuarterNoGoScale_pos).2 low
  exact ⟨positiveMellinQuarterNoGoShell, by
    change MellinConvergent
      (positiveMellinExtension
        (positiveClozelLowCorrection - positiveMellinQuarterNoGoRawLow)) z
    rw [map_sub]
    change IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (z - 1) •
        (positiveMellinExtension positiveClozelLowCorrection t -
          positiveMellinExtension positiveMellinQuarterNoGoRawLow t)) (Ioi 0)
    exact (low.sub raw).congr_fun
      (fun t ht => by simp; ring) measurableSet_Ioi⟩

theorem positiveMellinQuarterNoGoShellElement_value (z : ℂ) (hz : 0 < z.re) :
    positiveMellinFunctional z
        (positiveMellinQuarterNoGoShellElement z hz) =
      1 / z - (positiveMellinQuarterNoGoScale : ℂ) ^ (-z) * (1 / z) := by
  have low : HasMellin
      (positiveMellinExtension positiveClozelLowCorrection) z
      (1 / z) := ⟨positiveClozelLowCorrection_positiveMellinConvergent hz,
        by
          calc
            mellin (positiveMellinExtension positiveClozelLowCorrection) z =
                mellin clozelLowCorrection z := by
                  apply setIntegral_congr_fun measurableSet_Ioi
                  intro t ht
                  change 0 < t at ht
                  simp [positiveMellinExtension, positiveClozelLowCorrection,
                    clozelLowCorrection, ht]
            _ = 1 / z := (hasMellin_clozelLowCorrection hz).2⟩
  have raw : HasMellin
      (positiveMellinExtension positiveMellinQuarterNoGoRawLow) z
      ((positiveMellinQuarterNoGoScale : ℂ) ^ (-z) * (1 / z : ℂ)) := by
    rw [positiveMellinQuarterNoGoRawLow_extension]
    refine ⟨(MellinConvergent.comp_mul_left
      positiveMellinQuarterNoGoScale_pos).2 low.1, ?_⟩
    rw [mellin_comp_mul_left
      (ha := positiveMellinQuarterNoGoScale_pos), low.2]
    simp only [smul_eq_mul]
  have shell := hasMellin_sub low.1 raw.1
  change mellin
      (positiveMellinExtension
        (positiveClozelLowCorrection - positiveMellinQuarterNoGoRawLow)) z = _
  rw [show positiveMellinExtension
      (positiveClozelLowCorrection - positiveMellinQuarterNoGoRawLow) =
      positiveMellinExtension positiveClozelLowCorrection -
        positiveMellinExtension positiveMellinQuarterNoGoRawLow by rw [map_sub]]
  calc
    mellin (positiveMellinExtension positiveClozelLowCorrection -
        positiveMellinExtension positiveMellinQuarterNoGoRawLow) z =
        mellin (positiveMellinExtension positiveClozelLowCorrection) z -
          mellin (positiveMellinExtension positiveMellinQuarterNoGoRawLow) z := shell.2
    _ = 1 / z - (positiveMellinQuarterNoGoScale : ℂ) ^ (-z) * (1 / z) := by
      rw [low.2, raw.2]

theorem positiveMellinQuarterNoGoShellElement_value_ne_zero
    (z : ℂ) (hz : 0 < z.re) :
    positiveMellinFunctional z
        (positiveMellinQuarterNoGoShellElement z hz) ≠ 0 := by
  rw [positiveMellinQuarterNoGoShellElement_value z hz]
  have zNe : z ≠ 0 := by
    intro hz0
    rw [hz0, zero_re] at hz
    exact (lt_irrefl 0) hz
  have qNorm : ‖(positiveMellinQuarterNoGoScale : ℂ) ^ (-z)‖ =
      positiveMellinQuarterNoGoScale ^ (-z.re) := by
    exact Complex.norm_cpow_eq_rpow_re_of_pos
      positiveMellinQuarterNoGoScale_pos (-z)
  have qLt : ‖(positiveMellinQuarterNoGoScale : ℂ) ^ (-z)‖ < 1 := by
    rw [qNorm]
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · norm_num [positiveMellinQuarterNoGoScale]
    · linarith
  have qNe : (positiveMellinQuarterNoGoScale : ℂ) ^ (-z) ≠ 1 := by
    intro qEq
    rw [qEq] at qLt
    norm_num at qLt
  intro hzero
  have hquot :
      (1 - (positiveMellinQuarterNoGoScale : ℂ) ^ (-z)) / z = 0 := by
    calc
      (1 - (positiveMellinQuarterNoGoScale : ℂ) ^ (-z)) / z =
          1 / z - (positiveMellinQuarterNoGoScale : ℂ) ^ (-z) * (1 / z) := by
            field_simp
      _ = 0 := hzero
  rcases (div_eq_zero_iff.mp hquot) with hnum | hz0
  · exact qNe (sub_eq_zero.mp hnum).symm
  · exact (zNe hz0).elim

/-- An orthonormal family with pairwise disjoint measurable supports. -/
theorem orthonormal_of_disjoint_support
    (orbit : ℕ → PositiveMellinQuarterEnergy)
    (support : ℕ → Set ℝ)
    (norm_one : ∀ n, ‖orbit n‖ = 1)
    (support_zero : ∀ n,
      ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
        x ∉ support n → orbit n x = 0)
    (support_disjoint : ∀ ⦃m n : ℕ⦄, m ≠ n → Disjoint (support m) (support n)) :
    Orthonormal ℂ orbit := by
  rw [orthonormal_iff_ite]
  intro m n
  by_cases hmn : m = n
  · subst n
    rw [inner_self_eq_norm_sq_to_K, norm_one]
    norm_num
  · rw [MeasureTheory.L2.inner_def]
    simp only [if_neg hmn]
    apply integral_eq_zero_of_ae
    have hm := support_zero m
    have hn := support_zero n
    filter_upwards [hm, hn] with x hm hn
    by_cases hxm : x ∈ support m
    · have hxn : x ∉ support n := by
        intro hxn
        exact (Set.disjoint_left.mp (support_disjoint hmn)) hxm hxn
      simp [hn hxn]
    · simp [hm hxm]

def positiveMellinQuarterNoGoSupport (n : ℕ) : Set ℝ :=
  Ioc (-Real.log positiveMellinQuarterNoGoScale -
      (n : ℝ) * Real.log positiveMellinQuarterNoGoScale)
    (-(n : ℝ) * Real.log positiveMellinQuarterNoGoScale)

theorem positiveMellinQuarterNoGoSupport_disjoint
    {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (positiveMellinQuarterNoGoSupport m)
      (positiveMellinQuarterNoGoSupport n) := by
  rcases lt_or_gt_of_ne hmn with hmn | hnm
  · apply Set.disjoint_left.mpr
    intro x hx hy
    have hcast : (m : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hmn)
    have hm_lower : -Real.log positiveMellinQuarterNoGoScale -
          (m : ℝ) * Real.log positiveMellinQuarterNoGoScale < x := hx.1
    have hn_upper : x ≤ -(n : ℝ) * Real.log positiveMellinQuarterNoGoScale := hy.2
    have hmul := mul_le_mul_of_nonneg_right hcast
      (le_of_lt positiveMellinQuarterNoGoScale_log_pos)
    linarith
  · apply Set.disjoint_left.mpr
    intro x hx hy
    have hcast : (n : ℝ) + 1 ≤ (m : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hnm)
    have hm_upper : x ≤ -(m : ℝ) * Real.log positiveMellinQuarterNoGoScale := hx.2
    have hn_lower : -Real.log positiveMellinQuarterNoGoScale -
          (n : ℝ) * Real.log positiveMellinQuarterNoGoScale < x := hy.1
    have hmul := mul_le_mul_of_nonneg_right hcast
      (le_of_lt positiveMellinQuarterNoGoScale_log_pos)
    linarith

def positiveMellinQuarterNoGoOrbit (base : PositiveMellinQuarterEnergy) : ℕ →
    PositiveMellinQuarterEnergy
  | 0 => base
  | n + 1 => positiveMellinQuarterEnergyTranslation
      (Real.log positiveMellinQuarterNoGoScale)
      (positiveMellinQuarterNoGoOrbit base n)

theorem positiveMellinQuarterNoGoOrbit_eq_translation
    (base : PositiveMellinQuarterEnergy) (n : ℕ) :
    positiveMellinQuarterNoGoOrbit base n =
      positiveMellinQuarterEnergyTranslation
        ((n : ℝ) * Real.log positiveMellinQuarterNoGoScale) base := by
  induction n with
  | zero =>
      simpa [positiveMellinQuarterNoGoOrbit] using
        (positiveMellinQuarterEnergyTranslation_zero base).symm
  | succ n ih =>
      rw [positiveMellinQuarterNoGoOrbit, ih]
      have comp := congrArg
        (fun F : PositiveMellinQuarterEnergy →ₗ[ℂ]
          PositiveMellinQuarterEnergy => F base)
        (positiveMellinQuarterEnergyTranslation_comp
          (Real.log positiveMellinQuarterNoGoScale)
          ((n : ℝ) * Real.log positiveMellinQuarterNoGoScale))
      calc
        positiveMellinQuarterEnergyTranslation
            (Real.log positiveMellinQuarterNoGoScale)
            (positiveMellinQuarterEnergyTranslation
              ((n : ℝ) * Real.log positiveMellinQuarterNoGoScale) base) =
            positiveMellinQuarterEnergyTranslation
              ((n : ℝ) * Real.log positiveMellinQuarterNoGoScale +
                Real.log positiveMellinQuarterNoGoScale) base := comp
        _ = positiveMellinQuarterEnergyTranslation
              (((n + 1 : ℕ) : ℝ) * Real.log positiveMellinQuarterNoGoScale) base := by
          congr 2
          push_cast
          ring

theorem positiveMellinQuarterNoGoOrbit_support (n : ℕ) :
    ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      x ∉ positiveMellinQuarterNoGoSupport n →
        positiveMellinQuarterNoGoOrbit
          positiveMellinQuarterNoGoShellUnit n x = 0 := by
  rw [positiveMellinQuarterNoGoOrbit_eq_translation]
  change ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
    x ∉ positiveMellinQuarterNoGoSupport n →
      (Lp.compMeasurePreserving
        (fun y : ℝ => (n : ℝ) * Real.log positiveMellinQuarterNoGoScale + y)
        (measurePreserving_add_left (volume : Measure ℝ)
          ((n : ℝ) * Real.log positiveMellinQuarterNoGoScale))
        positiveMellinQuarterNoGoShellUnit) x = 0
  have hcomp := Lp.coeFn_compMeasurePreserving
    positiveMellinQuarterNoGoShellUnit
    (measurePreserving_add_left (volume : Measure ℝ)
      ((n : ℝ) * Real.log positiveMellinQuarterNoGoScale))
  have hunit := positiveMellinQuarterNoGoShellUnit_coeFn_support
  have hunitShift :=
    (measurePreserving_add_left (volume : Measure ℝ)
      ((n : ℝ) * Real.log positiveMellinQuarterNoGoScale)).quasiMeasurePreserving.tendsto_ae hunit
  filter_upwards [hcomp, hunitShift] with x hx hunit
  change ((n : ℝ) * Real.log positiveMellinQuarterNoGoScale + x) ∉
      Ioc (-Real.log positiveMellinQuarterNoGoScale) 0 →
      positiveMellinQuarterNoGoShellUnit
        ((n : ℝ) * Real.log positiveMellinQuarterNoGoScale + x) = 0 at hunit
  intro hnot
  rw [hx]
  change positiveMellinQuarterNoGoShellUnit
    ((n : ℝ) * Real.log positiveMellinQuarterNoGoScale + x) = 0
  apply hunit
  intro hmem
  apply hnot
  dsimp [positiveMellinQuarterNoGoSupport] at hmem ⊢
  constructor
  · exact (sub_lt_iff_lt_add.mpr (by simpa [add_comm] using hmem.1))
  · have hle : x ≤ 0 - (n : ℝ) * Real.log positiveMellinQuarterNoGoScale :=
      le_sub_iff_add_le.mpr (by simpa [add_comm] using hmem.2)
    simpa [zero_sub, neg_mul] using hle

theorem positiveMellinQuarterNoGoOrbit_norm_one
    (baseNe : positiveMellinQuarterNoGoShellLp ≠ 0) (n : ℕ) :
    ‖positiveMellinQuarterNoGoOrbit
      positiveMellinQuarterNoGoShellUnit n‖ = 1 := by
  rw [positiveMellinQuarterNoGoOrbit_eq_translation]
  change ‖Lp.compMeasurePreserving
      (fun x : ℝ => (n : ℝ) * Real.log positiveMellinQuarterNoGoScale + x)
      (measurePreserving_add_left (volume : Measure ℝ)
        ((n : ℝ) * Real.log positiveMellinQuarterNoGoScale))
      positiveMellinQuarterNoGoShellUnit‖ = 1
  rw [Lp.norm_compMeasurePreserving]
  exact positiveMellinQuarterNoGoShellUnit_norm baseNe

theorem positiveMellinQuarterNoGoOrbit_orthonormal
    (baseNe : positiveMellinQuarterNoGoShellLp ≠ 0) :
    Orthonormal ℂ (positiveMellinQuarterNoGoOrbit
      positiveMellinQuarterNoGoShellUnit) := by
  apply orthonormal_of_disjoint_support
    (orbit := positiveMellinQuarterNoGoOrbit
      positiveMellinQuarterNoGoShellUnit)
    (support := positiveMellinQuarterNoGoSupport)
  · exact positiveMellinQuarterNoGoOrbit_norm_one baseNe
  · exact positiveMellinQuarterNoGoOrbit_support
  · intro m n hmn
    exact positiveMellinQuarterNoGoSupport_disjoint hmn

end
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
