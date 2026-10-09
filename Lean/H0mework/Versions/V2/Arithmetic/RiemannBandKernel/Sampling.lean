import H0mework.Versions.V2.Arithmetic.BurnolPhysical.L2DirectDilation
import Mathlib.Analysis.PSeries

/-! The original first moment generates an absolutely summable annular sampling family in the original L² space. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex Filter FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace SchwartzMap Topology
noncomputable section

def burnolSamplingAnnulus : Set ℝ := {t | (1 / 4 : ℝ) < |t| ∧ |t| ≤ 4}

theorem measurableSet_burnolSamplingAnnulus : MeasurableSet burnolSamplingAnnulus :=
  (measurableSet_lt measurable_const continuous_abs.measurable).inter
    (measurableSet_le continuous_abs.measurable measurable_const)

def burnolAnnulusSamplingRaw (value : BurnolL2) (n : ℕ) : ℝ → ℂ :=
  burnolSamplingAnnulus.indicator (fun t => value (((n : ℝ) + 1) * t))

theorem burnolAnnulusSamplingRaw_memLp (value : BurnolL2) (n : ℕ) :
    MemLp (burnolAnnulusSamplingRaw value n) 2 volume := by
  have positive : 0 < (n : ℝ) + 1 := by positivity
  have qmp : Measure.QuasiMeasurePreserving
      (fun t : ℝ => ((n : ℝ) + 1) * t) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := (n : ℝ) + 1) positive.ne')
  have measurable := (Lp.memLp value).1.comp_quasiMeasurePreserving qmp
  have scaled : MemLp (fun t : ℝ => value (((n : ℝ) + 1) * t)) 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm measurable).2
    exact ((memLp_two_iff_integrable_sq_norm (Lp.memLp value).1).1
      (Lp.memLp value)).comp_mul_left' positive.ne'
  exact scaled.indicator measurableSet_burnolSamplingAnnulus

def burnolAnnulusSamplingL2 (value : BurnolL2) (n : ℕ) : BurnolL2 :=
  (burnolAnnulusSamplingRaw_memLp value n).toLp (burnolAnnulusSamplingRaw value n)

theorem burnolAnnulusSamplingL2_coeFn (value : BurnolL2) (n : ℕ) :
    (burnolAnnulusSamplingL2 value n : ℝ → ℂ) =ᵐ[volume] burnolAnnulusSamplingRaw value n :=
  (burnolAnnulusSamplingRaw_memLp value n).coeFn_toLp

/-- The original first moment pays both the reciprocal position and dilation decay. -/
theorem burnolAnnulusSamplingL2_norm_le (value : BurnolL2)
    (moment : MemLp (fun x : ℝ => (x : ℂ) * value x) 2 volume) (n : ℕ) :
    ‖burnolAnnulusSamplingL2 value n‖ ≤
      4 * ((n : ℝ) + 1) ^ (-3 / 2 : ℝ) *
        ‖moment.toLp (fun x : ℝ => (x : ℂ) * value x)‖ := by
  let a : ℝ := (n : ℝ) + 1
  have ha : 0 < a := by dsimp [a]; positivity
  let g : BurnolL2 := moment.toLp (fun x : ℝ => (x : ℂ) * value x)
  have qmp : Measure.QuasiMeasurePreserving (fun t : ℝ => a * t) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ)) (r := a) ha.ne')
  have coefficient : a ^ (-3 / 2 : ℝ) * Real.exp (Real.log a / 2) * a = 1 := by
    calc
      _ = Real.exp (Real.log a * (-3 / 2)) * Real.exp (Real.log a / 2) *
          Real.exp (Real.log a) := by rw [Real.rpow_def_of_pos ha, Real.exp_log ha]
      _ = Real.exp (Real.log a * (-3 / 2) + Real.log a / 2 + Real.log a) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ = 1 := by convert Real.exp_zero using 2; ring
  have pointwise : ∀ᵐ t ∂volume,
      ‖burnolAnnulusSamplingL2 value n t‖ ≤
        (4 * a ^ (-3 / 2 : ℝ)) * ‖burnolMultiplicativeDilation (Real.log a) g t‖ := by
    filter_upwards [burnolAnnulusSamplingL2_coeFn value n,
      burnolMultiplicativeDilation_coeFn (Real.log a) g,
      qmp.ae moment.coeFn_toLp] with t sampleRead dilationRead momentRead
    rw [sampleRead, dilationRead]
    unfold burnolL2RawNormalizedDilation
    rw [Real.exp_log ha]
    change ‖burnolSamplingAnnulus.indicator (fun t => value (a * t)) t‖ ≤
      (4 * a ^ (-3 / 2 : ℝ)) * ‖(Real.exp (Real.log a / 2) : ℂ) * g (a * t)‖
    by_cases ht : t ∈ burnolSamplingAnnulus
    · rw [Set.indicator_of_mem ht]
      change g (a * t) = (a * t : ℝ) * value (a * t) at momentRead
      rw [momentRead]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ha, abs_of_pos (Real.exp_pos _)]
      have lower : 1 ≤ 4 * |t| := by have := ht.1; linarith
      calc
        ‖value (a * t)‖ ≤ (4 * |t|) * ‖value (a * t)‖ := by
          nlinarith [norm_nonneg (value (a * t))]
        _ = (4 * |t| * ‖value (a * t)‖) *
            (a ^ (-3 / 2 : ℝ) * Real.exp (Real.log a / 2) * a) := by
          rw [coefficient, mul_one]
        _ = _ := by ring
    · rw [Set.indicator_of_notMem ht, norm_zero]
      positivity
  have normBound := Lp.norm_le_mul_norm_of_ae_le_mul pointwise
  simpa only [LinearIsometryEquiv.norm_map] using normBound

/-- The annular samples of the actual L² representative form an absolutely summable L² family. -/
theorem burnolAnnulusSamplingL2_summable (value : BurnolL2)
    (moment : MemLp (fun x : ℝ => (x : ℂ) * value x) 2 volume) :
    Summable (burnolAnnulusSamplingL2 value) := by
  have powers : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-3 / 2 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by norm_num : (-3 / 2 : ℝ) < -1))
  have bound := (powers.mul_left 4).mul_right
    ‖moment.toLp (fun x : ℝ => (x : ℂ) * value x)‖
  exact bound.of_norm_bounded (burnolAnnulusSamplingL2_norm_le value moment)

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
