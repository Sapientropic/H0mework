import H0mework.Versions.V2.Arithmetic.BurnolPhysical.QuarterMellinAdditiveRechartNorm
import H0mework.Versions.R2.Arithmetic.RiemannSpectral.MultiplicativeDilation

/-!
# Direct L² realization of the installed Burnol dilation

The Schwartz-dense extension is identified with its canonical normalized
multiplicative representative on every Burnol L² state.  This supplies the
pointwise action law needed by source recharts without replacing the existing
dilation.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex MeasureTheory
open scoped ENNReal InnerProductSpace SchwartzMap

noncomputable section

/-- Canonical representative formula for normalized multiplicative dilation
on the full Burnol L² carrier. -/
def burnolL2RawNormalizedDilation
    (h : ℝ) (value : BurnolL2) (x : ℝ) : ℂ :=
  (Real.exp (h / 2) : ℂ) * value (Real.exp h * x)

private theorem burnolL2RawNormalizedDilation_memLp
    (h : ℝ) (value : BurnolL2) :
    MemLp (burnolL2RawNormalizedDilation h value) 2 volume := by
  have qmp : Measure.QuasiMeasurePreserving
      (fun x : ℝ => Real.exp h * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp h) (Real.exp_ne_zero h))
  have measurable : AEStronglyMeasurable
      (burnolL2RawNormalizedDilation h value) volume :=
    ((Lp.memLp value).1.comp_quasiMeasurePreserving qmp).const_smul
      (Real.exp (h / 2) : ℂ)
  rw [memLp_two_iff_integrable_sq_norm measurable]
  have inputIntegrable : Integrable (fun x : ℝ => ‖value x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp value).1).mp
      (Lp.memLp value)
  have composedIntegrable :
      Integrable (fun x : ℝ => ‖value (Real.exp h * x)‖ ^ 2) :=
    inputIntegrable.comp_mul_left' (Real.exp_ne_zero h)
  exact (composedIntegrable.const_mul (Real.exp h)).congr
    (ae_of_all volume fun x => by
      unfold burnolL2RawNormalizedDilation
      change Real.exp h * ‖value (Real.exp h * x)‖ ^ 2 =
        ‖(Real.exp (h / 2) : ℂ) * value (Real.exp h * x)‖ ^ 2
      rw [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow,
        ← Real.exp_nat_mul]
      congr 2
      ring)

def burnolL2DirectDilationValue
    (h : ℝ) (value : BurnolL2) : BurnolL2 :=
  (burnolL2RawNormalizedDilation_memLp h value).toLp
    (burnolL2RawNormalizedDilation h value)

theorem burnolL2DirectDilationValue_coeFn
    (h : ℝ) (value : BurnolL2) :
    (burnolL2DirectDilationValue h value : ℝ → ℂ) =ᵐ[volume]
      burnolL2RawNormalizedDilation h value :=
  MemLp.coeFn_toLp (burnolL2RawNormalizedDilation_memLp h value)

private theorem burnolL2DirectDilationValue_add
    (h : ℝ) (left right : BurnolL2) :
    burnolL2DirectDilationValue h (left + right) =
      burnolL2DirectDilationValue h left +
        burnolL2DirectDilationValue h right := by
  apply Lp.ext
  have qmp : Measure.QuasiMeasurePreserving
      (fun x : ℝ => Real.exp h * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp h) (Real.exp_ne_zero h))
  filter_upwards [
    burnolL2DirectDilationValue_coeFn h (left + right),
    burnolL2DirectDilationValue_coeFn h left,
    burnolL2DirectDilationValue_coeFn h right,
    Lp.coeFn_add (burnolL2DirectDilationValue h left)
      (burnolL2DirectDilationValue h right),
    qmp.ae (Lp.coeFn_add left right)]
      with x sourceSum sourceLeft sourceRight targetAdd inputAdd
  rw [sourceSum, targetAdd]
  change burnolL2RawNormalizedDilation h (left + right) x =
    burnolL2DirectDilationValue h left x +
      burnolL2DirectDilationValue h right x
  rw [sourceLeft, sourceRight]
  unfold burnolL2RawNormalizedDilation
  rw [inputAdd]
  change (Real.exp (h / 2) : ℂ) *
      (left (Real.exp h * x) + right (Real.exp h * x)) = _
  ring

private theorem burnolL2DirectDilationValue_smul
    (h : ℝ) (coefficient : ℂ) (value : BurnolL2) :
    burnolL2DirectDilationValue h (coefficient • value) =
      coefficient • burnolL2DirectDilationValue h value := by
  apply Lp.ext
  have qmp : Measure.QuasiMeasurePreserving
      (fun x : ℝ => Real.exp h * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp h) (Real.exp_ne_zero h))
  filter_upwards [
    burnolL2DirectDilationValue_coeFn h (coefficient • value),
    burnolL2DirectDilationValue_coeFn h value,
    Lp.coeFn_smul coefficient (burnolL2DirectDilationValue h value),
    qmp.ae (Lp.coeFn_smul coefficient value)]
      with x sourceScaled sourceValue targetScaled inputScaled
  rw [sourceScaled, targetScaled]
  change burnolL2RawNormalizedDilation h (coefficient • value) x =
    coefficient * burnolL2DirectDilationValue h value x
  rw [sourceValue]
  unfold burnolL2RawNormalizedDilation
  rw [inputScaled]
  change (Real.exp (h / 2) : ℂ) *
      (coefficient * value (Real.exp h * x)) =
    coefficient * ((Real.exp (h / 2) : ℂ) *
      value (Real.exp h * x))
  ring

def burnolL2DirectDilationLinear (h : ℝ) :
    BurnolL2 →ₗ[ℂ] BurnolL2 where
  toFun := burnolL2DirectDilationValue h
  map_add' := burnolL2DirectDilationValue_add h
  map_smul' := burnolL2DirectDilationValue_smul h

private theorem burnolL2DirectDilationValue_norm
    (h : ℝ) (value : BurnolL2) :
    ‖burnolL2DirectDilationValue h value‖ = ‖value‖ := by
  have squareEq :
      ‖burnolL2DirectDilationValue h value‖ ^ 2 = ‖value‖ ^ 2 := by
    rw [burnolL2_norm_sq_eq_integral_norm_sq,
      burnolL2_norm_sq_eq_integral_norm_sq]
    have targetRead := burnolL2DirectDilationValue_coeFn h value
    calc
      (∫ x : ℝ, ‖burnolL2DirectDilationValue h value x‖ ^ 2) =
          ∫ x : ℝ, ‖burnolL2RawNormalizedDilation h value x‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [targetRead] with x read
        rw [read]
      _ = ∫ x : ℝ,
          Real.exp h * ‖value (Real.exp h * x)‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with x
        unfold burnolL2RawNormalizedDilation
        rw [norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow,
          ← Real.exp_nat_mul]
        congr 2
        ring
      _ = ∫ x : ℝ, ‖value x‖ ^ 2 := by
        rw [integral_const_mul]
        let integrand : ℝ → ℝ := fun x => ‖value x‖ ^ 2
        have change := Measure.integral_comp_mul_left integrand (Real.exp h)
        change (Real.exp h) •
            (∫ x : ℝ, integrand (Real.exp h * x)) =
          ∫ x : ℝ, integrand x
        rw [change, abs_of_pos (inv_pos.mpr (Real.exp_pos h)), smul_smul,
          mul_inv_cancel₀ (Real.exp_ne_zero h), one_smul]
  nlinarith [norm_nonneg (burnolL2DirectDilationValue h value),
    norm_nonneg value]

def burnolL2DirectDilationIsometry (h : ℝ) :
    BurnolL2 →ₗᵢ[ℂ] BurnolL2 where
  toLinearMap := burnolL2DirectDilationLinear h
  norm_map' := burnolL2DirectDilationValue_norm h

private theorem complexExp_cpow_half_for_directDilation (h : ℝ) :
    (Real.exp h : ℂ) ^ (1 / 2 : ℂ) =
      (Real.exp (h / 2) : ℂ) := by
  calc
    _ = ((Real.exp h ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      symm
      convert Complex.ofReal_cpow (Real.exp_pos h).le (1 / 2 : ℝ) using 1
      all_goals norm_num
    _ = _ := by
      congr 1
      rw [Real.rpow_def_of_pos (Real.exp_pos h), Real.log_exp]
      congr 1
      ring

private theorem burnolL2DirectDilationIsometry_schwartz
    (h : ℝ) (test : SchwartzMap ℝ ℂ) :
    burnolL2DirectDilationIsometry h
        (test.toLp 2 (volume : Measure ℝ)) =
      (coPoissonSchwartzEnergyTranslationEquiv h test).toLp 2
        (volume : Measure ℝ) := by
  apply Lp.ext
  have qmp : Measure.QuasiMeasurePreserving
      (fun x : ℝ => Real.exp h * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp h) (Real.exp_ne_zero h))
  filter_upwards [
    burnolL2DirectDilationValue_coeFn h
      (test.toLp 2 (volume : Measure ℝ)),
    (coPoissonSchwartzEnergyTranslationEquiv h test).coeFn_toLp
      2 (volume : Measure ℝ),
    qmp.ae (test.coeFn_toLp 2 (volume : Measure ℝ))]
      with x directRead targetRead inputRead
  change burnolL2DirectDilationValue h
      (test.toLp 2 (volume : Measure ℝ)) x =
    (coPoissonSchwartzEnergyTranslationEquiv h test).toLp
      2 (volume : Measure ℝ) x
  rw [directRead, targetRead]
  unfold burnolL2RawNormalizedDilation
  rw [inputRead]
  simp only [coPoissonSchwartzEnergyTranslationEquiv_apply,
    coPoissonSchwartzEnergyTranslation, LinearMap.coe_mk, AddHom.coe_mk,
    smul_apply, ClozelEndpointSourceEffect.scaledSchwartzTest_apply,
    smul_eq_mul, complexExp_cpow_half_for_directDilation]

/-- The dense-extension definition of the installed Burnol dilation has the
canonical normalized multiplicative representative formula on every L²
state. -/
theorem burnolMultiplicativeDilation_eq_direct (h : ℝ) :
    (burnolMultiplicativeDilation h).toLinearIsometry =
      burnolL2DirectDilationIsometry h := by
  apply LinearIsometry.ext
  intro value
  apply DenseRange.induction_on (p := fun value : BurnolL2 ↦
      burnolMultiplicativeDilation h value =
        burnolL2DirectDilationIsometry h value)
    (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2)
      (μ := (volume : Measure ℝ)) ENNReal.ofNat_ne_top) value
  · apply isClosed_eq
    · exact (burnolMultiplicativeDilation h).continuous
    · exact (burnolL2DirectDilationIsometry h).continuous
  · intro test
    change burnolMultiplicativeDilation h
        (test.toLp 2 (volume : Measure ℝ)) =
      burnolL2DirectDilationIsometry h
        (test.toLp 2 (volume : Measure ℝ))
    rw [burnolMultiplicativeDilation_schwartz]
    exact (burnolL2DirectDilationIsometry_schwartz h test).symm

theorem burnolMultiplicativeDilation_coeFn
    (h : ℝ) (value : BurnolL2) :
    (burnolMultiplicativeDilation h value : ℝ → ℂ) =ᵐ[volume]
      burnolL2RawNormalizedDilation h value := by
  have actionEq : burnolMultiplicativeDilation h value =
      burnolL2DirectDilationIsometry h value :=
    congrArg (fun action : BurnolL2 →ₗᵢ[ℂ] BurnolL2 => action value)
      (burnolMultiplicativeDilation_eq_direct h)
  rw [actionEq]
  exact burnolL2DirectDilationValue_coeFn h value

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
