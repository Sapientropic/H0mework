import H0mework.Versions.V2.Arithmetic.RemainderSource.Recovery
import H0mework.Versions.V2.Arithmetic.RiemannResolvent.CompleteRemainder

/-! Homogeneous inner germs are faithful under the actual comb-remainder read.
A contracted dilation difference has the existing inner gap; its vanishing
forces a strictly contractive eigencharacter of an isometry to be zero. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter FourierTransform
open scoped InnerProductSpace Topology
noncomputable section

private theorem innerPower_profile_dilation (s amplitude : ℂ) (h x : ℝ) :
    (Real.exp (h / 2) : ℂ) * (amplitude * (((|Real.exp h * x| : ℝ) : ℂ) ^ (s - 1))) =
      Complex.exp ((s - 1 / 2) * (h : ℂ)) * (amplitude * (((|x| : ℝ) : ℂ) ^ (s - 1))) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos h), Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (Real.exp_pos h).le (abs_nonneg x)]
  have power : (Real.exp h : ℂ) ^ (s - 1) = Complex.exp ((h : ℂ) * (s - 1)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero h)),
      ← Complex.ofReal_log (Real.exp_pos h).le, Real.log_exp]
  rw [power, Complex.ofReal_exp]
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
  calc
    _ = (Complex.exp ((h : ℂ) / 2) * Complex.exp ((h : ℂ) * (s - 1))) *
        (amplitude * (((|x| : ℝ) : ℂ) ^ (s - 1))) := by ring
    _ = _ := by rw [← Complex.exp_add]; congr 2; ring

theorem burnolRemainderSourceRead_faithful_of_innerPower (s : ℂ) (rightHalf : 1 / 2 < s.re)
    (amplitude : ℂ) (source : BurnolL2) (even : reflectL2 source = source)
    (germ : (source : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))]
      fun x => amplitude * (((|x| : ℝ) : ℂ) ^ (s - 1)))
    (readZero : ∀ test : SchwartzMap ℝ ℂ, burnolRemainderSourceRead source test = 0) :
    source = 0 := by
  let character := Complex.exp ((s - 1 / 2) * (-1 : ℂ))
  let delta := burnolMultiplicativeDilation (-1) source - character • source
  have globalGerm : ∀ᵐ x : ℝ ∂volume, x ∈ symmetricInterval (1 / 4 : ℝ) →
      source x = amplitude * (((|x| : ℝ) : ℂ) ^ (s - 1)) :=
    (ae_restrict_iff' (measurableSet_symmetricInterval (1 / 4 : ℝ))).mp germ
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp (-1) * x) volume volume := by
    simpa only [smul_eq_mul] using (Measure.quasiMeasurePreserving_smul
      (μ := (volume : Measure ℝ)) (r := Real.exp (-1)) (Real.exp_ne_zero _))
  have gap : (delta : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => 0 := by
    filter_upwards [ae_restrict_of_ae globalGerm, ae_restrict_of_ae (qmp.ae globalGerm),
      ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn (-1) source),
      ae_restrict_of_ae (Lp.coeFn_sub (burnolMultiplicativeDilation (-1) source) (character • source)),
      ae_restrict_of_ae (Lp.coeFn_smul character source),
      ae_restrict_mem (measurableSet_symmetricInterval (1 / 4 : ℝ))]
        with x original scaled acted difference scalar inside
    have scaledInside : Real.exp (-1) * x ∈ symmetricInterval (1 / 4 : ℝ) := by
      apply abs_le.mp
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      have small : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      nlinarith [abs_nonneg x, abs_le.mpr inside, Real.exp_pos (-1)]
    change (burnolMultiplicativeDilation (-1) source - character • source : BurnolL2) x = 0
    rw [difference]
    change burnolMultiplicativeDilation (-1) source x - (character • source : BurnolL2) x = 0
    rw [scalar, acted]
    change burnolL2RawNormalizedDilation (-1) source x - character * source x = 0
    unfold burnolL2RawNormalizedDilation
    rw [scaled scaledInside, original inside, innerPower_profile_dilation]
    simp [character]
  have deltaZero : delta = 0 := by
    apply burnolRemainderSourceRead_faithful delta
    · change reflectL2 (burnolMultiplicativeDilation (-1) source - character • source) = _
      rw [map_sub, reflectL2_burnolMultiplicativeDilation, map_smul, even]
    · exact gap
    · intro test
      change burnolRemainderSourceRead
        (burnolMultiplicativeDilation (-1) source - character • source) test = 0
      rw [← burnolRemainderSourceReadCLM_apply, map_sub, map_smul,
        burnolRemainderSourceReadCLM_apply, burnolRemainderSourceReadCLM_apply,
        burnolRemainderSourceRead_dilation, readZero, readZero]
      simp
  have eigen : burnolMultiplicativeDilation (-1) source = character • source := sub_eq_zero.mp deltaZero
  have normEquation := congrArg norm eigen
  rw [(burnolMultiplicativeDilation (-1)).norm_map, norm_smul] at normEquation
  have contraction : ‖character‖ < 1 := by
    change ‖Complex.exp ((s - 1 / 2) * (-1 : ℂ))‖ < 1
    rw [Complex.norm_exp]
    apply Real.exp_lt_one_iff.mpr
    norm_num
    linarith
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg source]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
