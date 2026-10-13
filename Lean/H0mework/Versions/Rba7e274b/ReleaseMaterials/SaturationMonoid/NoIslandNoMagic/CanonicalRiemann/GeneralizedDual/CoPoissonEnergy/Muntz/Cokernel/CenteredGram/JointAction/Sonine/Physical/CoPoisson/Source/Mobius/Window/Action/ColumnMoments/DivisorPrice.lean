import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.ColumnPullback
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalColumnMomentSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology BigOperators
open OriginalRieszSource

def responseEndpointPrice (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (n : ℕ+) : ℂ :=
  let scale : ℝ := (n:ℕ)*Real.exp (-h)
  let lower : ℝ := (1/4:ℝ)/(n:ℕ)
  let upper : ℝ := (1/4:ℝ)*Real.exp h/(n:ℕ)
  sourceCotest coordinate scale upper*(upper:ℂ)*burnolRieszSingleFourierSourceRaw coordinate upper-
    sourceCotest coordinate scale lower*(lower:ℂ)*burnolRieszSingleFourierSourceRaw coordinate lower-
    (∫ y : ℝ in lower..upper,((y:ℂ)*sourceCotestDerivative coordinate scale y+
      star coordinate.value*sourceCotest coordinate scale y)*burnolRieszSingleFourierSourceRaw coordinate y)-
    Kernel.beta coordinate*(∫ y : ℝ in lower..upper,sourceCotest coordinate scale y)

theorem original_B_quarter_raw (coordinate : BurnolCompletedMellinCoordinate) :
    (originalB coordinate:ℝ→ℂ)=ᵐ[volume]
      (symmetricInterval (1/4:ℝ)).indicator (burnolRieszSingleFourierSourceRaw coordinate) := by
  have read := (ae_restrict_iff' (measurableSet_symmetricInterval (1/4:ℝ))).mp (burnolRieszSingleFourierSource_ae_raw coordinate)
  filter_upwards [burnolQuarterZeroExtension_coe (burnolRieszSingleFourierSource coordinate:BurnolQuarterIntervalL2),read] with x extended actual
  unfold originalB
  rw [extended]
  by_cases inside : x∈symmetricInterval (1/4:ℝ)
  · simp only [indicator_of_mem inside]
    exact actual inside
  · simp only [indicator_of_notMem inside]

 theorem original_response_divisor_price (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bounded : h≤Real.log 2) (n : ℕ+) (nonunit : n≠1) :
    inner ℂ (Paid.pairedColumn coordinate h) (F.fullPullback n (wholeContactResponse coordinate))=
      -(2:ℂ)*(Real.exp (-h/2):ℂ)*(n:ℕ)*responseEndpointPrice coordinate h n := by
  rw [column_response_divisor_read coordinate h nonnegative bounded]
  have positive : (0:ℝ)<(n:ℕ) := by exact_mod_cast n.property
  have growth : 1≤Real.exp h := Real.one_le_exp_iff.mpr nonnegative
  have small : Real.exp h≤2 := by simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using Real.exp_le_exp.mpr bounded
  have two : (2:ℝ)≤(n:ℕ) := by
    have different : (n:ℕ)≠1 := by intro same;exact nonunit (PNat.coe_injective same)
    exact_mod_cast (lt_of_le_of_ne (show 1≤(n:ℕ) from n.property) (Ne.symm different))
  let factor : ℝ := ((n:ℕ):ℝ)*Real.exp (-h)
  have factorPositive : 0<factor := mul_pos positive (Real.exp_pos _)
  have rawIntegral : (∫ y : ℝ in ((1/4:ℝ)*Real.exp (-h))..(1/4:ℝ),
      star (originalB coordinate y)*wholeContactResponse coordinate (Real.exp h*y/(n:ℕ)))=
    (∫ y : ℝ in ((1/4:ℝ)*Real.exp (-h))..(1/4:ℝ),
      (fun z : ℝ=>sourceCotest coordinate factor z*contactResponse coordinate z) (factor⁻¹*y)) := by
    apply intervalIntegral.integral_congr_ae_restrict
    have qmp : Measure.QuasiMeasurePreserving (fun y : ℝ=>factor⁻¹*y) volume volume := by
      simpa only [smul_eq_mul] using Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ))
        (r:=factor⁻¹) (inv_ne_zero factorPositive.ne')
    have source := (ae_restrict_iff' (measurableSet_symmetricInterval (1/4:ℝ))).mp
      (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval (1/4:ℝ)) (wholeContactResponse coordinate))
    have restriction : burnolRadiusRestriction (1/4:ℝ) (wholeContactResponse coordinate)=contactResponse coordinate := by
      change burnolRadiusRestriction (1/4:ℝ) (burnolRadiusZeroExtension (1/4:ℝ) (contactResponse coordinate))=_
      rw [burnolRadiusRestriction_zeroExtension]
    change ∀ᵐ x : ℝ ∂volume,x∈symmetricInterval (1/4:ℝ)→
      burnolRadiusRestriction (1/4:ℝ) (wholeContactResponse coordinate) x=wholeContactResponse coordinate x at source
    rw [restriction] at source
    filter_upwards [ae_restrict_of_ae (original_B_quarter_raw coordinate),
      ae_restrict_of_ae (qmp.ae source),ae_restrict_mem measurableSet_uIoc] with y original actual inside
    have order : (1/4:ℝ)*Real.exp (-h)≤(1/4:ℝ) := by nlinarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr nonnegative)]
    have band : y∈Ioc ((1/4:ℝ)*Real.exp (-h)) (1/4:ℝ) := by simpa only [uIoc_of_le order] using inside
    have yPositive : 0<y := lt_trans (mul_pos (by norm_num) (Real.exp_pos _)) band.1
    have yQuarter : y∈symmetricInterval (1/4:ℝ) := ⟨by linarith,band.2⟩
    have scaled : factor⁻¹*y=Real.exp h*y/(n:ℕ) := by
      dsimp only [factor]
      rw [mul_inv_rev,Real.exp_neg,inv_inv]
      field_simp
    have scaledQuarter : factor⁻¹*y∈symmetricInterval (1/4:ℝ) := by
      rw [scaled]
      have lower := div_nonneg (mul_nonneg (Real.exp_pos h).le yPositive.le) positive.le
      have upper : Real.exp h*y/(n:ℕ)≤(1/4:ℝ) := by
        apply (div_le_iff₀ positive).mpr
        nlinarith [mul_le_mul_of_nonneg_left band.2 (Real.exp_pos h).le]
      exact ⟨by linarith,upper⟩
    rw [original,indicator_of_mem yQuarter,scaled]
    unfold sourceCotest
    rw [← scaled,actual scaledQuarter]
    have inverse : factor*(factor⁻¹*y)=y := by rw [← mul_assoc,mul_inv_cancel₀ factorPositive.ne',one_mul]
    rw [inverse]
  rw [rawIntegral]
  have changeSource := intervalIntegral.integral_comp_mul_left
    (fun z : ℝ=>sourceCotest coordinate factor z*contactResponse coordinate z)
    (a:=((1/4:ℝ)*Real.exp (-h))) (b:=(1/4:ℝ)) (c:=factor⁻¹) (inv_ne_zero factorPositive.ne')
  rw [changeSource]
  have lower : factor⁻¹*((1/4:ℝ)*Real.exp (-h))=(1/4:ℝ)/(n:ℕ) := by
    dsimp only [factor]
    field_simp
  have upper : factor⁻¹*(1/4:ℝ)=((1/4:ℝ)*Real.exp h)/(n:ℕ) := by
    dsimp only [factor]
    rw [Real.exp_neg]
    field_simp
  rw [lower,upper,inv_inv]
  change -(2:ℂ)*(Real.exp (h/2):ℂ)*
    ((factor:ℂ)*(∫ y : ℝ in ((1/4:ℝ)/(n:ℕ))..(((1/4:ℝ)*Real.exp h)/(n:ℕ)),
      sourceCotest coordinate factor y*contactResponse coordinate y))=_
  have source : (∫ y : ℝ in ((1/4:ℝ)/(n:ℕ))..(((1/4:ℝ)*Real.exp h)/(n:ℕ)),
      sourceCotest coordinate factor y*contactResponse coordinate y)=responseEndpointPrice coordinate h n := by
    simpa only [responseEndpointPrice,factor,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_natCast] using
      divisor_response_endpoints coordinate h nonnegative bounded n nonunit
  rw [source]
  have phase : (Real.exp (h/2):ℂ)*(Real.exp (-h):ℂ)=(Real.exp (-h/2):ℂ) := by
    rw [← Complex.ofReal_mul,← Real.exp_add]
    congr 2
    ring
  unfold factor
  rw [Complex.ofReal_mul,Complex.ofReal_natCast]
  have scalar : -(2:ℂ)*(Real.exp (h/2):ℂ)*(((n:ℕ):ℂ)*(Real.exp (-h):ℂ))=
      -(2:ℂ)*(Real.exp (-h/2):ℂ)*(n:ℕ) := by
    calc
      _=-(2:ℂ)*((Real.exp (h/2):ℂ)*(Real.exp (-h):ℂ))*(n:ℕ) := by ring
      _=_ := by rw [phase]
  rw [← mul_assoc,scalar]

end OriginalColumnMomentSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
