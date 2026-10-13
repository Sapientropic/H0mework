import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.Cotest
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalColumnMomentSource
open Complex MeasureTheory Set Filter
open scoped Topology InnerProductSpace
open OriginalRieszSource

def wholeContactResponse (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolQuarterZeroExtension (contactResponse coordinate)
def divisorBand (h : ℝ) (n : ℕ+) : Set ℝ :=
  {y | (1/4:ℝ)/(n:ℕ) < |y| ∧ |y|≤((1/4:ℝ)*Real.exp h)/(n:ℕ)}

theorem whole_contact_response_read (coordinate : BurnolCompletedMellinCoordinate) :
    (wholeContactResponse coordinate : ℝ→ℂ)=ᵐ[volume]
      (symmetricInterval (1/4:ℝ)).indicator
        (fun x=>OriginalRieszSourceGreen.weightedRaw coordinate x-Kernel.beta coordinate-
          (star coordinate.value-1/2)*burnolRieszSingleFourierSourceRaw coordinate x) := by
  have source := (ae_restrict_iff' (measurableSet_symmetricInterval (1/4:ℝ))).mp
    (original_contact_response_read coordinate)
  filter_upwards [burnolQuarterZeroExtension_coe (contactResponse coordinate),source] with x extended actual
  rw [wholeContactResponse,extended]
  by_cases inside : x∈symmetricInterval (1/4:ℝ)
  · simp only [indicator_of_mem inside]
    exact actual inside
  · simp only [indicator_of_notMem inside]

theorem whole_contact_response_mean (coordinate : BurnolCompletedMellinCoordinate) :
    FiniteMobiusResolventFlux.actualMean (wholeContactResponse coordinate)=0 := by
  change (‖intervalConstant (1/4:ℝ)‖^2:ℂ)⁻¹ *
    inner ℂ (intervalConstant (1/4:ℝ)) (burnolRadiusRestriction (1/4:ℝ)
      (burnolQuarterZeroExtension (contactResponse coordinate)))=0
  change (‖intervalConstant (1/4:ℝ)‖^2:ℂ)⁻¹ * inner ℂ (intervalConstant (1/4:ℝ))
    (burnolRadiusRestriction (1/4:ℝ) (burnolRadiusZeroExtension (1/4:ℝ) (contactResponse coordinate)))=0
  rw [burnolRadiusRestriction_zeroExtension]
  have mean := Constructor.mean_zero (Kernel.A coordinate • Response.u-Kernel.beta coordinate • Response.v)
  change burnolQuarterMeanCoefficient (contactResponse coordinate)=0 at mean
  simpa only [burnolQuarterMeanCoefficient,Complex.ofReal_pow,div_eq_mul_inv,mul_comm] using mean

theorem whole_contact_response_supported (coordinate : BurnolCompletedMellinCoordinate) :
    OriginalPaPhysicalGreen.originalPhysicalCutoff (1/4:ℝ) (wholeContactResponse coordinate)=wholeContactResponse coordinate := by
  change burnolRadiusZeroExtension (1/4:ℝ) (burnolRadiusRestriction (1/4:ℝ)
    (burnolRadiusZeroExtension (1/4:ℝ) (contactResponse coordinate)))=_
  rw [burnolRadiusRestriction_zeroExtension]
  rfl

theorem unit_response_column_zero (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0≤h) :
    inner ℂ (Paid.pairedColumn coordinate h) (wholeContactResponse coordinate)=0 := by
  rw [original_paired_sample_positive coordinate h nonnegative,L2.inner_def]
  apply integral_eq_zero_of_ae
  have source := OriginalPaPhysicalGreen.originalPhysicalCutoff_coeFn (1/4:ℝ) (wholeContactResponse coordinate)
  rw [whole_contact_response_supported] at source
  filter_upwards [source,burnolAnnulusSamplingL2_coeFn (OriginalRieszFiniteColumns.fourierColumn coordinate h) 0] with x actual sampled
  simp only [Pi.zero_apply]
  rw [sampled]
  unfold burnolAnnulusSamplingRaw
  simp only [Nat.cast_zero,zero_add,one_mul]
  by_cases annulus : x∈burnolSamplingAnnulus
  · rw [indicator_of_mem annulus,actual,indicator_of_notMem (show x∉symmetricInterval (1/4:ℝ) from fun inside=>not_le_of_gt annulus.1 (abs_le.mpr inside)),inner_zero_right]
  · rw [indicator_of_notMem annulus,inner_zero_left]

-- The actual finite Mobius pullback retains its own mean and consumes the original response incidence.
theorem actual_lower_response_read (coordinate : BurnolCompletedMellinCoordinate) (n : ℕ+) :
    (FiniteMobiusResolventFlux.lowerPullback n (wholeContactResponse coordinate):ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval 4)]
      fun x=>(symmetricInterval (1/4:ℝ)).indicator
        (fun y=>OriginalRieszSourceGreen.weightedRaw coordinate y-Kernel.beta coordinate-
          (star coordinate.value-1/2)*burnolRieszSingleFourierSourceRaw coordinate y) (x/(n:ℕ))-
          FiniteMobiusResolventFlux.actualMean (wholeContactResponse coordinate) := by
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ=>x/(n:ℕ)) volume volume := by
    simpa only [div_eq_mul_inv,mul_comm,smul_eq_mul] using
      Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ)) (r:=((n:ℕ):ℝ)⁻¹)
        (inv_ne_zero (by exact_mod_cast n.ne_zero))
  filter_upwards [FiniteMobiusResolventFlux.lower_pullback_read n (wholeContactResponse coordinate),
    ae_restrict_of_ae (qmp.ae_eq (whole_contact_response_read coordinate))] with x pulled generated
  simp only [Function.comp_def] at generated
  rw [pulled,generated]

 theorem divisor_response_endpoints (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bounded : h≤Real.log 2) (n : ℕ+) (nonunit : n≠1) :
    (∫ y : ℝ in ((1/4:ℝ)/(n:ℕ))..(((1/4:ℝ)*Real.exp h)/(n:ℕ)),
      sourceCotest coordinate (((n:ℕ):ℝ)*Real.exp (-h)) y*contactResponse coordinate y)=
      sourceCotest coordinate (((n:ℕ):ℝ)*Real.exp (-h)) (((1/4:ℝ)*Real.exp h)/(n:ℕ))*
        ((((1/4:ℝ)*Real.exp h)/(n:ℕ)):ℂ)*burnolRieszSingleFourierSourceRaw coordinate (((1/4:ℝ)*Real.exp h)/(n:ℕ))-
      sourceCotest coordinate (((n:ℕ):ℝ)*Real.exp (-h)) ((1/4:ℝ)/(n:ℕ))*
        (((1/4:ℝ)/(n:ℕ)):ℂ)*burnolRieszSingleFourierSourceRaw coordinate ((1/4:ℝ)/(n:ℕ))-
      (∫ y : ℝ in ((1/4:ℝ)/(n:ℕ))..(((1/4:ℝ)*Real.exp h)/(n:ℕ)),
        ((y:ℂ)*sourceCotestDerivative coordinate (((n:ℕ):ℝ)*Real.exp (-h)) y+
          star coordinate.value*sourceCotest coordinate (((n:ℕ):ℝ)*Real.exp (-h)) y)*burnolRieszSingleFourierSourceRaw coordinate y)-
      Kernel.beta coordinate*(∫ y : ℝ in ((1/4:ℝ)/(n:ℕ))..(((1/4:ℝ)*Real.exp h)/(n:ℕ)),
        sourceCotest coordinate (((n:ℕ):ℝ)*Real.exp (-h)) y) := by
  have positive : (0:ℝ)<(n:ℕ) := by exact_mod_cast n.property
  have two : (2:ℝ)≤(n:ℕ) := by
    have nonunitNat : (n:ℕ)≠1 := by intro same;exact nonunit (PNat.coe_injective same)
    exact_mod_cast (lt_of_le_of_ne (show 1≤(n:ℕ) from n.property) (Ne.symm nonunitNat))
  have growth : 1≤Real.exp h := Real.one_le_exp_iff.mpr nonnegative
  have small : Real.exp h≤2 := by simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using Real.exp_le_exp.mpr bounded
  have lower : 0<(1/4:ℝ)/(n:ℕ) := div_pos (by norm_num) positive
  have ordered : (1/4:ℝ)/(n:ℕ)≤((1/4:ℝ)*Real.exp h)/(n:ℕ) :=
    div_le_div_of_nonneg_right (by nlinarith) positive.le
  have quarter : ((1/4:ℝ)*Real.exp h)/(n:ℕ)≤(1/4:ℝ) := by
    apply (div_le_iff₀ positive).mpr
    nlinarith
  simpa only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_natCast] using
    actual_cotest_band_response coordinate (((n:ℕ):ℝ)*Real.exp (-h)) (mul_pos positive (Real.exp_pos _))
      ((1/4:ℝ)/(n:ℕ)) (((1/4:ℝ)*Real.exp h)/(n:ℕ)) lower ordered quarter

end OriginalColumnMomentSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
