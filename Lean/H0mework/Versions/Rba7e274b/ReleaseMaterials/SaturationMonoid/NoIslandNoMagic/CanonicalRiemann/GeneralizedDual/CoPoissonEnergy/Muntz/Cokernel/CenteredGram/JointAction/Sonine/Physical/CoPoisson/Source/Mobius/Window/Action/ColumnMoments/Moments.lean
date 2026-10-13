import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.Change
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalColumnMomentSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace
namespace Paid
export OriginalPrimitiveRankBalance (pairedColumn conjugateCoordinate)
export FiniteMobiusResolventFlux (box box_read interiorBase interior_base_read)
end Paid

def bandMass (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  -(Real.exp (h/2):ℂ)*star (∫ y : ℝ in innerBand h,originalB coordinate y)
def bandPower (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  fullMellinTranslationCharacter (star coordinate.value) (-h)*
    (∫ y : ℝ in innerBand h,star (originalB coordinate y)*((|y|:ℝ):ℂ)^(star coordinate.value-1))

 theorem outer_band_small (h : ℝ) (bounded : h≤Real.log 2) {x : ℝ} (inside : x∈outerBand h) : |x|<4 := by
  have small : Real.exp h≤2 := by simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using Real.exp_le_exp.mpr bounded
  exact lt_of_le_of_lt (inside.2.trans (mul_le_mul_of_nonneg_left small (by norm_num))) (by norm_num)

 theorem original_mass_source (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    inner ℂ (Paid.pairedColumn coordinate h) (Paid.box 4)=bandMass coordinate h := by
  rw [original_paired_sample_positive coordinate h nonnegative,L2.inner_def]
  have raw : (fun x=>inner ℂ (burnolAnnulusSamplingL2 (OriginalRieszFiniteColumns.fourierColumn coordinate h) 0 x)
      (Paid.box 4 x))=ᵐ[volume]
      (outerBand h).indicator (fun x=>-(Real.exp (-h/2):ℂ)*star (originalB coordinate (Real.exp (-h)*x))) := by
    filter_upwards [original_positive_sample_raw coordinate h nonnegative bounded,Paid.box_read 4] with x source box
    rw [source,box]
    by_cases inside : x∈outerBand h
    · have boxed : x∈symmetricInterval 4 := abs_le.mp (outer_band_small h bounded inside).le
      simp only [indicator_of_mem inside,indicator_of_mem boxed]
      rw [RCLike.inner_apply]
      simp only [map_mul,map_neg,conj_ofReal,one_mul]
      rfl
    · simp only [indicator_of_notMem inside,inner_zero_left]
  rw [integral_congr_ae raw,integral_indicator (measurable_outerBand h),integral_const_mul,
    source_band_change h (fun y=>star (originalB coordinate y))]
  change -(Real.exp (-h/2):ℂ)*((Real.exp h:ℂ)*(∫ y : ℝ in innerBand h, (starRingEnd ℂ) (originalB coordinate y)))=_
  rw [integral_conj]
  unfold bandMass
  have phase : (Real.exp (-h/2):ℂ)*(Real.exp h:ℂ)=(Real.exp (h/2):ℂ) := by
    rw [← Complex.ofReal_mul,← Real.exp_add]
    congr 2
    ring
  rw [← mul_assoc,neg_mul,phase]
  rfl

 theorem original_power_source (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    inner ℂ (Paid.pairedColumn coordinate h) (Paid.interiorBase (Paid.conjugateCoordinate coordinate))=bandPower coordinate h := by
  rw [original_paired_sample_positive coordinate h nonnegative,L2.inner_def]
  have raw : (fun x=>inner ℂ (burnolAnnulusSamplingL2 (OriginalRieszFiniteColumns.fourierColumn coordinate h) 0 x)
      (Paid.interiorBase (Paid.conjugateCoordinate coordinate) x))=ᵐ[volume]
      (outerBand h).indicator (fun x=>(Real.exp (-h/2):ℂ)*
        (star (originalB coordinate (Real.exp (-h)*x))*((|x|:ℝ):ℂ)^(star coordinate.value-1))) := by
    filter_upwards [original_positive_sample_raw coordinate h nonnegative bounded,
      Paid.interior_base_read (Paid.conjugateCoordinate coordinate)] with x source power
    rw [source,power]
    by_cases inside : x∈outerBand h
    · simp only [indicator_of_mem inside,if_pos (outer_band_small h bounded inside)]
      rw [RCLike.inner_apply]
      simp only [map_mul,map_neg,conj_ofReal,Paid.conjugateCoordinate]
      change -((|x|:ℝ):ℂ)^(star coordinate.value-1)*(-(Real.exp (-h/2):ℂ)*star (originalB coordinate (Real.exp (-h)*x)))=_
      ring
    · simp only [indicator_of_notMem inside,inner_zero_left]
  rw [integral_congr_ae raw,integral_indicator (measurable_outerBand h),integral_const_mul,
    weighted_source_band_change h (fun y=>star (originalB coordinate y)) (star coordinate.value-1)]
  unfold bandPower
  rw [← mul_assoc,half_density_weight_character]

end OriginalColumnMomentSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
