import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.VolterraWord
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalColumnMomentSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace BigOperators

def generatedResponseRead (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  ∫ x : ℝ in outerBand h,-(Real.exp (-h/2):ℂ)*star (originalB coordinate (Real.exp (-h)*x))*
    generatedResponseProfile coordinate |x|

-- Both physical legs come from the same source-even response; arbitrary material increments are not erased.
theorem original_Rplus_response_read (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    inner ℂ (Paid.pairedColumn coordinate h)
      (S.Rplus (star coordinate.value/2) (FiniteMobiusResolventFlux.M (wholeContactResponse coordinate)))=
      generatedResponseRead coordinate h := by
  let value := S.Rplus (star coordinate.value/2) (FiniteMobiusResolventFlux.M (wholeContactResponse coordinate))
  have meanEven : reflectL2 (FiniteMobiusResolventFlux.M (wholeContactResponse coordinate))=
      FiniteMobiusResolventFlux.M (wholeContactResponse coordinate) := by
    rw [actual_response_full_word]
    simp only [map_sum,map_smul,full_pullback_even]
  have even : reflectL2 value=value := by
    exact FiniteMobiusResolventFlux.Rplus_even (Paid.conjugateCoordinate coordinate) _ meanEven
  have reflection := Lp.coeFn_compMeasurePreserving value negMeasurePreserving
  change (reflectL2 value:ℝ→ℂ)=ᵐ[volume] fun x=>value (-x) at reflection
  rw [even] at reflection
  have actual := actual_Rplus_response_profile coordinate
  have negative := negMeasurePreserving.quasiMeasurePreserving.ae actual
  rw [original_paired_sample_positive coordinate h nonnegative,L2.inner_def]
  have raw : (fun x : ℝ=>inner ℂ (burnolAnnulusSamplingL2 (OriginalRieszFiniteColumns.fourierColumn coordinate h) 0 x) (value x))=ᵐ[volume]
      (outerBand h).indicator (fun x=>-(Real.exp (-h/2):ℂ)*star (originalB coordinate (Real.exp (-h)*x))*generatedResponseProfile coordinate |x|) := by
    filter_upwards [original_positive_sample_raw coordinate h nonnegative bounded,actual,negative,reflection] with x column positive negative reflected
    by_cases inside : x∈outerBand h
    · have nonzero : x≠0 := by have nonzero:=inside.1;intro zero;rw [zero,abs_zero] at nonzero;linarith
      have sourceRead : value x=generatedResponseProfile coordinate |x| := by
        by_cases sign : 0<x
        · rw [abs_of_pos sign]
          exact positive sign
        · have xNegative : x<0 := lt_of_le_of_ne (le_of_not_gt sign) nonzero
          have inversePositive : 0< -x := neg_pos.mpr xNegative
          rw [abs_of_neg xNegative]
          exact reflected.trans (negative inversePositive)
      rw [column,sourceRead]
      simp only [indicator_of_mem inside]
      rw [RCLike.inner_apply]
      simp only [map_mul,map_neg,Complex.conj_ofReal]
      change generatedResponseProfile coordinate |x| *(-(Real.exp (-h/2):ℂ)*star (originalB coordinate (Real.exp (-h)*x)))=
        -(Real.exp (-h/2):ℂ)*star (originalB coordinate (Real.exp (-h)*x))*generatedResponseProfile coordinate |x|
      ring
    · rw [column,indicator_of_notMem inside,inner_zero_left]
      rw [indicator_of_notMem inside]
  rw [integral_congr_ae raw,integral_indicator (measurable_outerBand h)]
  rfl

end OriginalColumnMomentSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
