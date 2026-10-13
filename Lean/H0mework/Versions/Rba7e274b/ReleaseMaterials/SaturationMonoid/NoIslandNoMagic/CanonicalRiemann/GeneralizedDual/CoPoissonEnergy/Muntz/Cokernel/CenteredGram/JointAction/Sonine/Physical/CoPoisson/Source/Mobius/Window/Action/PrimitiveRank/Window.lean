import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveRank.Power
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPrimitiveRankBalance
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace

def conjugateCoordinate (coordinate : BurnolCompletedMellinCoordinate) : BurnolCompletedMellinCoordinate :=
  ⟨star coordinate.value,by simpa only [Complex.star_def,Complex.conj_re] using coordinate.rightHalf,
    by simpa only [Complex.star_def,Complex.conj_re] using coordinate.belowOne⟩

-- The actual inside tail is computed on the finite window, with resonance retained in the source integral.
theorem interior_tail_read (coordinate parameter : BurnolCompletedMellinCoordinate) (x : ℝ)
    (positive : 0<x) (bounded : x≤4) :
    burnolRadiusMellinTailEvaluator x positive parameter.value parameter.rightHalf (Paid.interiorBase coordinate)=
      -(∫ t : ℝ in x..(4:ℝ),(t:ℂ)^(coordinate.value-parameter.value-1)) := by
  rw [burnolRadiusMellinTailEvaluator_eq_integral,intervalIntegral.integral_of_le bounded]
  rw [← integral_neg,← integral_indicator measurableSet_Ioi,← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [Paid.interior_base_read coordinate,volume.ae_ne (4:ℝ)] with t base notFour
  by_cases lower : x<t
  · have tPositive : 0<t := positive.trans lower
    rw [indicator_of_mem (show t∈Ioi x from lower),base,abs_of_pos tPositive]
    by_cases upper : t<4
    · rw [if_pos upper,indicator_of_mem (show t∈Ioc x 4 from ⟨lower,upper.le⟩),mul_neg]
      congr 1
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr tPositive.ne')]
      congr 1
      ring
    · have outside : t∉Ioc x 4 := by
        intro inside
        exact notFour (le_antisymm inside.2 (le_of_not_gt upper))
      rw [if_neg upper,mul_zero,indicator_of_notMem outside]
  · rw [indicator_of_notMem (show t∉Ioi x from lower),indicator_of_notMem (show t∉Ioc x 4 from fun h=>lower h.1)]

 theorem box_tail_read (parameter : BurnolCompletedMellinCoordinate) (x : ℝ)
    (positive : 0<x) (bounded : x≤4) :
    burnolRadiusMellinTailEvaluator x positive parameter.value parameter.rightHalf (Paid.box 4)=
      ∫ t : ℝ in x..(4:ℝ),(t:ℂ)^(-parameter.value) := by
  rw [burnolRadiusMellinTailEvaluator_eq_integral,intervalIntegral.integral_of_le bounded]
  rw [← integral_indicator measurableSet_Ioi,← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [FiniteMobiusResolventFlux.box_read 4] with t boxRead
  by_cases lower : x<t
  · have tPositive : 0<t := positive.trans lower
    rw [indicator_of_mem (show t∈Ioi x from lower),boxRead]
    by_cases upper : t≤4
    · rw [indicator_of_mem (show t∈symmetricInterval 4 from ⟨by linarith,upper⟩),mul_one,
        indicator_of_mem (show t∈Ioc x 4 from ⟨lower,upper⟩)]
    · rw [indicator_of_notMem (show t∉symmetricInterval 4 from fun h=>upper h.2),mul_zero,
        indicator_of_notMem (show t∉Ioc x 4 from fun h=>upper h.2)]
  · rw [indicator_of_notMem (show t∉Ioi x from lower),indicator_of_notMem (show t∉Ioc x 4 from fun h=>lower h.1)]

 theorem interior_Rplus_positive (coordinate parameter : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x : ℝ ∂volume, ∀ _positive : 0<x, ∀ _bounded : x≤4,
      Paid.Rplus (parameter.value/2) (Paid.interiorBase coordinate) x=
      (2:ℂ)*(x:ℂ)^(parameter.value-1)*(∫ t : ℝ in x..(4:ℝ),(t:ℂ)^(coordinate.value-parameter.value-1)) := by
  have source := OriginalPaPhysicalGreen.sourceVolterraResolvent_positive_profile parameter (Paid.interiorBase coordinate)
  have right : 1/4<(parameter.value/2).re := by rw [Complex.div_re];norm_num;linarith [parameter.rightHalf]
  have same : OriginalPaPhysicalGreen.sourceVolterraResolvent parameter (Paid.interiorBase coordinate)=
      Paid.Rplus (parameter.value/2) (Paid.interiorBase coordinate) := (FiniteMobiusResolventFlux.Rplus_tate _ right _).symm
  rw [same] at source
  filter_upwards [source] with x actual positive bounded
  rw [actual positive,interior_tail_read coordinate parameter x positive bounded]
  ring

 theorem box_Rplus_positive (parameter : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x : ℝ ∂volume, ∀ _positive : 0<x, ∀ _bounded : x≤4,
      Paid.Rplus (parameter.value/2) (Paid.box 4) x=
      -(2:ℂ)*(x:ℂ)^(parameter.value-1)*((4:ℂ)^(1-parameter.value)-(x:ℂ)^(1-parameter.value))/(1-parameter.value) := by
  have source := OriginalPaPhysicalGreen.sourceVolterraResolvent_positive_profile parameter (Paid.box 4)
  have right : 1/4<(parameter.value/2).re := by rw [Complex.div_re];norm_num;linarith [parameter.rightHalf]
  have same : OriginalPaPhysicalGreen.sourceVolterraResolvent parameter (Paid.box 4)=
      Paid.Rplus (parameter.value/2) (Paid.box 4) := (FiniteMobiusResolventFlux.Rplus_tate _ right _).symm
  rw [same] at source
  filter_upwards [source] with x actual positive bounded
  rw [actual positive,box_tail_read parameter x positive bounded,
    integral_cpow (Or.inl (by simp only [Complex.neg_re];linarith [parameter.belowOne]))]
  rw [show -parameter.value+1=1-parameter.value by ring]
  norm_num only [Complex.ofReal_ofNat]
  ring

end OriginalPrimitiveRankBalance
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
