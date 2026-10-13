import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierMobiusReturn.Word
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalFourierMobiusReturnSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace BigOperators
open OriginalRieszSource

theorem original_fourier_source_even (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    fullFourierSource coordinate (-x)=fullFourierSource coordinate x :=
  OriginalRieszFinitePairing.source_fourier_even coordinate x

 theorem finite_source_even (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    sourceH coordinate (-x)=sourceH coordinate x := by
  unfold sourceH
  apply Finset.sum_congr rfl
  intro n _
  rw [neg_div,original_fourier_source_even]

 theorem actual_fourier_response_even (coordinate : BurnolCompletedMellinCoordinate) :
    reflectL2 (fourierL2 (C.wholeContactResponse coordinate))=fourierL2 (C.wholeContactResponse coordinate) := by
  rw [← fourierL2_reflectL2_commute,OriginalColumnMomentSource.whole_response_even]

-- The literal complete M word preserves reflection of this source; it grants no gap or Pa admission.
theorem actual_fourier_mobius_even (coordinate : BurnolCompletedMellinCoordinate) :
    reflectL2 (Paid.M (fourierL2 (C.wholeContactResponse coordinate)))=Paid.M (fourierL2 (C.wholeContactResponse coordinate)) := by
  rw [FiniteMobiusResolventFlux.lower_source_cutoff]
  simp only [map_sum,map_smul,map_sub]
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  rw [FiniteMobiusResolventFlux.cutoff_even _ (by
    unfold FiniteMobiusResolventFlux.fullPullback
    simp only [smul_apply,map_smul,LinearIsometry.coe_toContinuousLinearMap,LinearIsometryEquiv.coe_toLinearIsometry,
      reflectL2_burnolMultiplicativeDilation,actual_fourier_response_even])]
  have unit : reflectL2 (FiniteMobiusResolventFlux.box 4)=FiniteMobiusResolventFlux.box 4 := by
    unfold FiniteMobiusResolventFlux.box
    rw [burnolRadiusZeroExtension_reflect,reflectRestricted_intervalConstant]
  rw [unit]

 theorem actual_fourier_return_even (coordinate : BurnolCompletedMellinCoordinate) :
    reflectL2 (burnolDirectRightResolvent (star coordinate.value/2)
      (Paid.M (fourierL2 (C.wholeContactResponse coordinate))))=
      burnolDirectRightResolvent (star coordinate.value/2) (Paid.M (fourierL2 (C.wholeContactResponse coordinate))) := by
  unfold burnolDirectRightResolvent
  rw [map_neg,← reflectL2.integral_comp_comm]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro tau _
  unfold burnolDirectRightResolventIntegrand
  dsimp only
  rw [map_smul,reflectL2_burnolMultiplicativeDilation,actual_fourier_mobius_even]

end OriginalFourierMobiusReturnSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
