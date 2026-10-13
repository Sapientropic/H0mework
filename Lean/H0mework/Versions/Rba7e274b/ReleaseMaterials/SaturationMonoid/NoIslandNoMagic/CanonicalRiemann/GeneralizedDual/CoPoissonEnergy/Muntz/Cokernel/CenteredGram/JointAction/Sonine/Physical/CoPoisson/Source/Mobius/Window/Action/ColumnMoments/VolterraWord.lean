import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.VolterraSource
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.CompactResponse
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.EtaPrice
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalColumnMomentSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace BigOperators

-- The complete finite inventory, not just the original first annulus, is passed through Rplus.
def generatedResponseProfile (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  -(2:ℂ)*(x:ℂ)^(star coordinate.value-1)*
    (∑ n ∈ burnolCenteredMobiusCutoffFinset 4,FiniteMobiusResolventFlux.coefficient n*
      ((n:ℕ):ℂ)^(1-star coordinate.value)*sourceTailPrice coordinate (x/(n:ℕ)))

 theorem actual_complete_response_tail (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0<x) :
    burnolRadiusMellinTailEvaluator x positive (star coordinate.value)
      (by simpa only [Complex.star_def,Complex.conj_re] using coordinate.rightHalf)
        (FiniteMobiusResolventFlux.M (wholeContactResponse coordinate))=
    ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,FiniteMobiusResolventFlux.coefficient n*
      ((n:ℕ):ℂ)^(1-star coordinate.value)*sourceTailPrice coordinate (x/(n:ℕ)) := by
  rw [actual_response_full_word]
  simp only [map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro n _
  rw [response_pullback_tail coordinate n x positive,mul_assoc]

 theorem actual_Rplus_response_profile (coordinate : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x : ℝ ∂volume,∀ _positive : 0<x,
      S.Rplus (star coordinate.value/2) (FiniteMobiusResolventFlux.M (wholeContactResponse coordinate)) x=
        generatedResponseProfile coordinate x := by
  have source := OriginalPaPhysicalGreen.sourceVolterraResolvent_positive_profile (Paid.conjugateCoordinate coordinate)
    (FiniteMobiusResolventFlux.M (wholeContactResponse coordinate))
  have right : 1/4<(star coordinate.value/2).re := by rw [Complex.div_re];norm_num [Complex.star_def];linarith [coordinate.rightHalf]
  have direct : OriginalPaPhysicalGreen.sourceVolterraResolvent (Paid.conjugateCoordinate coordinate)
      (FiniteMobiusResolventFlux.M (wholeContactResponse coordinate))=
      S.Rplus (star coordinate.value/2) (FiniteMobiusResolventFlux.M (wholeContactResponse coordinate)) := by
    exact (FiniteMobiusResolventFlux.Rplus_tate _ right _).symm
  rw [direct] at source
  filter_upwards [source] with x actual positive
  rw [actual positive]
  change -(2:ℂ)*(x:ℂ)^(star coordinate.value-1)*
    burnolRadiusMellinTailEvaluator x positive (star coordinate.value)
      (by simpa only [Complex.star_def,Complex.conj_re] using coordinate.rightHalf)
        (FiniteMobiusResolventFlux.M (wholeContactResponse coordinate))=_
  rw [actual_complete_response_tail coordinate x positive]
  rfl

end OriginalColumnMomentSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
