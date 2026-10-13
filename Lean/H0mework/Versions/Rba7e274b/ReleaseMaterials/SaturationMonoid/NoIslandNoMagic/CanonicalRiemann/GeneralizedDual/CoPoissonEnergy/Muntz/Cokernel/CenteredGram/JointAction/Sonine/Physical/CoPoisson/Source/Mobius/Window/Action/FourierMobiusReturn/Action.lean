import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierMobiusReturn.Profile
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierMobiusReturn.ActualFeed
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierMobiusReturn.EvenSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalFourierMobiusReturnSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
open OriginalRieszSource

theorem actual_generated_positive_return (coordinate : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x : ℝ ∂volume,∀ _positive : 0<x,
      burnolDirectRightResolvent (star coordinate.value/2)
        (Paid.M (fourierL2 (C.wholeContactResponse coordinate))) x=generatedFourierReturnRaw coordinate x := by
  filter_upwards [actual_R_fourier_source_feed coordinate] with x read positive
  rw [read]
  unfold actualFourierReturnTimeRaw
  rw [original_R_radial_time coordinate _ x positive,computed_positive_return_profile coordinate x positive]

 theorem generated_return_raw_even (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    generatedFourierReturnRaw coordinate (-x)=generatedFourierReturnRaw coordinate x := by
  unfold generatedFourierReturnRaw gluedSourceRaw gluedPowerRaw fixedEdgeReturnRaw
  rw [abs_neg]
  split_ifs
  · rw [finite_source_even]
  · rfl

 theorem actual_generated_return (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolDirectRightResolvent (star coordinate.value/2)
      (Paid.M (fourierL2 (C.wholeContactResponse coordinate))):ℝ→ℂ)=ᵐ[volume] generatedFourierReturnRaw coordinate := by
  let field := burnolDirectRightResolvent (star coordinate.value/2)
    (Paid.M (fourierL2 (C.wholeContactResponse coordinate)))
  have negative := negMeasurePreserving.quasiMeasurePreserving.ae (actual_generated_positive_return coordinate)
  filter_upwards [actual_generated_positive_return coordinate,negative,
    Lp.coeFn_compMeasurePreserving field negMeasurePreserving,volume.ae_ne (0:ℝ)] with x direct moved reflection nonzero
  have parity : field (-x)=field x := by
    change reflectL2 field x=field (-x) at reflection
    rw [actual_fourier_return_even coordinate] at reflection
    exact reflection.symm
  rcases lt_or_gt_of_ne nonzero with neg | pos
  · rw [← parity,moved (by linarith),generated_return_raw_even]
  · exact direct pos

 theorem generated_return_memLp (coordinate : BurnolCompletedMellinCoordinate) : MemLp (generatedFourierReturnRaw coordinate) 2 volume :=
  (memLp_congr_ae (actual_generated_return coordinate)).mp (Lp.memLp _)

-- This generated field is fixed by the literal whole finite source profile, not a caller-selected R output.
def generatedFourierReturn (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (generated_return_memLp coordinate).toLp (generatedFourierReturnRaw coordinate)

 theorem generated_return_read (coordinate : BurnolCompletedMellinCoordinate) :
    (generatedFourierReturn coordinate:ℝ→ℂ)=ᵐ[volume] generatedFourierReturnRaw coordinate := MemLp.coeFn_toLp _

 theorem original_R_fourier_response (coordinate : BurnolCompletedMellinCoordinate) :
    burnolDirectRightResolvent (star coordinate.value/2)
      (Paid.M (fourierL2 (C.wholeContactResponse coordinate)))=generatedFourierReturn coordinate := by
  apply Lp.ext
  exact (actual_generated_return coordinate).trans (generated_return_read coordinate).symm

 theorem original_Rplus_Tate_response (coordinate : BurnolCompletedMellinCoordinate) :
    FiniteMobiusResolventFlux.Rplus (star coordinate.value/2)
      (burnolTateReciprocalL2 (Paid.M (fourierL2 (C.wholeContactResponse coordinate))))=
        burnolTateReciprocalL2 (generatedFourierReturn coordinate) := by
  have right : 1/4<(star coordinate.value/2).re := by rw [Complex.div_re];norm_num [Complex.star_def];linarith [coordinate.rightHalf]
  rw [FiniteMobiusResolventFlux.Rplus_tate _ right,burnolTateReciprocalL2_involutive,original_R_fourier_response]

end OriginalFourierMobiusReturnSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
