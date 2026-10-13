import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ContactFeedback.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalContactFeedbackSource
open Complex MeasureTheory
open scoped InnerProductSpace Topology
open OriginalRieszSource
attribute [local instance 1100] NormedSpace.complexToReal

-- The source-cancelled whole ordinary equation, not a caller return premise, fixes the actual R action.
theorem original_combined_R_return (coordinate : BurnolCompletedMellinCoordinate) :
    burnolDirectRightResolvent (star coordinate.value/2) (sourceForcing coordinate)=(2:ℂ) • sourceField coordinate := by
  have right : 1/4<(star coordinate.value/2).re := by rw [Complex.div_re];norm_num [Complex.star_def];linarith [coordinate.rightHalf]
  have scalar : HasDerivAt (fun time : ℝ=>-time/2) (-1/2:ℝ) 0 := by
    simpa only [id_eq,Pi.neg_apply] using (hasDerivAt_id (0:ℝ)).neg.div_const (2:ℝ)
  have ordinary := (combined_source_strong coordinate).const_smul ((2:ℂ))
  have actual := HasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) ordinary.hasFDerivAt scalar (by norm_num)
  have source : HasDerivAt (fun time : ℝ=>burnolMultiplicativeDilation (-time/2) ((2:ℂ) • sourceField coordinate))
      ((star coordinate.value/2-1/4) • ((2:ℂ) • sourceField coordinate)+sourceForcing coordinate) 0 := by
    convert! actual using 1
    · funext time
      rw [map_smul]
      rfl
    · change _=(-1/2:ℝ) • ((2:ℂ) • sourceVelocity coordinate)
      rw [← algebraMap_smul ℂ (-1/2:ℝ)]
      unfold sourceVelocity
      norm_num only [map_div₀,map_neg,map_one,map_ofNat]
      module
  exact (burnolDirectRightResolvent_of_strongEquation (star coordinate.value/2) right
    (sourceForcing coordinate) ((2:ℂ) • sourceField coordinate) source).symm

 def generatedCombinedReturn (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (2:ℂ) • FiniteMobiusResolventFlux.M (sourceField coordinate)-
    FiniteMobiusResolventFlux.actualFlux (star coordinate.value/2) (sourceForcing coordinate)

-- Full-L2 actual tail and mean flux are the existing source inventories; no gap or Pa qualification is supplied.
theorem original_combined_M_R_return (coordinate : BurnolCompletedMellinCoordinate) :
    burnolDirectRightResolvent (star coordinate.value/2) (FiniteMobiusResolventFlux.M (sourceForcing coordinate))=
      generatedCombinedReturn coordinate := by
  have right : 1/4<(star coordinate.value/2).re := by rw [Complex.div_re];norm_num [Complex.star_def];linarith [coordinate.rightHalf]
  have actual := FiniteMobiusResolventFlux.actual_M_R_action (star coordinate.value/2) right (sourceForcing coordinate)
  rw [original_combined_R_return,map_smul] at actual
  unfold generatedCombinedReturn
  exact eq_sub_of_add_eq actual.symm

 theorem original_combined_Tate_return (coordinate : BurnolCompletedMellinCoordinate) :
    FiniteMobiusResolventFlux.Rplus (star coordinate.value/2)
      (burnolTateReciprocalL2 (FiniteMobiusResolventFlux.M (sourceForcing coordinate)))=
        burnolTateReciprocalL2 (generatedCombinedReturn coordinate) := by
  have right : 1/4<(star coordinate.value/2).re := by rw [Complex.div_re];norm_num [Complex.star_def];linarith [coordinate.rightHalf]
  rw [FiniteMobiusResolventFlux.Rplus_tate _ right,burnolTateReciprocalL2_involutive,original_combined_M_R_return]

end OriginalContactFeedbackSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
