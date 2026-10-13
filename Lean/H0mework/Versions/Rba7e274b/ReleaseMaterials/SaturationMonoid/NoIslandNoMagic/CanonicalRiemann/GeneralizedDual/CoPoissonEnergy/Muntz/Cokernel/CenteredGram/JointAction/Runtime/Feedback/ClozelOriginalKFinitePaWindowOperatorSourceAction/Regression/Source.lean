import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFinitePaWindowOperatorSourceAction.Received
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFinitePaWindowOperatorSourceAction.Emitter
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction.Gate
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState

/-- The source cutoff, rather than a completed window constant, computes a zero-source override. -/
theorem zero_actual_nu_override (radius : ℝ) :
 (completeWindowWord radius).eval (windowEnvironment 0) = 0 := by
 rw [finite_word_source_value]
 simp [windowEnvironment]

theorem old_written_override_keeps_source (radius : ℝ) (source old changed : Branches) :
 (sourceStockWord radius source).eval (windowEnvironment changed) - changed =
 (sourceStockWord radius source).eval (windowEnvironment old) - old := by
 rw [source_stock_word_value,source_stock_word_value]
 change changed + _ - changed = old + _ - old
 rw [add_sub_cancel_left,add_sub_cancel_left]

theorem erase_actual_pole_cost (radius : ℝ) (source : Branches)
 (erased : (completeWindowWord radius).eval (windowEnvironment source) =
  (cutoffWord radius (burnolCenteredMobiusCutoffFinset radius).toList).eval (windowEnvironment source)) :
 sourcePole radius source=0 := by
 change _ + sourcePole radius source = _ at erased
 exact add_left_cancel (erased.trans (add_zero _).symm)

theorem nonmatching_cutoff_has_own_action_cost (radius : ℝ) (m : ℕ+) (rest : List ℕ+)
 (source : Branches)
 (erased : (cutoffWord radius (m::rest)).eval (windowEnvironment source) =
  (cutoffWord radius rest).eval (windowEnvironment source)) :
 cutoffWeight m (cutoffPullback radius m source)=0 := by
 have action := literal_cutoff_append radius m rest (windowEnvironment source)
 rw [erased,sub_self] at action
 exact action.symm

/-- The actual first inverse fibre cannot be deleted merely because its forward window was read. -/
theorem erase_first_inverse_residual_cost (radius : ℝ) (source : Branches)
 (erased : firstInverseResidual radius source=0) :
 OriginalKFullSourceRAction.originalField source =
 burnolMobiusSourceL2 (burnolEvenAmbientProjection (OriginalKFullSourceRAction.originalField
  ((completeWindowWord radius).eval (windowEnvironment source)))) := by
 have actual := first_inverse_residual_equation radius source
 rw [erased,add_zero] at actual
 exact actual

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction.Gate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
