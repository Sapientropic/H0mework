import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaCutoffCompressionSourceAction.Support
import H0mework.Realization.ScalarCofinal.KernelCompletion
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaWindowCofinalSourceCompletion
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open MeasureTheory Set
open scoped InnerProductSpace

abbrev PaSourceCarrier := burnolCompactCoPoissonClosedRange.toSubmodule

def sourceNu : PaSourceCarrier →L[ℂ] BurnolL2 :=
 burnolMobiusSourceL2.comp burnolCompactCoPoissonClosedRange.toSubmodule.subtypeL

def windowRead (stage : Nat) : PaSourceCarrier →L[ℂ] BurnolRadiusIntervalL2 (stage+1:ℝ) :=
 (burnolSourceOnlyCoPoissonWindow (stage+1:ℝ)).comp sourceNu

def windowTransition (stage : Nat) :
 BurnolRadiusIntervalL2 ((stage+1:Nat)+1:ℝ) →L[ℂ] BurnolRadiusIntervalL2 (stage+1:ℝ) :=
 (burnolRadiusRestriction (stage+1:ℝ)).comp (burnolRadiusZeroExtension ((stage+1:Nat)+1:ℝ))

theorem source_window_read (stage : Nat) (value : PaSourceCarrier) :
 windowRead stage value = burnolRadiusRestriction (stage+1:ℝ) ((value : BurnolPaAmbientCarrier) : BurnolL2) :=
 burnolSourceOnlyCoPoissonWindow_replay _ _ value.property

theorem source_literal_window_read (stage : Nat) (value : PaSourceCarrier) :
 (OriginalKFinitePaWindowOperatorSourceAction.completeWindowWord (stage+1:ℝ)).eval
  (OriginalKFinitePaWindowOperatorSourceAction.windowEnvironment
   (OriginalKBoundaryNativeSourceAction.sourceFields (sourceNu value))) =
 OriginalKBoundaryNativeSourceAction.sourceFields
  (burnolRadiusZeroExtension (stage+1:ℝ) (windowRead stage value)) := by
 rw [OriginalKFinitePaWindowOperatorSourceAction.finite_word_source_value]
 simp only [OriginalKFinitePaWindowOperatorSourceAction.windowEnvironment,
  OriginalKBoundaryNativeSourceAction.source_fields_first]
 rfl

/-- Nested source support generates this restriction equation before any Data compatibility field. -/
theorem actual_nested_source_restriction (small large : ℝ) (included : small≤large) (value : BurnolL2) :
 burnolRadiusRestriction small (burnolRadiusZeroExtension large (burnolRadiusRestriction large value)) =
 burnolRadiusRestriction small value := by
 have largeRead := (ae_restrict_iff' (measurableSet_symmetricInterval large)).mp
  (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval large) value)
 apply Lp.ext
 filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval small)
  (burnolRadiusZeroExtension large (burnolRadiusRestriction large value)),
  LpToLpRestrictCLM_coeFn ℂ (symmetricInterval small) value,
  ae_restrict_of_ae (s:=symmetricInterval small)
   (burnolRadiusZeroExtension_coe (burnolRadiusRestriction large value)),
  ae_restrict_of_ae (s:=symmetricInterval small) largeRead,
  ae_restrict_mem (measurableSet_symmetricInterval small)] with x left right extension source inside
 change x∈symmetricInterval small at inside
 have atLarge : x∈symmetricInterval large := by
  change -small≤x ∧ x≤small at inside
  change -large≤x ∧ x≤large
  constructor <;> linarith [inside.1,inside.2]
 change (burnolRadiusRestriction small (burnolRadiusZeroExtension large (burnolRadiusRestriction large value))) x = _
 change (burnolRadiusRestriction small (burnolRadiusZeroExtension large (burnolRadiusRestriction large value))) x =
  (burnolRadiusZeroExtension large (burnolRadiusRestriction large value)) x at left
 change (burnolRadiusRestriction small value) x = value x at right
 change x∈symmetricInterval large → (burnolRadiusRestriction large value) x = value x at source
 rw [left,extension,Set.indicator_of_mem atLarge,right]
 exact source atLarge

theorem source_window_transition (stage : Nat) (value : PaSourceCarrier) :
 windowTransition stage (windowRead (stage+1) value) = windowRead stage value := by
 rw [source_window_read,source_window_read]
 change burnolRadiusRestriction (stage+1:ℝ)
  (burnolRadiusZeroExtension ((stage+1:Nat)+1:ℝ)
   (burnolRadiusRestriction ((stage+1:Nat)+1:ℝ) ((value : BurnolPaAmbientCarrier) : BurnolL2))) = _
 exact actual_nested_source_restriction _ _ (by norm_num [Nat.cast_add]) _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaWindowCofinalSourceCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
