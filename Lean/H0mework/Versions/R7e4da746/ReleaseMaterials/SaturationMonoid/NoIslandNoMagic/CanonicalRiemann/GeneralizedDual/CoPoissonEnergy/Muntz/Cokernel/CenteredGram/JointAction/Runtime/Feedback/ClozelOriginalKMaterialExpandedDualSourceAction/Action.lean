import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialExpandedDualSourceAction.Reader
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPhysicalStockSourceAction.WholeConsumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialExpandedDualSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex BurnolPhysicalState
open scoped InnerProductSpace
namespace D
export OriginalKMaterialPhysicalStockSourceAction.D (SourceBranches)
end D
namespace C
export OriginalKMaterialPhysicalStockSourceAction.C (Value Var)
end C
namespace SF
export OriginalKMaterialPhysicalStockSourceAction.SF (Factory Packet)
end SF
namespace A
export OriginalKMaterialPhysicalStockSourceAction.A (Programme)
end A
namespace L
export OriginalKMaterialPhysicalStockSourceAction.L (Value groups)
end L
local instance actionGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target

def sourceExpandedDualAction (t : ℝ) : D.SourceBranches →L[ℂ] D.SourceBranches :=
 OriginalKBoundaryNativeSourceAction.sourceFields.comp
  ((sourceDualCompleteField t).comp OriginalKFullSourceRAction.originalField)

def sourceDualRawPlusAction (t : ℝ) : D.SourceBranches →L[ℂ] D.SourceBranches :=
 OriginalKBoundaryNativeSourceAction.sourceFields.comp
  (OriginalKCvelSourceAction.actualStockExtension.comp ((sourceDualPlusRaw t).comp OriginalKFullSourceRAction.originalField))

def sourceDualRawMinusAction (t : ℝ) : D.SourceBranches →L[ℂ] D.SourceBranches :=
 OriginalKBoundaryNativeSourceAction.sourceFields.comp
  (OriginalKCvelSourceAction.actualStockExtension.comp ((sourceDualMinusRaw t).comp OriginalKFullSourceRAction.originalField))

def sourceDualOddPlusAction (t : ℝ) : D.SourceBranches →L[ℂ] D.SourceBranches :=
 sourceDualRawPlusAction t - OriginalKBoundaryNativeSourceAction.sourceFields.comp
  (OriginalKCvelSourceAction.actualStockExtension.comp ((sourceDualPlus t).comp OriginalKFullSourceRAction.originalField))

def sourceDualOddMinusAction (t : ℝ) : D.SourceBranches →L[ℂ] D.SourceBranches :=
 sourceDualRawMinusAction t - OriginalKBoundaryNativeSourceAction.sourceFields.comp
  (OriginalKCvelSourceAction.actualStockExtension.comp ((sourceDualMinus t).comp OriginalKFullSourceRAction.originalField))

def sourceDualFourierAction : D.SourceBranches →L[ℂ] D.SourceBranches :=
 OriginalKBoundaryNativeSourceAction.sourceFields.comp
  (fourierL2.toLinearIsometry.toContinuousLinearMap.comp OriginalKFullSourceRAction.originalField)

def sourceDualNegativeAction : D.SourceBranches →L[ℂ] D.SourceBranches :=
 -ContinuousLinearMap.id ℂ D.SourceBranches

/-- Raw/odd source faces remain explicit AST nodes of the same action; their dependent even faces are then assembled into the full vector. -/
def sourceExpandedDualCode (t : ℝ) : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .add
  (.add (.linear (s:=()) (t:=()) (sourceDualRawPlusAction t).toLinearMap.toAddMonoidHom (.var ()))
   (.linear (s:=()) (t:=()) sourceDualNegativeAction.toLinearMap.toAddMonoidHom (.linear (s:=()) (t:=()) (sourceDualOddPlusAction t).toLinearMap.toAddMonoidHom (.var ()))))
  (.linear (s:=()) (t:=()) sourceDualFourierAction.toLinearMap.toAddMonoidHom
   (.add (.linear (s:=()) (t:=()) (sourceDualRawMinusAction t).toLinearMap.toAddMonoidHom (.var ()))
    (.linear (s:=()) (t:=()) sourceDualNegativeAction.toLinearMap.toAddMonoidHom (.linear (s:=()) (t:=()) (sourceDualOddMinusAction t).toLinearMap.toAddMonoidHom (.var ())))))

theorem source_expanded_dual_code_read (t : ℝ) (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (sourceExpandedDualCode t).eval environment=sourceExpandedDualAction t (environment () ()) := by
 change sourceDualRawPlusAction t (environment () ()) + sourceDualNegativeAction (sourceDualOddPlusAction t (environment () ())) +
  sourceDualFourierAction (sourceDualRawMinusAction t (environment () ()) + sourceDualNegativeAction (sourceDualOddMinusAction t (environment () ())))=_
 simp only [sourceDualNegativeAction,neg_apply,ContinuousLinearMap.id_apply,←sub_eq_add_neg]
 unfold sourceDualOddPlusAction sourceDualOddMinusAction
 simp only [sub_apply,sub_sub_cancel]
 change OriginalKBoundaryNativeSourceAction.sourceFields _ +
  OriginalKBoundaryNativeSourceAction.sourceFields (fourierL2 _)=_
 rw [←map_add]
 rfl

/-- The actual full material increment drives the two-profile field operation before any fee is read. -/
theorem source_expanded_dual_code_effect (t : ℝ)
 (environment increment : Env (PairValue (PairValue C.Value)) C.Var) :
 (sourceExpandedDualCode t).effect environment increment=sourceExpandedDualAction t (increment () ()) := by
 have source := Expr.eval_update (sourceExpandedDualCode t) environment increment
 rw [source_expanded_dual_code_read,source_expanded_dual_code_read] at source
 change sourceExpandedDualAction t (environment () ()+increment () ())=_ at source
 rw [map_add] at source
 exact add_left_cancel source.symm

/-- All four source action roles are generated from the same complete field; the two profiles are recovered through the original inverse. -/
theorem source_expanded_dual_action_recovers_profiles (t : ℝ) (value : D.SourceBranches) :
 burnolAmbientMeanZeroFirstCorrection (OriginalKFullSourceRAction.originalField (sourceExpandedDualAction t value)) =
  sourceDualPlus t (OriginalKFullSourceRAction.originalField value) ∧
 burnolAmbientMeanZeroSecondCorrection (OriginalKFullSourceRAction.originalField (sourceExpandedDualAction t value)) =
  sourceDualMinus t (OriginalKFullSourceRAction.originalField value) := by
 exact source_own_profiles_recovered _ t

/-- The dependent field reader consumes the actual source effect, preserving its entire input role. -/
theorem source_expanded_dual_effect_pays_independent_fees (t : ℝ)
 (environment increment : Env (PairValue (PairValue C.Value)) C.Var) :
 inner ℂ (burnolAmbientMeanZeroFirstCorrection (OriginalKFullSourceRAction.originalField
  ((sourceExpandedDualCode t).effect environment increment))) OriginalRieszSource.Response.eta =
 inner ℂ (burnolEvenAmbientProjection (OriginalKFullSourceRAction.originalField (increment () ())) : BurnolL2)
  (burnolMultiplicativeDilation (-t) (OriginalRieszSource.Response.wholeU+OriginalRieszSource.Response.wholeV)) ∧
 inner ℂ (burnolAmbientMeanZeroSecondCorrection (OriginalKFullSourceRAction.originalField
  ((sourceExpandedDualCode t).effect environment increment))) OriginalRieszSource.Response.eta =
 inner ℂ (burnolEvenAmbientProjection (OriginalKFullSourceRAction.originalField (increment () ())) : BurnolL2)
  (burnolMultiplicativeDilation (-t) (OriginalRieszSource.Response.wholeU-OriginalRieszSource.Response.wholeV)) := by
 rw [source_expanded_dual_code_effect]
 exact source_received_profiles_pay_expanded_fees _ t
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialExpandedDualSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
