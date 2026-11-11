import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExpandedDualForcingSourceAction.MeanDebt
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialExpandedDualSourceAction.Action
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKExpandedDualForcingSourceAction
open Complex BurnolPhysicalState OriginalKMaterialExpandedDualSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open OriginalRieszSource OriginalKExpandedInverseSourceAction
open scoped InnerProductSpace

/-- Both full forcing programmes are lifted before the independent expanded fee is read. -/
def sourceForcingCompleteFieldAction (t : ℝ) : BurnolL2 →L[ℂ] BurnolL2 :=
 burnolQuarterZeroExtension.comp (sourceFullPlusForcingProgramme t) +
 fourierL2.toLinearIsometry.toContinuousLinearMap.comp
  (burnolQuarterZeroExtension.comp (sourceFullMinusForcingProgramme t))

def sourceForcingMaterialAction (t : ℝ) : D.SourceBranches →L[ℂ] D.SourceBranches :=
 OriginalKBoundaryNativeSourceAction.sourceFields.comp
  ((sourceForcingCompleteFieldAction t).comp OriginalKFullSourceRAction.originalField)

/-- Raw profiles, signed forcing and the complete mean debt remain individual source AST nodes. -/
def sourceRawPlusMaterialAction (t : ℝ) : D.SourceBranches →L[ℂ] D.SourceBranches :=
 OriginalKBoundaryNativeSourceAction.sourceFields.comp
  (OriginalKCvelSourceAction.actualStockExtension.comp ((sourceDualPlusRaw t).comp OriginalKFullSourceRAction.originalField))

def sourceRawMinusMaterialAction (t : ℝ) : D.SourceBranches →L[ℂ] D.SourceBranches :=
 OriginalKBoundaryNativeSourceAction.sourceFields.comp
  (OriginalKCvelSourceAction.actualStockExtension.comp ((sourceDualMinusRaw t).comp OriginalKFullSourceRAction.originalField))

/-- The same raw compact foot is decoded by its actual restriction and mean-zero carrier, without even elimination. -/
def sourcePlusForcingMaterialAction : D.SourceBranches →L[ℂ] D.SourceBranches :=
 OriginalKBoundaryNativeSourceAction.sourceFields.comp
  (OriginalKCvelSourceAction.actualStockExtension.comp
   (sourceDualPlusForcing.comp (Constructor.zeroMean.comp
    (burnolQuarterRestriction.comp OriginalKFullSourceRAction.originalField))))

def sourceMinusForcingMaterialAction : D.SourceBranches →L[ℂ] D.SourceBranches :=
 OriginalKBoundaryNativeSourceAction.sourceFields.comp
  (OriginalKCvelSourceAction.actualStockExtension.comp
   (sourceDualMinusForcing.comp (Constructor.zeroMean.comp
    (burnolQuarterRestriction.comp OriginalKFullSourceRAction.originalField))))

def sourceMeanDebtMaterialAction (t : ℝ) : D.SourceBranches →L[ℂ] D.SourceBranches :=
 OriginalKBoundaryNativeSourceAction.sourceFields.comp
  (burnolQuarterZeroExtension.comp ((sourceQuarterMeanDebtAction t).comp OriginalKFullSourceRAction.originalField))

def sourceForcingMaterialCode (t : ℝ) : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .add
  (.add (.linear (s:=()) (t:=()) sourcePlusForcingMaterialAction.toLinearMap.toAddMonoidHom
    (.linear (s:=()) (t:=()) (sourceRawPlusMaterialAction t).toLinearMap.toAddMonoidHom (.var ())))
   (.linear (s:=()) (t:=()) (sourceMeanDebtMaterialAction t).toLinearMap.toAddMonoidHom (.var ())))
  (.linear (s:=()) (t:=()) sourceDualFourierAction.toLinearMap.toAddMonoidHom
   (.add (.linear (s:=()) (t:=()) sourceMinusForcingMaterialAction.toLinearMap.toAddMonoidHom
     (.linear (s:=()) (t:=()) (sourceRawMinusMaterialAction t).toLinearMap.toAddMonoidHom (.var ())))
    (.linear (s:=()) (t:=()) (sourceMeanDebtMaterialAction t).toLinearMap.toAddMonoidHom (.var ()))))

private theorem source_compact_own_raw_read (source : BurnolQuarterMeanZeroCarrier) :
 Constructor.zeroMean (burnolQuarterRestriction (OriginalKCvelSourceAction.actualStockExtension source))=source := by
 apply Subtype.ext
 change burnolQuarterMeanZeroProjection (burnolQuarterRestriction
  (burnolQuarterZeroExtension (source : BurnolQuarterIntervalL2)))=(source : BurnolQuarterIntervalL2)
 rw [burnolQuarterRestriction_zeroExtension,burnolQuarterMeanZeroProjection_coe]

theorem source_forcing_material_code_read (t : ℝ)
 (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (sourceForcingMaterialCode t).eval environment=sourceForcingMaterialAction t (environment () ()) := by
 change sourcePlusForcingMaterialAction (sourceRawPlusMaterialAction t (environment () ()))+
  sourceMeanDebtMaterialAction t (environment () ())+
  sourceDualFourierAction (sourceMinusForcingMaterialAction (sourceRawMinusMaterialAction t (environment () ()))+
   sourceMeanDebtMaterialAction t (environment () ()))=_
 simp only [sourcePlusForcingMaterialAction,sourceMinusForcingMaterialAction,
  sourceRawPlusMaterialAction,sourceRawMinusMaterialAction,sourceMeanDebtMaterialAction,
  sourceDualFourierAction,ContinuousLinearMap.comp_apply]
 change OriginalKBoundaryNativeSourceAction.sourceFields
  (OriginalKCvelSourceAction.actualStockExtension (sourceDualPlusForcing
   (Constructor.zeroMean (burnolQuarterRestriction (OriginalKCvelSourceAction.actualStockExtension
    (sourceDualPlusRaw t (OriginalKFullSourceRAction.originalField (environment () ()))))))))+
  OriginalKBoundaryNativeSourceAction.sourceFields
   (burnolQuarterZeroExtension (sourceQuarterMeanDebtAction t (OriginalKFullSourceRAction.originalField (environment () ()))))+
  OriginalKBoundaryNativeSourceAction.sourceFields (fourierL2
   (OriginalKCvelSourceAction.actualStockExtension (sourceDualMinusForcing
    (Constructor.zeroMean (burnolQuarterRestriction (OriginalKCvelSourceAction.actualStockExtension
     (sourceDualMinusRaw t (OriginalKFullSourceRAction.originalField (environment () ())))))))+
    burnolQuarterZeroExtension (sourceQuarterMeanDebtAction t (OriginalKFullSourceRAction.originalField (environment () ())))))=_
 rw [source_compact_own_raw_read,source_compact_own_raw_read,←map_add,←map_add]
 change _=OriginalKBoundaryNativeSourceAction.sourceFields _
 congr 1
 change OriginalKCvelSourceAction.actualStockExtension
  (sourceDualPlusForcing (sourceDualPlusRaw t (OriginalKFullSourceRAction.originalField (environment () ()))))+
  burnolQuarterZeroExtension (sourceQuarterMeanDebtAction t (OriginalKFullSourceRAction.originalField (environment () ())))+
  fourierL2 (OriginalKCvelSourceAction.actualStockExtension
   (sourceDualMinusForcing (sourceDualMinusRaw t (OriginalKFullSourceRAction.originalField (environment () ()))))+
   burnolQuarterZeroExtension (sourceQuarterMeanDebtAction t (OriginalKFullSourceRAction.originalField (environment () ()))))=
  burnolQuarterZeroExtension
   ((sourceDualPlusForcing (sourceDualPlusRaw t (OriginalKFullSourceRAction.originalField (environment () ()))))+
    sourceQuarterMeanDebtAction t (OriginalKFullSourceRAction.originalField (environment () ())))+
  fourierL2 (burnolQuarterZeroExtension
   ((sourceDualMinusForcing (sourceDualMinusRaw t (OriginalKFullSourceRAction.originalField (environment () ()))))+
    sourceQuarterMeanDebtAction t (OriginalKFullSourceRAction.originalField (environment () ()))))
 simp only [map_add]
 rfl

theorem source_forcing_material_code_effect (t : ℝ)
 (environment increment : Env (PairValue (PairValue C.Value)) C.Var) :
 (sourceForcingMaterialCode t).effect environment increment=sourceForcingMaterialAction t (increment () ()) := by
 have generated := Expr.eval_update (sourceForcingMaterialCode t) environment increment
 rw [source_forcing_material_code_read,source_forcing_material_code_read] at generated
 change sourceForcingMaterialAction t (environment () ()+increment () ())=_ at generated
 rw [map_add] at generated
 exact add_left_cancel generated.symm

/-- The effect field regenerates the same complete quarter forcing on both original feet. -/
theorem source_forcing_material_effect_field (t : ℝ)
 (environment increment : Env (PairValue (PairValue C.Value)) C.Var) :
 OriginalKFullSourceRAction.originalField ((sourceForcingMaterialCode t).effect environment increment)=
 burnolQuarterZeroExtension (sourceFullQuarterAction t (OriginalKFullSourceRAction.originalField (increment () ())))+
 fourierL2 (burnolQuarterZeroExtension (sourceFullQuarterAction t (OriginalKFullSourceRAction.originalField (increment () ())))) := by
 rw [source_forcing_material_code_effect]
 change sourceForcingCompleteFieldAction t (OriginalKFullSourceRAction.originalField (increment () ()))=_
 have actual := source_full_forcing_programme (OriginalKFullSourceRAction.originalField (increment () ())) t
 exact congrArg₂ (fun first second : BurnolQuarterIntervalL2 =>
  burnolQuarterZeroExtension first+fourierL2 (burnolQuarterZeroExtension second)) actual.1 actual.2

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKExpandedDualForcingSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
