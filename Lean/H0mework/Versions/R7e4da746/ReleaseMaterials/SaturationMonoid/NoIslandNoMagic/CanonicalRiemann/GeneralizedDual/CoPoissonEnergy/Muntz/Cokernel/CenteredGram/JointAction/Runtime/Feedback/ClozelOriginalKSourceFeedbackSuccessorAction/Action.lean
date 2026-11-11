import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.Slots
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
open Complex BurnolPhysicalState OriginalKRawDualFeedbackSourceAction OriginalKMaterialExpandedDualSourceAction
open OriginalKFullSourceRAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
local instance actionComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
 IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
local notation "Z" => OriginalKCvelSourceAction.actualStockExtension

def finitePlusRead : Prior.Branches →L[ℂ] BurnolQuarterMeanZeroCarrier :=
 sourceCompactRead.comp ((ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.fst ℂ _ _))
def finiteMinusRead : Prior.Branches →L[ℂ] BurnolQuarterMeanZeroCarrier :=
 sourceCompactRead.comp ((ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.fst ℂ _ _))
def tailPlusRead : Prior.Branches →L[ℂ] BurnolQuarterMeanZeroCarrier :=
 sourceCompactRead.comp ((ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _))
def tailMinusRead : Prior.Branches →L[ℂ] BurnolQuarterMeanZeroCarrier :=
 sourceCompactRead.comp ((ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _))

def plusTailFeedback : Prior.Branches →L[ℂ] BurnolQuarterMeanZeroCarrier := plusFeedback.comp tailPlusRead
def minusTailFeedback : Prior.Branches →L[ℂ] BurnolQuarterMeanZeroCarrier := minusFeedback.comp tailMinusRead

def plusTailPower : Prior.Branches →L[ℂ] BurnolQuarterMeanZeroCarrier := tailPlusRead-plusTailFeedback
def minusTailPower : Prior.Branches →L[ℂ] BurnolQuarterMeanZeroCarrier := tailMinusRead-minusTailFeedback

def sourceNextSlots : Prior.Branches →L[ℂ] Prior.Branches :=
 ((Z).comp (finitePlusRead+plusTailPower)).prod ((Z).comp (finiteMinusRead+minusTailPower)) |>.prod
 (((Z).comp plusTailFeedback).prod ((Z).comp minusTailFeedback))

theorem source_next_slots_actual (value : Prior.Branches) : sourceNextSlots value=sourceSlotNext value := rfl

def sourceQuarterSlots : BurnolQuarterMeanZeroCarrier →L[ℂ] Prior.Branches :=
 ((Z).prod 0).prod (0 : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolL2 × BurnolL2)

def sourceSlotRead (reader : Prior.Branches →L[ℂ] BurnolQuarterMeanZeroCarrier) : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .linear (s:=()) (t:=()) (sourceQuarterSlots.comp reader).toLinearMap.toAddMonoidHom (.var ())

def sourcePlusFeedbackCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .linear (s:=()) (t:=()) (sourceQuarterSlots.comp (plusFeedback.comp (sourceCompactRead.comp originalField))).toLinearMap.toAddMonoidHom
  (sourceSlotRead tailPlusRead)

def sourceMinusFeedbackCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .linear (s:=()) (t:=()) (sourceQuarterSlots.comp (minusFeedback.comp (sourceCompactRead.comp originalField))).toLinearMap.toAddMonoidHom
  (sourceSlotRead tailMinusRead)

def sourceNegativeSlots : Prior.Branches →L[ℂ] Prior.Branches := -(ContinuousLinearMap.id ℂ Prior.Branches)

def sourcePlusPowerCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .add (sourceSlotRead tailPlusRead) (.linear (s:=()) (t:=()) sourceNegativeSlots.toLinearMap.toAddMonoidHom sourcePlusFeedbackCode)
def sourceMinusPowerCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .add (sourceSlotRead tailMinusRead) (.linear (s:=()) (t:=()) sourceNegativeSlots.toLinearMap.toAddMonoidHom sourceMinusFeedbackCode)

def sourceFinitePlusCode := Expr.add (sourceSlotRead finitePlusRead) sourcePlusPowerCode
def sourceFiniteMinusCode := Expr.add (sourceSlotRead finiteMinusRead) sourceMinusPowerCode

def sourceInjectFiniteMinus : Prior.Branches →L[ℂ] Prior.Branches :=
 (0 : Prior.Branches →L[ℂ] BurnolL2).prod originalField |>.prod (0 : Prior.Branches →L[ℂ] BurnolL2 × BurnolL2)
def sourceInjectTailPlus : Prior.Branches →L[ℂ] Prior.Branches :=
 (0 : Prior.Branches →L[ℂ] BurnolL2 × BurnolL2).prod (originalField.prod (0 : Prior.Branches →L[ℂ] BurnolL2))
def sourceInjectTailMinus : Prior.Branches →L[ℂ] Prior.Branches :=
 (0 : Prior.Branches →L[ℂ] BurnolL2 × BurnolL2).prod ((0 : Prior.Branches →L[ℂ] BurnolL2).prod originalField)

def sourceNextSlotsCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .add (.add sourceFinitePlusCode
   (.linear (s:=()) (t:=()) sourceInjectFiniteMinus.toLinearMap.toAddMonoidHom sourceFiniteMinusCode))
  (.add (.linear (s:=()) (t:=()) sourceInjectTailPlus.toLinearMap.toAddMonoidHom sourcePlusFeedbackCode)
   (.linear (s:=()) (t:=()) sourceInjectTailMinus.toLinearMap.toAddMonoidHom sourceMinusFeedbackCode))

private theorem actual_compact_slot (source : BurnolQuarterMeanZeroCarrier) :
 sourceCompactRead (Z source)=source := by
 apply Subtype.ext
 change burnolQuarterMeanZeroProjection (burnolQuarterRestriction (burnolQuarterZeroExtension (source : BurnolQuarterIntervalL2)))=(source : BurnolQuarterIntervalL2)
 rw [burnolQuarterRestriction_zeroExtension,burnolQuarterMeanZeroProjection_coe]

/-- The source successor executes each raw reader, feedback, forcing power, finite addition and zero extension in its literal AST. -/
theorem source_next_code_read (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 sourceNextSlotsCode.eval environment=sourceSlotNext (environment () ()) := by
 change sourceQuarterSlots (finitePlusRead (environment () ()))+
   (sourceQuarterSlots (tailPlusRead (environment () ()))+
    sourceNegativeSlots (sourceQuarterSlots (plusFeedback (sourceCompactRead (originalField (sourceQuarterSlots (tailPlusRead (environment () ()))))))))+
  sourceInjectFiniteMinus
   (sourceQuarterSlots (finiteMinusRead (environment () ()))+
    (sourceQuarterSlots (tailMinusRead (environment () ()))+
     sourceNegativeSlots (sourceQuarterSlots (minusFeedback (sourceCompactRead (originalField (sourceQuarterSlots (tailMinusRead (environment () ())))))))))+
  (sourceInjectTailPlus (sourceQuarterSlots (plusFeedback (sourceCompactRead (originalField (sourceQuarterSlots (tailPlusRead (environment () ())))))))+
   sourceInjectTailMinus (sourceQuarterSlots (minusFeedback (sourceCompactRead (originalField (sourceQuarterSlots (tailMinusRead (environment () ()))))))))=_
 simp only [sourceQuarterSlots,ContinuousLinearMap.prod_apply,zero_apply,originalField,
  ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',sourceNegativeSlots,neg_apply,ContinuousLinearMap.id_apply]
 rw [actual_compact_slot,actual_compact_slot]
 apply Prod.ext
 · apply Prod.ext
   · change _ = Z (sourceCompactRead (environment () ()).1.1+
      (sourceCompactRead (environment () ()).2.1-plusFeedback (sourceCompactRead (environment () ()).2.1)))
     simp only [sourceInjectFiniteMinus,sourceInjectTailPlus,sourceInjectTailMinus,ContinuousLinearMap.prod_apply,
      zero_apply,originalField,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',
      Prod.fst_add,Prod.fst_neg,add_zero,map_add,map_sub]
     simp only [finitePlusRead,tailPlusRead,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',sub_eq_add_neg]
   · change _ = Z (sourceCompactRead (environment () ()).1.2+
      (sourceCompactRead (environment () ()).2.2-minusFeedback (sourceCompactRead (environment () ()).2.2)))
     simp only [sourceInjectFiniteMinus,sourceInjectTailPlus,sourceInjectTailMinus,ContinuousLinearMap.prod_apply,
      zero_apply,originalField,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',
      Prod.fst_add,Prod.fst_neg,Prod.snd_add,Prod.snd_neg,zero_add,add_zero,map_add,map_sub]
     simp only [finiteMinusRead,tailMinusRead,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',sub_eq_add_neg,neg_zero,zero_add]
 · apply Prod.ext
   · change _ = Z (plusFeedback (sourceCompactRead (environment () ()).2.1))
     simp only [sourceInjectFiniteMinus,sourceInjectTailPlus,sourceInjectTailMinus,ContinuousLinearMap.prod_apply,
      zero_apply,originalField,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',
      Prod.fst_add,Prod.fst_neg,Prod.snd_add,Prod.snd_neg,zero_add,add_zero]
     simp only [tailPlusRead,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',Prod.fst_zero,neg_zero,zero_add]
   · change _ = Z (minusFeedback (sourceCompactRead (environment () ()).2.2))
     simp only [sourceInjectFiniteMinus,sourceInjectTailPlus,sourceInjectTailMinus,ContinuousLinearMap.prod_apply,
      zero_apply,originalField,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',
      Prod.fst_add,Prod.fst_neg,Prod.snd_add,Prod.snd_neg,zero_add,add_zero]
     simp only [tailMinusRead,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_snd',Prod.snd_zero,neg_zero,zero_add]

/-- Source substitution uses this same literal four-role operation; there is no external finite-depth selector. -/
def sourceSlotBinding (target : Unit) (_name : C.Var target) : Expr (PairValue (PairValue C.Value)) C.Var target := by
 cases target
 exact sourceNextSlotsCode

theorem source_binding_actual (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 SourceOperationScalarPresentation.SourceSubstitution.sourceEnvironment sourceSlotBinding environment () ()=
 sourceSlotNext (environment () ()) := source_next_code_read environment

theorem source_binding_generated_delta (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 SourceOperationScalarPresentation.SourceSubstitution.sourceEnvironment sourceSlotBinding environment () ()-environment () ()=
 sourceNextSlots (environment () ())-environment () () := by
 rw [source_binding_actual,source_next_slots_actual]

/-- This equation is generated by actual source substitution, with all four raw roles distinct. -/
theorem source_binding_actual_next (source : BurnolQuarterMeanZeroCarrier) (N : Nat) :
 SourceOperationScalarPresentation.SourceSubstitution.sourceEnvironment sourceSlotBinding
  (fun _ _ => sourceRawSlots (sourceRawFeet source N)) () ()=
 sourceRawSlots (sourceRawFeet source (N+1)) :=
 (source_binding_actual _).trans (source_slots_actual_next source N)
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
