import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDecodedPaRSourceEnergy.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaUnitOutsideSourceDebtAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace Four
export OriginalKDecodedPaRFourFaceSourceAction (actualParentFactory actualParentPacket receivedOwnStock actual_material_stock_effect ownFourFaceSource own_four_face_read)
end Four
namespace Energy
export OriginalKDecodedPaRSourceEnergy (sourceR source_R_read source_R_vector_action source_Pa_unit_complete_energy sourceRankCoefficient originalUnitRank)
end Energy
namespace C
export OriginalKFullSourceRAction.C (Value Var)
end C
namespace Native
export OriginalKBoundaryNativeSourceAction (sourceFields source_fields_first)
end Native
abbrev Branches := OriginalKFinitePaWindowOperatorSourceAction.Branches
local instance splitPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def sourceRRead : Branches →L[ℂ] BurnolL2 :=
 (ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.fst ℂ _ _) +
 (ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.fst ℂ _ _)
def paProjection : BurnolL2 →L[ℂ] BurnolL2 :=
 BurnolPaAmbientCarrier.subtypeL.comp OriginalKCombCofinalPaAction.E
def unitProjection : BurnolL2 →L[ℂ] BurnolL2 :=
 BurnolPaAmbientCarrier.subtypeL.comp OriginalKCombCofinalPaAction.Q
def outsideProjection : BurnolL2 →L[ℂ] BurnolL2 :=
 BurnolPaAmbientCarrierᗮ.starProjection

def splitProjection : BurnolL2 →L[ℂ] Branches :=
 (paProjection.prod unitProjection).prod (outsideProjection.prod (ContinuousLinearMap.id ℂ BurnolL2))

def recombineRFields : Branches →L[ℂ] Branches := Native.sourceFields.comp sourceRRead
def dilationRFields (shift : ℝ) : Branches →L[ℂ] Branches :=
 Native.sourceFields.comp ((burnolMultiplicativeDilation (-shift/2)).toLinearIsometry.toContinuousLinearMap.comp OriginalKFullSourceRAction.originalField)
def splitSourceFields : Branches →L[ℂ] Branches :=
 splitProjection.comp OriginalKFullSourceRAction.originalField

/-- The three source operations preserve their literal intermediate stock and are run before any energy read. -/
def splitCode (shift : ℝ) : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .linear (s:=()) (t:=()) splitSourceFields.toLinearMap.toAddMonoidHom
  (.linear (s:=()) (t:=()) (dilationRFields shift).toLinearMap.toAddMonoidHom
   (.linear (s:=()) (t:=()) recombineRFields.toLinearMap.toAddMonoidHom (.var ())))

def splitAction (shift : ℝ) : Branches →L[ℂ] Branches :=
 splitProjection.comp ((burnolMultiplicativeDilation (-shift/2)).toLinearIsometry.toContinuousLinearMap.comp sourceRRead)

theorem split_code_read (shift : ℝ) (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (splitCode shift).eval environment=splitAction shift (environment () ()) := rfl

theorem split_code_effect (shift : ℝ) (environment increment : Env (PairValue (PairValue C.Value)) C.Var) :
 (splitCode shift).effect environment increment=splitAction shift (increment () ()) := by
 have generated := Expr.eval_update (splitCode shift) environment increment
 rw [split_code_read,split_code_read] at generated
 change splitAction shift (environment () ()+increment () ())=_ at generated
 rw [map_add] at generated
 exact add_left_cancel generated.symm

def sourceSplitWord (source : Branches) (shift : ℝ) : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .linear (s:=()) (t:=()) splitSourceFields.toLinearMap.toAddMonoidHom
  (.linear (s:=()) (t:=()) (dilationRFields shift).toLinearMap.toAddMonoidHom
   (.linear (s:=()) (t:=()) recombineRFields.toLinearMap.toAddMonoidHom (.const source)))

def splitUpdateWord (source : Branches) (shift : ℝ) : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .add (sourceSplitWord source shift)
  (.linear (s:=()) (t:=()) (-(ContinuousLinearMap.id ℂ Branches)).toLinearMap.toAddMonoidHom (sourceSplitWord source 0))

def splitActorCode (source : Branches) (shift : ℝ) : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .add (.var ()) (splitUpdateWord source shift)

theorem split_actor_increment (source before : Branches) (shift : ℝ) :
 (splitActorCode source shift).eval (OriginalKFinitePaWindowOperatorSourceAction.windowEnvironment before)-before =
 splitAction shift source-splitAction 0 source := by
 change (before+(splitAction shift source+ -(splitAction 0 source)))-before = _
 abel

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaUnitOutsideSourceDebtAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
