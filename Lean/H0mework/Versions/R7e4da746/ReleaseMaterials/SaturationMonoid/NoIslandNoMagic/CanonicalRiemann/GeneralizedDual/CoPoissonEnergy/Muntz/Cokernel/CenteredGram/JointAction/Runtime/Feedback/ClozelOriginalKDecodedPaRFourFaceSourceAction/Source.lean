import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDecodedPaRSourceSuccessor.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRFourFaceSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
namespace Prior
export OriginalKDecodedPaRSourceSuccessor (decodedPaSource decodedSourceMaterial decoded_pa_source_qualified decoded_source_original_receipt receivedOwnR received_material_own_R actual_material_R_effect sourceBornPacket actualParentPacket actualParentFactory sourceRFactory)
end Prior
namespace FullR
export OriginalKFullSourceRAction (originalField variableAction sourceCode source_code_read source_code_effect)
end FullR
namespace C
export OriginalKFullSourceRAction.C (Value Var)
end C
abbrev Branches := OriginalKFinitePaWindowOperatorSourceAction.Branches

def fourierRead : Branches →L[ℂ] BurnolL2 :=
 (ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)
def pairedRead : Branches →L[ℂ] BurnolL2 := (1/2 : ℂ) • (FullR.originalField + fourierRead)
def siblingRead : Branches →L[ℂ] BurnolL2 := (1/2 : ℂ) • (FullR.originalField - fourierRead)
def sourceFourier : Branches →L[ℂ] BurnolL2 :=
 fourierL2.toLinearIsometry.toContinuousLinearMap.comp FullR.originalField

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

/-- R and FR supply the response faces; no defect field is identified with the actual velocity. -/
def responseFaceAction : Branches →L[ℂ] Branches :=
 (pairedRead.prod siblingRead).prod
  (((observation.coordinate/2-1/4) • siblingRead).prod ((observation.coordinate/2-1/4) • pairedRead))

def sourceContactAction : Branches →L[ℂ] Branches :=
 ((0 : Branches →L[ℂ] BurnolL2).prod 0).prod
  (((1/2 : ℂ) • (FullR.originalField-sourceFourier)).prod ((1/2 : ℂ) • (FullR.originalField+sourceFourier)))

def fourFaceAction : Branches →L[ℂ] Branches :=
 (responseFaceAction observation).comp (FullR.variableAction observation nontrivial half) + sourceContactAction

/-- The original variable R AST and source contact operation run before any physical target is read. -/
def fourFaceCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .add (.linear (s:=()) (t:=()) (responseFaceAction observation).toLinearMap.toAddMonoidHom
  (FullR.sourceCode observation nontrivial half))
  (.linear (s:=()) (t:=()) sourceContactAction.toLinearMap.toAddMonoidHom (.var ()))

theorem source_code_read (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (fourFaceCode observation nontrivial half).eval environment =
 fourFaceAction observation nontrivial half (environment () ()) := rfl

theorem source_code_effect (environment increment : Env (PairValue (PairValue C.Value)) C.Var) :
 (fourFaceCode observation nontrivial half).effect environment increment =
 fourFaceAction observation nontrivial half (increment () ()) := by
 have generated := Expr.eval_update (fourFaceCode observation nontrivial half) environment increment
 rw [source_code_read,source_code_read] at generated
 change fourFaceAction observation nontrivial half (environment () ()+increment () ()) = _ at generated
 rw [map_add] at generated
 exact add_left_cancel generated.symm

variable (depth ordinal : Nat) (h H N : ℝ)

def ownSourceEnvironment := OriginalKFinitePaWindowOperatorSourceAction.windowEnvironment
 (Prior.decodedSourceMaterial observation nontrivial half depth ordinal h H N)
def ownSourceRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=PairValue (PairValue C.Value)) (Var:=C.Var) (sort:=()) :=
 ⟨ownSourceEnvironment observation nontrivial half depth ordinal h H N,fourFaceCode observation nontrivial half⟩
def ownSourceTrace : Trace
 (ownSourceRaw observation nontrivial half depth ordinal h H N).environment
 (ownSourceRaw observation nontrivial half depth ordinal h H N).expression
 (.const ((ownSourceRaw observation nontrivial half depth ordinal h H N).expression.eval
  (ownSourceRaw observation nontrivial half depth ordinal h H N).environment)) := execution _ _

def ownFourFaceSource : Branches :=
 (ownSourceRaw observation nontrivial half depth ordinal h H N).expression.eval
  (ownSourceRaw observation nontrivial half depth ordinal h H N).environment

theorem own_four_face_source_generated : ownFourFaceSource observation nontrivial half depth ordinal h H N =
 fourFaceAction observation nontrivial half (Prior.decodedSourceMaterial observation nontrivial half depth ordinal h H N) := rfl

/-- Only decoded source material enters the literal stock word; the completed R/stock is computed by its operations. -/
def ownFourFaceWord : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .add (.linear (s:=()) (t:=()) (responseFaceAction observation).toLinearMap.toAddMonoidHom
  (.linear (s:=()) (t:=()) (FullR.variableAction observation nontrivial half).toLinearMap.toAddMonoidHom
   (.const (Prior.decodedSourceMaterial observation nontrivial half depth ordinal h H N))))
  (.linear (s:=()) (t:=()) sourceContactAction.toLinearMap.toAddMonoidHom
   (.const (Prior.decodedSourceMaterial observation nontrivial half depth ordinal h H N)))

theorem own_four_face_word_read (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (ownFourFaceWord observation nontrivial half depth ordinal h H N).eval environment =
 ownFourFaceSource observation nontrivial half depth ordinal h H N := rfl

def stockActorCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .add (.var ()) (ownFourFaceWord observation nontrivial half depth ordinal h H N)

theorem stock_actor_actual_increment (before : Branches) :
 (stockActorCode observation nontrivial half depth ordinal h H N).eval
  (OriginalKFinitePaWindowOperatorSourceAction.windowEnvironment before)-before =
 ownFourFaceSource observation nontrivial half depth ordinal h H N := by
 change (before+ownFourFaceSource observation nontrivial half depth ordinal h H N)-before = _
 abel

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRFourFaceSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
