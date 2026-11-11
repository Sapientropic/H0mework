import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRSourceMethodHistory
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRSourceMethodConsumer
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CenteredGram.IntegralGraphJointAction
namespace H
export BornRSourceMethodHistory
 (born retainedCode? retained_present retainedCode action raw receiver lowProgramme methodProgramme admitted
  reader_actual_source compiled actualSuccessor)
end H
namespace C
export CompletedSourceRCalculation (Value Var sourceConfiguration)
end C
namespace F
export BornWholeStockRConsumer (settledActionFrame registeredMaterial registeredValue actual_equation_registered)
namespace Generic
export BornWholeStockRConsumer.Generic (born_expression)
end Generic
end F
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence resultFace baseRoot)
end S
namespace R
export SourceGeneratedInquiryReceiptAction (actionReader actualMaterial registered)
end R
namespace Q
export SourceGeneratedInquiryReceiptAction.Inventory.ActualQuery (result_value)
end Q
namespace IS
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Source (request_environment)
end IS
namespace Generic
variable {Sorts:Type} {U X:Sorts→Type} [∀s,AddCommGroup (U s)] {s:Sorts}
theorem effect_zero (expr:Expr U X s) (env:Env U X) : expr.effect env 0=0 := by
 have generated:=Expr.eval_update expr env 0
 rw [add_zero] at generated
 exact add_left_cancel (generated.symm.trans (add_zero _).symm)
theorem pair_zero (expr:Expr U X s) (env:Env U X) :
 (liftExpr expr).eval (pairEnvironment env 0)=(expr.eval env,0) :=
 (eval_liftExpr expr env 0).trans
 (congrArg (fun effect=>(expr.eval env,effect)) (effect_zero expr env))
theorem negate_paid (expr:Expr U X s) (env:Env U X) :
 (Expr.linear (-AddMonoidHom.id (U s)) (Expr.linear (-AddMonoidHom.id (U s)) expr)).eval env=expr.eval env := by
 simp only [Expr.eval,AddMonoidHom.neg_apply,AddMonoidHom.id_apply,neg_neg]
theorem paired_action_value (r:U s→+U s) (expr:Expr U X s) (env:Env U X) :
 (Expr.linear ((r.prodMap r).prodMap (r.prodMap r)) (liftExpr (liftExpr expr))).eval
 (pairEnvironment (pairEnvironment env 0) 0)=((r (expr.eval env),0),0) := by
 change ((r.prodMap r).prodMap (r.prodMap r))
  ((liftExpr (liftExpr expr)).eval (pairEnvironment (pairEnvironment env 0) 0))=_
 rw [pair_zero,pair_zero]
 change ((r (expr.eval env),r 0),(r 0,r 0))=_
 rw [map_zero]
 rfl
end Generic
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat)
local notation "slot"=>CountedPaInitial.CompletedSourceRCalculation.Slot.branches
local notation "b"=>H.born observation nontrivial half depth ordinal
local notation "frame"=>F.settledActionFrame observation nontrivial half depth ordinal
local notation "material"=>F.registeredMaterial observation nontrivial half depth ordinal
local notation "pR"=>H.methodProgramme observation nontrivial half depth ordinal
local notation "receiver"=>H.receiver observation nontrivial half depth ordinal
local notation "wholeR"=>OriginalKFullSourceRAction.variableAction observation nontrivial half

theorem born_environment : (b).registered.input.environment=(material).environment := by
 exact (IS.request_environment (frame).old (frame).registered (frame).packetAt (frame).environment (frame).depth).trans (by rfl)

theorem retained_code_source : H.retainedCode? observation nontrivial half depth ordinal=
 some (Expr.linear (-AddMonoidHom.id (C.Value slot))
  (Expr.linear (-AddMonoidHom.id (C.Value slot)) (material).state.1)) := by
 have rawEq : (frame).registered.input.expression=
  RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression (material) :=
  F.actual_equation_registered observation nontrivial half depth ordinal
 have bornEq := F.Generic.born_expression (frame) C.sourceConfiguration
 have sourceEq := bornEq.trans (congrArg
  (fun expr:Expr C.Value C.Var slot=>Expr.add expr
   (Expr.linear (-AddMonoidHom.id (C.Value slot)) (frame).event.state.1)) rawEq)
 exact congrArg (fun expr:Expr C.Value C.Var slot=>
  match expr with
  | .add (.add _ paid) _ => some (Expr.linear (-AddMonoidHom.id (C.Value slot)) paid)
  | _ => none) sourceEq

theorem retained_value : (H.retainedCode observation nontrivial half depth ordinal).eval
 (b).registered.input.environment=F.registeredValue observation nontrivial half depth ordinal := by
 have source:=Option.get_of_eq_some (H.retained_present observation nontrivial half depth ordinal)
  (retained_code_source observation nontrivial half depth ordinal)
 exact (congrArg (fun expr:Expr C.Value C.Var slot=>expr.eval (b).registered.input.environment) source).trans <|
  (Generic.negate_paid (material).state.1 (b).registered.input.environment).trans <|
   congrArg (fun env:Env C.Value C.Var=>(material).state.1.eval env)
    (born_environment observation nontrivial half depth ordinal)

theorem raw_value : (H.raw observation nontrivial half depth ordinal).expression.eval
 (H.raw observation nontrivial half depth ordinal).environment=
 ((wholeR (F.registeredValue observation nontrivial half depth ordinal),0),0) := by
 exact (Generic.paired_action_value (wholeR).toLinearMap.toAddMonoidHom
  (H.retainedCode observation nontrivial half depth ordinal) (b).registered.input.environment).trans <|
   congrArg (fun stock:C.Value slot=>((wholeR stock,0),0))
    (retained_value observation nontrivial half depth ordinal)

theorem query_value : (S.resultFace receiver pR).rootRead.2.2.1=
 ((wholeR (F.registeredValue observation nontrivial half depth ordinal),0),0) := by
 have source:=Q.result_value receiver (H.lowProgramme observation nontrivial half depth ordinal)
 exact source.trans (raw_value observation nontrivial half depth ordinal)

abbrev registeredMaterial := R.actualMaterial receiver pR

def registeredValue := (registeredMaterial observation nontrivial half depth ordinal).state.1.eval
 (registeredMaterial observation nontrivial half depth ordinal).environment

theorem registered_whole_R : registeredValue observation nontrivial half depth ordinal=
 ((wholeR (F.registeredValue observation nontrivial half depth ordinal),0),0) := by
 exact (registeredMaterial observation nontrivial half depth ordinal).state.2.sound.symm.trans
  (raw_value observation nontrivial half depth ordinal)

theorem actual_equation_registered : (R.registered receiver pR).input.expression=
 RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression
  (registeredMaterial observation nontrivial half depth ordinal) := rfl

def actual_source_method_consumer :=
 PProd.mk (H.reader_actual_source observation nontrivial half depth ordinal) <|
 PProd.mk (query_value observation nontrivial half depth ordinal) <|
 PProd.mk (registered_whole_R observation nontrivial half depth ordinal) <|
 PProd.mk (actual_equation_registered observation nontrivial half depth ordinal) <|
 PProd.mk (H.compiled observation nontrivial half depth ordinal)
 (H.actualSuccessor observation nontrivial half depth ordinal)
end CountedPaInitial.BornRSourceMethodConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
