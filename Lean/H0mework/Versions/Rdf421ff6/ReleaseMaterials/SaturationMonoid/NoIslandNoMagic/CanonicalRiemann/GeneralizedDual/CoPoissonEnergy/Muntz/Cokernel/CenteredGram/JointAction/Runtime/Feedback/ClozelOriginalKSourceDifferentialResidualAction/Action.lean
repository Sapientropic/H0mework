import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceDifferentialResidualAction.GradedField
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialResidualAction
open Complex BurnolPhysicalState
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {W : Unit→Type} [∀ target,AddCommGroup (W target)]
local instance completeLiftGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value W grade target) := L.groups W grade

/-- The existing pairLinear action retains each ordered source old/effect role through its actual graded family. -/
def sourceLiftOperator (action : PairValue W ()→+PairValue W ()) :
 (grade : Nat)→PairValue (L.Value W grade) ()→+PairValue (L.Value W grade) ()
 | 0=>action
 | grade+1=>pairLinear (sourceLiftOperator action grade)

theorem source_lift_operator_read (action : PairValue W ()→+PairValue W ())
 (grade : Nat) (value : PairValue (L.Value W grade) ()) :
 sourceCollapseHom grade (sourceLiftOperator action grade value)=action (sourceCollapseHom grade value) := by
 induction grade with
 | zero=>rfl
 | succ grade previous=>
  change sourceCollapseHom grade ((sourceLiftOperator action grade) value.1+(sourceLiftOperator action grade) value.2)=_
  rw [map_add,previous,previous]
  exact (action.map_add _ _).symm.trans (congrArg action (map_add (sourceCollapseHom grade) value.1 value.2).symm)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local instance completeBaseGroups (initialGrade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue OriginalR.C.Value) initialGrade target) :=
 L.groups (PairValue OriginalR.C.Value) initialGrade
local instance completeOriginGroups (initialGrade originGrade : Nat) : ∀ target,AddCommGroup
 (L.Value (L.Value (PairValue OriginalR.C.Value) initialGrade) originGrade target) :=
 L.groups (L.Value (PairValue OriginalR.C.Value) initialGrade) originGrade
local instance completeRuntimeGroups (initialGrade originGrade grade : Nat) : ∀ target,AddCommGroup
 (L.Value (L.Value (L.Value (PairValue OriginalR.C.Value) initialGrade) originGrade) grade target) :=
 L.groups (L.Value (L.Value (PairValue OriginalR.C.Value) initialGrade) originGrade) grade
variable (initialGrade originGrade grade : Nat)

/-- These are the original init/source-born/runtime restrictions, each read from its actual packet; none identifies an occurrence by a numeric counter. -/
def completeRSourceRead := (sourceCollapseHom (W:=PairValue OriginalR.C.Value) initialGrade).comp
 ((sourceCollapseHom (W:=L.Value (PairValue OriginalR.C.Value) initialGrade) originGrade).comp
  (sourceCollapseHom (W:=L.Value (L.Value (PairValue OriginalR.C.Value) initialGrade) originGrade) grade))

def completeRSourceAction := sourceLiftOperator
 (W:=L.Value (L.Value (PairValue OriginalR.C.Value) initialGrade) originGrade)
 (sourceLiftOperator (W:=L.Value (PairValue OriginalR.C.Value) initialGrade)
  (sourceLiftOperator (W:=PairValue OriginalR.C.Value)
   (OriginalR.variableAction observation nontrivial half).toLinearMap.toAddMonoidHom initialGrade) originGrade) grade

theorem complete_R_source_action_read
 (value : PairValue (L.Value (L.Value (L.Value (PairValue OriginalR.C.Value) initialGrade) originGrade) grade) ()) :
 completeRSourceRead initialGrade originGrade grade
  (completeRSourceAction observation nontrivial half initialGrade originGrade grade value)=
 OriginalR.variableAction observation nontrivial half (completeRSourceRead initialGrade originGrade grade value) := by
 change sourceCollapseHom initialGrade (sourceCollapseHom originGrade (sourceCollapseHom grade
  (sourceLiftOperator (sourceLiftOperator (sourceLiftOperator _ initialGrade) originGrade) grade value)))=_
 rw [source_lift_operator_read,source_lift_operator_read,source_lift_operator_read]
 rfl

variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=L.Value (L.Value (L.Value (PairValue OriginalR.C.Value) initialGrade) originGrade) grade)
 (Var:=OriginalR.C.Var) (sort:=()))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : D.I.Occurrence frame (current:=current))

def completeResidualTotalRole :=
 let V:=L.Value (L.Value (L.Value (PairValue OriginalR.C.Value) initialGrade) originGrade) grade ()
 ((AddMonoidHom.fst V V)+(AddMonoidHom.snd V V)).prod (0:V×V→+V)

/-- Explicit source old/change addition precedes the role-preserving original R action. -/
def completeResidualRCode : Expr
 (PairValue (L.Value (L.Value (L.Value (PairValue OriginalR.C.Value) initialGrade) originGrade) grade)) OriginalR.C.Var () :=
 .linear (s:=()) (t:=()) (completeRSourceAction observation nontrivial half initialGrade originGrade grade)
  (.linear (s:=()) (t:=()) (completeResidualTotalRole initialGrade originGrade grade) (sourceResidualCode frame supplied))

theorem complete_R_code_read :
 completeRSourceRead initialGrade originGrade grade
 ((completeResidualRCode observation nontrivial half initialGrade originGrade grade frame supplied).eval
  (sourceResidualEnvironment frame supplied))=
 OriginalR.variableAction observation nontrivial half
 (completeRSourceRead initialGrade originGrade grade
  (completeResidualTotalRole initialGrade originGrade grade
   ((sourceResidualCode frame supplied).eval (sourceResidualEnvironment frame supplied)))) :=
 complete_R_source_action_read _ _ _ _ _ _ _

theorem complete_R_code_effect (environment increment : Env
 (PairValue (L.Value (L.Value (L.Value (PairValue OriginalR.C.Value) initialGrade) originGrade) grade)) OriginalR.C.Var) :
 (completeResidualRCode observation nontrivial half initialGrade originGrade grade frame supplied).effect environment increment=
 completeRSourceAction observation nontrivial half initialGrade originGrade grade
  (completeResidualTotalRole initialGrade originGrade grade ((sourceResidualCode frame supplied).effect environment increment)) := by
 have actual:=Expr.eval_update (completeResidualRCode observation nontrivial half initialGrade originGrade grade frame supplied) environment increment
 change completeRSourceAction observation nontrivial half initialGrade originGrade grade
  (completeResidualTotalRole initialGrade originGrade grade ((sourceResidualCode frame supplied).eval (environment+increment)))=
  completeRSourceAction observation nontrivial half initialGrade originGrade grade
   (completeResidualTotalRole initialGrade originGrade grade ((sourceResidualCode frame supplied).eval environment))+_ at actual
 rw [Expr.eval_update,map_add,map_add] at actual
 exact add_left_cancel actual.symm

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialResidualAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
