import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Recovery.Action
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceFullRecovery
open RootInquiryCompletion RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
open SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
variable (transition : GeneratedStepJointTransitionAt (recognition.generateStepAt visit) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (recognition.generateStepAt visit))
  (stepTargetPairingOccurrence (recognition.generateStepAt visit) successor))
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (count : Nat)

local instance : Module ℤ (JointCarrier root recognition visit successor transition alignment U7 calculus count) :=
  AddCommGroup.toIntModule _
variable (point : Carrier root recognition visit successor)
variable (seedWord : List (Letter root recognition visit successor))
variable (queryWord : List (Letter root recognition visit successor))
inductive Slot : Type u | model | joined
abbrev Value : Slot → Type u
 | .model => Original root recognition visit successor transition alignment U7 calculus count
 | .joined => Range root recognition visit successor transition alignment U7 calculus count
abbrev Var : Slot → Type u := fun _ => PUnit.{u+1}
instance : (slot : Slot) → AddCommGroup (Value root recognition visit successor transition alignment U7 calculus count slot)
 | .model => inferInstance
 | .joined => inferInstance

def environmentAt (value : Original root recognition visit successor transition alignment U7 calculus count) :
    Env (Value root recognition visit successor transition alignment U7 calculus count) Var
 | .model,_ => value
 | .joined,_ => 0

def rangeProgramme : List (Letter root recognition visit successor) →
    Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .joined →
    Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .joined
 | [],expression => expression
 | first::rest,expression => rangeProgramme rest
     (.linear (rangeAdvance root recognition visit successor transition alignment U7 calculus count first).toAddMonoidHom expression)

def programme : Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .model :=
  .linear (s:=Slot.joined) (recover root recognition visit successor transition alignment U7 calculus count).toAddMonoidHom
    (rangeProgramme root recognition visit successor transition alignment U7 calculus count queryWord
      (.linear (s:=Slot.model) (emit root recognition visit successor transition alignment U7 calculus count).toAddMonoidHom (.var PUnit.unit)))

theorem range_eval (value : Original root recognition visit successor transition alignment U7 calculus count)
    (expression : Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .joined) :
    (rangeProgramme root recognition visit successor transition alignment U7 calculus count queryWord expression).eval
      (environmentAt root recognition visit successor transition alignment U7 calculus count value)=
    SourceGeneratedActionWords.run (rangeAdvance root recognition visit successor transition alignment U7 calculus count) queryWord
      (expression.eval (environmentAt root recognition visit successor transition alignment U7 calculus count value)) := by
  induction queryWord generalizing expression with
  | nil => rfl
  | cons first rest previous => exact previous (.linear (rangeAdvance root recognition visit successor transition alignment U7 calculus count first).toAddMonoidHom expression)

theorem programme_value (value : Original root recognition visit successor transition alignment U7 calculus count) :
    (programme root recognition visit successor transition alignment U7 calculus count queryWord).eval
      (environmentAt root recognition visit successor transition alignment U7 calculus count value)=
    SourceGeneratedActionWords.run (PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count)
      queryWord value := by
  change recover root recognition visit successor transition alignment U7 calculus count
    ((rangeProgramme root recognition visit successor transition alignment U7 calculus count queryWord _).eval _)=_
  have evaluated := range_eval root recognition visit successor transition alignment U7 calculus count queryWord value
    (.linear (s:=Slot.model) (emit root recognition visit successor transition alignment U7 calculus count).toAddMonoidHom (.var PUnit.unit))
  exact (congrArg (recover root recognition visit successor transition alignment U7 calculus count) evaluated).trans
    ((recover_word root recognition visit successor transition alignment U7 calculus count queryWord (emit root recognition visit successor transition alignment U7 calculus count value)).trans
      (congrArg (SourceGeneratedActionWords.run (PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count) queryWord)
        (recover_emit root recognition visit successor transition alignment U7 calculus count value)))

theorem range_budget (expression : Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .joined) :
    remaining (rangeProgramme root recognition visit successor transition alignment U7 calculus count queryWord expression)=
      remaining expression+queryWord.length := by
  induction queryWord generalizing expression with
  | nil => simp only [rangeProgramme,List.length_nil,Nat.add_zero]
  | cons first rest previous => rw [rangeProgramme,previous]; change remaining expression+1+rest.length=remaining expression+(rest.length+1); omega

theorem programme_budget : remaining (programme root recognition visit successor transition alignment U7 calculus count queryWord)=queryWord.length+3 := by
  change remaining (rangeProgramme root recognition visit successor transition alignment U7 calculus count queryWord _)+1=_
  rw [range_budget]
  change (2+queryWord.length)+1=_
  omega
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceFullRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
