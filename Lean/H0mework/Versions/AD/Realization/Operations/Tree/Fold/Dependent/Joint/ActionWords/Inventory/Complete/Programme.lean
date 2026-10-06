import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Complete.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Complete
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


variable (point : Carrier root recognition visit successor)
variable (word : List (Letter root recognition visit successor))
inductive Slot : Type u | source | whole | model
abbrev Value : Slot → Type u
 | .source => Carrier root recognition visit successor
 | .whole => Whole root recognition visit successor transition alignment U7 calculus count
 | .model => Model root recognition visit successor transition alignment U7 calculus count
abbrev Var : Slot → Type u := fun _ => PUnit.{u+1}
instance : (slot : Slot) → AddCommGroup (Value root recognition visit successor transition alignment U7 calculus count slot)
 | .source => inferInstance
 | .whole => inferInstance
 | .model => inferInstance
def environment : Env (Value root recognition visit successor transition alignment U7 calculus count) Var
 | .source,_ => point
 | .whole,_ => 0
 | .model,_ => 0
def wholeProgramme : List (Letter root recognition visit successor) →
    Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .whole →
    Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .whole
 | [],expression => expression
 | letter::rest,expression => wholeProgramme rest
     (.linear (completeAdvance root recognition visit successor transition alignment U7 calculus count letter).toAddMonoidHom expression)
def programme : Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .model :=
 .linear (s:=Slot.whole) (equivalence root recognition visit successor transition alignment U7 calculus count).symm.toLinearMap.toAddMonoidHom
   (wholeProgramme root recognition visit successor transition alignment U7 calculus count word
     (.linear (s:=Slot.source) (sourceMap root recognition visit successor transition alignment U7 calculus count).toAddMonoidHom (.var PUnit.unit)))
theorem whole_eval (expression : Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .whole) :
    (wholeProgramme root recognition visit successor transition alignment U7 calculus count word expression).eval
      (environment root recognition visit successor transition alignment U7 calculus count point)=
      SourceGeneratedActionWords.run (completeAdvance root recognition visit successor transition alignment U7 calculus count) word
        (expression.eval (environment root recognition visit successor transition alignment U7 calculus count point)) := by
  induction word generalizing expression with
  | nil => rfl
  | cons letter rest previous => exact previous (.linear (completeAdvance root recognition visit successor transition alignment U7 calculus count letter).toAddMonoidHom expression)
theorem programme_value : (programme root recognition visit successor transition alignment U7 calculus count word).eval
    (environment root recognition visit successor transition alignment U7 calculus count point) =
      SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) word
        (projection root recognition visit successor transition alignment U7 calculus count point) := by
  change (equivalence root recognition visit successor transition alignment U7 calculus count).symm
    ((wholeProgramme root recognition visit successor transition alignment U7 calculus count word _).eval _) = _
  rw [whole_eval]
  exact (model_action root recognition visit successor transition alignment U7 calculus count
    (sourceMap root recognition visit successor transition alignment U7 calculus count point) word).trans
      (congrArg (SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) word)
        (SourceGeneratedActionWords.completion_inverse_source _ _ _ point))
theorem whole_budget (expression : Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .whole) :
    remaining (wholeProgramme root recognition visit successor transition alignment U7 calculus count word expression)=remaining expression+word.length := by
  induction word generalizing expression with
  | nil => simp only [wholeProgramme,List.length_nil,Nat.add_zero]
  | cons letter rest previous => rw [wholeProgramme,previous]; change remaining expression+1+rest.length=remaining expression+(rest.length+1); omega
theorem programme_budget : remaining (programme root recognition visit successor transition alignment U7 calculus count word)=word.length+3 := by
  change remaining (wholeProgramme root recognition visit successor transition alignment U7 calculus count word _)+1=_
  rw [whole_budget]
  change (2+word.length)+1=_
  omega
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=Value root recognition visit successor transition alignment U7 calculus count) (Var:=Var) (sort:=Slot.model) :=
  ⟨environment root recognition visit successor transition alignment U7 calculus count point,
    programme root recognition visit successor transition alignment U7 calculus count word⟩
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Complete
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
