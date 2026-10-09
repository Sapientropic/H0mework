import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
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
inductive Slot : Type u | source | model
abbrev Value : Slot → Type u
 | .source => Carrier root recognition visit successor
 | .model => Model root recognition visit successor transition alignment U7 calculus count
abbrev Var : Slot → Type u := fun _ => PUnit.{u+1}
instance : (slot : Slot) → AddCommGroup (Value root recognition visit successor transition alignment U7 calculus count slot)
 | .source => inferInstance
 | .model => inferInstance
variable (point : Carrier root recognition visit successor)
def environment : Env (Value root recognition visit successor transition alignment U7 calculus count) Var
 | .source,_ => point
 | .model,_ => 0
def sourceProgramme : List Letter →
    Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .source →
    Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .source
 | [],expression => expression
 | letter :: rest,expression => sourceProgramme rest
     (.linear (actions root recognition visit successor transition alignment U7 calculus count letter).toAddMonoidHom expression)

theorem source_eval (word : List Letter)
    (expression : Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .source) :
    (sourceProgramme root recognition visit successor transition alignment U7 calculus count word expression).eval
      (environment root recognition visit successor transition alignment U7 calculus count point) =
        SourceGeneratedActionWords.run (actions root recognition visit successor transition alignment U7 calculus count) word
          (expression.eval (environment root recognition visit successor transition alignment U7 calculus count point)) := by
  induction word generalizing expression with
  | nil => rfl
  | cons letter rest previous =>
    exact previous (.linear (actions root recognition visit successor transition alignment U7 calculus count letter).toAddMonoidHom expression)

def programme (word : List Letter) : Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .model :=
 .linear (s:=.source) (SourceGeneratedActionWords.projection
  (actions root recognition visit successor transition alignment U7 calculus count)
  (read root recognition visit successor transition alignment U7 calculus count) .simultaneous).toAddMonoidHom
   (sourceProgramme root recognition visit successor transition alignment U7 calculus count word (.var PUnit.unit))

theorem programme_value (word : List Letter) : (programme root recognition visit successor transition alignment U7 calculus count word).eval
    (environment root recognition visit successor transition alignment U7 calculus count point) =
      SourceGeneratedActionWords.run (SourceGeneratedActionWords.advance
        (actions root recognition visit successor transition alignment U7 calculus count)
        (read root recognition visit successor transition alignment U7 calculus count) .simultaneous) word
          (SourceGeneratedActionWords.projection (actions root recognition visit successor transition alignment U7 calculus count)
            (read root recognition visit successor transition alignment U7 calculus count) .simultaneous point) := by
  change SourceGeneratedActionWords.projection _ _ _ ((sourceProgramme _ _ _ _ _ _ _ _ _ word (.var PUnit.unit)).eval _) = _
  rw [source_eval]
  exact (SourceGeneratedActionWords.run_source _ _ _ _ _).symm
theorem source_budget (word : List Letter)
    (expression : Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .source) :
    remaining (sourceProgramme root recognition visit successor transition alignment U7 calculus count word expression) =
      remaining expression + word.length := by
  induction word generalizing expression with
  | nil => simp only [sourceProgramme,List.length_nil,Nat.add_zero]
  | cons letter rest previous =>
      rw [sourceProgramme,previous]
      change remaining expression + 1 + rest.length = remaining expression + (rest.length+1)
      omega

theorem programme_budget (word : List Letter) :
    remaining (programme root recognition visit successor transition alignment U7 calculus count word) = word.length + 2 := by
  change remaining (sourceProgramme root recognition visit successor transition alignment U7 calculus count word (.var PUnit.unit)) + 1 = _
  rw [source_budget]
  change 1 + word.length + 1 = _
  omega
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
