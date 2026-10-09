import H0mework.Versions.V2.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.EffectHistory.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.EffectHistory
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
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

variable (point : I.Carrier root recognition visit successor)
variable (word : List (I.Letter root recognition visit successor))
inductive Slot : Type u | source | waves
abbrev Value : Slot → Type u
  | .source => I.Carrier root recognition visit successor
  | .waves => Waves root recognition visit successor
abbrev Var : Slot → Type u := fun _ => PUnit.{u+1}
instance : (sort : Slot) → AddCommGroup (Value root recognition visit successor sort)
  | .source => inferInstance
  | .waves => inferInstance

def environment : Env (Value root recognition visit successor) Var
  | .source,_ => point
  | .waves,_ => 0

def sourceProgramme : List (I.Letter root recognition visit successor) →
    Expr (Value root recognition visit successor) Var .source → Expr (Value root recognition visit successor) Var .source
  | [],expression => expression
  | letter::rest,expression => sourceProgramme rest
      (.linear (I.actions root recognition visit successor transition alignment U7 calculus count letter).toAddMonoidHom expression)
def waveProgramme : List (I.Letter root recognition visit successor) →
    Expr (Value root recognition visit successor) Var .waves → Expr (Value root recognition visit successor) Var .waves
  | [],expression => expression
  | letter::rest,expression => waveProgramme rest
      (.linear (wave root recognition visit successor letter).toAddMonoidHom expression)

def programme : Expr (Value root recognition visit successor) Var .waves :=
  .add (waveProgramme root recognition visit successor word
    (.linear (s:=Slot.source) (observe root recognition visit successor transition alignment U7 calculus count).toAddMonoidHom (.var PUnit.unit)))
    (.linear (s:=Slot.source) (-(observe root recognition visit successor transition alignment U7 calculus count).toAddMonoidHom)
      (sourceProgramme root recognition visit successor transition alignment U7 calculus count word (.var PUnit.unit)))

theorem source_eval (expression : Expr (Value root recognition visit successor) Var .source) :
    (sourceProgramme root recognition visit successor transition alignment U7 calculus count word expression).eval
      (environment root recognition visit successor point) =
    SourceGeneratedActionWords.run (I.actions root recognition visit successor transition alignment U7 calculus count) word
      (expression.eval (environment root recognition visit successor point)) := by
  induction word generalizing expression with
  | nil => rfl
  | cons letter rest previous => exact previous (.linear (I.actions root recognition visit successor transition alignment U7 calculus count letter).toAddMonoidHom expression)
theorem wave_eval (expression : Expr (Value root recognition visit successor) Var .waves) :
    (waveProgramme root recognition visit successor word expression).eval (environment root recognition visit successor point) =
    SourceGeneratedActionWords.run (wave root recognition visit successor) word
      (expression.eval (environment root recognition visit successor point)) := by
  induction word generalizing expression with
  | nil => rfl
  | cons letter rest previous => exact previous (.linear (wave root recognition visit successor letter).toAddMonoidHom expression)
theorem programme_value : (programme root recognition visit successor transition alignment U7 calculus count word).eval
    (environment root recognition visit successor point) = total root recognition visit successor transition alignment U7 calculus count point word := by
  change (waveProgramme root recognition visit successor word _).eval _ +
    (-(observe root recognition visit successor transition alignment U7 calculus count).toAddMonoidHom)
      ((sourceProgramme root recognition visit successor transition alignment U7 calculus count word _).eval _) = _
  rw [wave_eval,source_eval]
  simp only [Expr.eval,environment,AddMonoidHom.neg_apply,total,SourceGeneratedActionEffectHistory.residual,observe,LinearMap.toAddMonoidHom_coe,LinearMap.comp_apply,sub_eq_add_neg]
theorem source_budget (expression : Expr (Value root recognition visit successor) Var .source) :
    remaining (sourceProgramme root recognition visit successor transition alignment U7 calculus count word expression)=remaining expression+word.length := by
  induction word generalizing expression with
  | nil => simp only [sourceProgramme,List.length_nil,Nat.add_zero]
  | cons letter rest previous => rw [sourceProgramme,previous]; change remaining expression+1+rest.length=remaining expression+(rest.length+1); omega
theorem wave_budget (expression : Expr (Value root recognition visit successor) Var .waves) :
    remaining (waveProgramme root recognition visit successor word expression)=remaining expression+word.length := by
  induction word generalizing expression with
  | nil => simp only [waveProgramme,List.length_nil,Nat.add_zero]
  | cons letter rest previous => rw [waveProgramme,previous]; change remaining expression+1+rest.length=remaining expression+(rest.length+1); omega
theorem programme_budget : remaining (programme root recognition visit successor transition alignment U7 calculus count word)=2*word.length+5 := by
  change remaining (waveProgramme root recognition visit successor word _)+
    (remaining (sourceProgramme root recognition visit successor transition alignment U7 calculus count word _)+1)+1=_
  rw [wave_budget,source_budget]
  change (2+word.length)+((1+word.length)+1)+1=_
  omega

def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=Value root recognition visit successor) (Var:=Var) (sort:=Slot.waves) :=
  ⟨environment root recognition visit successor point,programme root recognition visit successor transition alignment U7 calculus count word⟩
def originalReader {current : V.Current}
    (_ : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :=
  raw root recognition visit successor transition alignment U7 calculus count point word
abbrev paidSourceResult := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
  (I.sourceRoot root recognition visit successor transition alignment U7 calculus count point word).toAuthoritativeRoot
  (originalReader root recognition visit successor transition alignment U7 calculus count point word)
  ((I.sourceRoot root recognition visit successor transition alignment U7 calculus count point word).emitted visit.current)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.EffectHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
