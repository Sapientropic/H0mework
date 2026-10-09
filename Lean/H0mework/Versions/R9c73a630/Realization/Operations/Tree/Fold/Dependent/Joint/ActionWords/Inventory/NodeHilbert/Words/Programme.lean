import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Words.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Words
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
variable (seedWord queryWord : List (Letter root recognition visit successor))
abbrev Slot := NodeHilbert.Slot
namespace Slot
export NodeHilbert.Slot (model measured)
end Slot
abbrev Value := NodeHilbert.Value root recognition visit successor transition alignment U7 calculus count
abbrev Var := NodeHilbert.Var
abbrev environment := NodeHilbert.environment root recognition visit successor transition alignment U7 calculus count point seedWord

def modelProgramme : List (Letter root recognition visit successor) → Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .model →
    Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .model
  | [],expression => expression
  | letter::rest,expression => modelProgramme rest
      (.linear (advance root recognition visit successor transition alignment U7 calculus count letter).toAddMonoidHom expression)
def waveProgramme : List (Letter root recognition visit successor) → Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .measured →
    Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .measured
  | [],expression => expression
  | letter::rest,expression => waveProgramme rest
      (.linear ((evolution root recognition visit successor letter).toLinearMap.restrictScalars ℤ).toAddMonoidHom expression)
def programme : Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .measured :=
  .add (waveProgramme root recognition visit successor transition alignment U7 calculus count queryWord
    (.linear (s:=Slot.model) (measurement root recognition visit successor transition alignment U7 calculus count).toAddMonoidHom (.var PUnit.unit)))
    (.linear (s:=Slot.model) (-(measurement root recognition visit successor transition alignment U7 calculus count).toAddMonoidHom)
      (modelProgramme root recognition visit successor transition alignment U7 calculus count queryWord (.var PUnit.unit)))
theorem model_eval (sourceEnv : Env (Value root recognition visit successor transition alignment U7 calculus count) Var)
    (expression : Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .model) :
    (modelProgramme root recognition visit successor transition alignment U7 calculus count queryWord expression).eval sourceEnv =
    SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) queryWord
      (expression.eval sourceEnv) := by
  induction queryWord generalizing expression with
  | nil => rfl
  | cons letter rest previous => exact previous (.linear (advance root recognition visit successor transition alignment U7 calculus count letter).toAddMonoidHom expression)
theorem wave_eval (sourceEnv : Env (Value root recognition visit successor transition alignment U7 calculus count) Var)
    (expression : Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .measured) :
    (waveProgramme root recognition visit successor transition alignment U7 calculus count queryWord expression).eval sourceEnv =
      wordEvolution root recognition visit successor queryWord (expression.eval sourceEnv) := by
  induction queryWord generalizing expression with
  | nil => rfl
  | cons letter rest previous => exact previous (.linear ((evolution root recognition visit successor letter).toLinearMap.restrictScalars ℤ).toAddMonoidHom expression)
theorem programme_equation (sourceEnv : Env (Value root recognition visit successor transition alignment U7 calculus count) Var) :
    (programme root recognition visit successor transition alignment U7 calculus count queryWord).eval sourceEnv =
      effect root recognition visit successor transition alignment U7 calculus count queryWord (sourceEnv .model PUnit.unit) := by
  change (waveProgramme root recognition visit successor transition alignment U7 calculus count queryWord _).eval sourceEnv +
    (-(measurement root recognition visit successor transition alignment U7 calculus count).toAddMonoidHom)
      ((modelProgramme root recognition visit successor transition alignment U7 calculus count queryWord _).eval sourceEnv)=_
  rw [wave_eval,model_eval]
  simp only [Expr.eval,AddMonoidHom.neg_apply,LinearMap.toAddMonoidHom_coe,
    effect,SourceGeneratedIntegralCoherentCovariance.couplingResidual,action,sub_eq_add_neg]
theorem model_budget (expression : Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .model) :
    remaining (modelProgramme root recognition visit successor transition alignment U7 calculus count queryWord expression)=remaining expression+queryWord.length := by
  induction queryWord generalizing expression with
  | nil => simp only [modelProgramme,List.length_nil,Nat.add_zero]
  | cons letter rest previous => rw [modelProgramme,previous]; change remaining expression+1+rest.length=remaining expression+(rest.length+1); omega
theorem wave_budget (expression : Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .measured) :
    remaining (waveProgramme root recognition visit successor transition alignment U7 calculus count queryWord expression)=remaining expression+queryWord.length := by
  induction queryWord generalizing expression with
  | nil => simp only [waveProgramme,List.length_nil,Nat.add_zero]
  | cons letter rest previous => rw [waveProgramme,previous]; change remaining expression+1+rest.length=remaining expression+(rest.length+1); omega
theorem programme_budget : remaining (programme root recognition visit successor transition alignment U7 calculus count queryWord)=2*queryWord.length+5 := by
  change remaining (waveProgramme root recognition visit successor transition alignment U7 calculus count queryWord _)+
    (remaining (modelProgramme root recognition visit successor transition alignment U7 calculus count queryWord _)+1)+1=_
  rw [wave_budget,model_budget]
  change (2+queryWord.length)+((1+queryWord.length)+1)+1=_
  omega
abbrev nextValue := SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) queryWord
  (Inventory.normal root recognition visit successor transition alignment U7 calculus count point seedWord)
def pairRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=SourceOperationScalarInventoryLift.PairValue (Value root recognition visit successor transition alignment U7 calculus count))
    (Var:=Var) (sort:=Slot.measured) :=
  ⟨SourceOperationScalarInventoryLift.pairEnvironment
      (environment root recognition visit successor transition alignment U7 calculus count point seedWord)
      (NodeHilbert.environmentAt root recognition visit successor transition alignment U7 calculus count
        (nextValue root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)-
        environment root recognition visit successor transition alignment U7 calculus count point seedWord),
    SourceOperationScalarInventoryLift.liftExpr (programme root recognition visit successor transition alignment U7 calculus count queryWord)⟩
def pairReader {current : V.Current}
    (_ : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :=
  pairRaw root recognition visit successor transition alignment U7 calculus count point seedWord queryWord
abbrev pairResult := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt root.toAuthoritativeRoot
  (pairReader root recognition visit successor transition alignment U7 calculus count point seedWord queryWord)
  (root.emitted visit.current)
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=Value root recognition visit successor transition alignment U7 calculus count) (Var:=Var) (sort:=Slot.measured) :=
  ⟨environment root recognition visit successor transition alignment U7 calculus count point seedWord,
    programme root recognition visit successor transition alignment U7 calculus count queryWord⟩
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Words
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
