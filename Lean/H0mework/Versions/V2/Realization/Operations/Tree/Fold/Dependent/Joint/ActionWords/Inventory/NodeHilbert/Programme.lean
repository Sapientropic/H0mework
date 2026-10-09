import H0mework.Versions.V2.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Gram
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert
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

variable (selectedLetter : Letter root recognition visit successor)
inductive Slot : Type u | model | measured
abbrev Value : Slot → Type u
  | .model => Model root recognition visit successor transition alignment U7 calculus count
  | .measured => Space root recognition visit successor
abbrev Var : Slot → Type u := fun _ => PUnit.{u+1}
instance : (slot : Slot) → AddCommGroup (Value root recognition visit successor transition alignment U7 calculus count slot)
  | .model => inferInstance
  | .measured => inferInstance
variable (point : Carrier root recognition visit successor) (word : List (Letter root recognition visit successor))
def environmentAt (value : Model root recognition visit successor transition alignment U7 calculus count) :
    Env (Value root recognition visit successor transition alignment U7 calculus count) Var
  | .model,_ => value
  | .measured,_ => 0
abbrev environment := environmentAt root recognition visit successor transition alignment U7 calculus count
  (Inventory.normal root recognition visit successor transition alignment U7 calculus count point word)
def programme : Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .measured :=
  .add (.linear (s:=Slot.measured) (t:=Slot.measured)
      ((evolution root recognition visit successor selectedLetter).toLinearMap.restrictScalars ℤ).toAddMonoidHom
      (.linear (s:=Slot.model) (measurement root recognition visit successor transition alignment U7 calculus count).toAddMonoidHom (.var PUnit.unit)))
    (.linear (s:=Slot.model) (-(measurement root recognition visit successor transition alignment U7 calculus count).toAddMonoidHom)
      (.linear (s:=Slot.model) (t:=Slot.model)
        (advance root recognition visit successor transition alignment U7 calculus count selectedLetter).toAddMonoidHom (.var PUnit.unit)))
theorem programme_value : (programme root recognition visit successor transition alignment U7 calculus count selectedLetter).eval
    (environment root recognition visit successor transition alignment U7 calculus count point word) =
      effect root recognition visit successor transition alignment U7 calculus count selectedLetter
        (Inventory.normal root recognition visit successor transition alignment U7 calculus count point word) := by
  simp only [programme,Expr.eval,environment,environmentAt,AddMonoidHom.neg_apply,LinearMap.toAddMonoidHom_coe,
    LinearMap.restrictScalars_apply,LinearIsometry.coe_toLinearMap,
    effect,SourceGeneratedIntegralCoherentCovariance.couplingResidual,action,sub_eq_add_neg]
theorem programme_cost : remaining (programme root recognition visit successor transition alignment U7 calculus count selectedLetter)=7 := rfl
abbrev nextValue := advance root recognition visit successor transition alignment U7 calculus count selectedLetter
  (Inventory.normal root recognition visit successor transition alignment U7 calculus count point word)
def pairRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=SourceOperationScalarInventoryLift.PairValue (Value root recognition visit successor transition alignment U7 calculus count))
    (Var:=Var) (sort:=Slot.measured) :=
  ⟨SourceOperationScalarInventoryLift.pairEnvironment
      (environment root recognition visit successor transition alignment U7 calculus count point word)
      (environmentAt root recognition visit successor transition alignment U7 calculus count
        (nextValue root recognition visit successor transition alignment U7 calculus count selectedLetter point word)-
        environment root recognition visit successor transition alignment U7 calculus count point word),
    SourceOperationScalarInventoryLift.liftExpr (programme root recognition visit successor transition alignment U7 calculus count selectedLetter)⟩
def pairReader {current : V.Current}
    (_ : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :=
  pairRaw root recognition visit successor transition alignment U7 calculus count selectedLetter point word
abbrev pairResult := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt root.toAuthoritativeRoot
  (pairReader root recognition visit successor transition alignment U7 calculus count selectedLetter point word)
  (root.emitted visit.current)
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=Value root recognition visit successor transition alignment U7 calculus count) (Var:=Var) (sort:=Slot.measured) :=
  ⟨environment root recognition visit successor transition alignment U7 calculus count point word,
    programme root recognition visit successor transition alignment U7 calculus count selectedLetter⟩
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
