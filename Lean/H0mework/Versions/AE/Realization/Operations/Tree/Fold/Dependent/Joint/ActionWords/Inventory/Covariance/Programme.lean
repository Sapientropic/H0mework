import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Covariance.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Covariance
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
variable (actor : Actor root recognition visit successor)
inductive Slot : Type u | model | measured
abbrev Value : Slot → Type u
  | .model => Model root recognition visit successor transition alignment U7 calculus count
  | .measured => H
abbrev Var : Slot → Type u := fun _ => PUnit.{u+1}
instance : (slot : Slot) → AddCommGroup (Value root recognition visit successor transition alignment U7 calculus count slot)
  | .model => inferInstance
  | .measured => inferInstance
def environmentAt (value : Model root recognition visit successor transition alignment U7 calculus count) :
    Env (Value root recognition visit successor transition alignment U7 calculus count) Var
  | .model,_ => value
  | .measured,_ => 0
variable (point : Carrier root recognition visit successor) (word : List (Letter root recognition visit successor))
def environment := environmentAt root recognition visit successor transition alignment U7 calculus count
  (Inventory.normal root recognition visit successor transition alignment U7 calculus count point word)
def updatedEnvironment := environmentAt root recognition visit successor transition alignment U7 calculus count
  (advance root recognition visit successor transition alignment U7 calculus count (letter root recognition visit successor actor)
    (Inventory.normal root recognition visit successor transition alignment U7 calculus count point word))

def programme : Expr (Value root recognition visit successor transition alignment U7 calculus count) Var .measured :=
  .add
    (.linear (s:=Slot.measured) (t:=Slot.measured) ((evolution root recognition visit successor actor).toLinearMap.restrictScalars ℤ).toAddMonoidHom
      (.linear (s:=Slot.model) (t:=Slot.measured) (feature root recognition visit successor transition alignment U7 calculus count actor).toAddMonoidHom (.var PUnit.unit)))
    (.linear (s:=Slot.model) (t:=Slot.measured) (-(feature root recognition visit successor transition alignment U7 calculus count actor).toAddMonoidHom)
      (.linear (s:=Slot.model) (t:=Slot.model) (advance root recognition visit successor transition alignment U7 calculus count
        (letter root recognition visit successor actor)).toAddMonoidHom (.var PUnit.unit)))

theorem programme_value : (programme root recognition visit successor transition alignment U7 calculus count actor).eval
    (environment root recognition visit successor transition alignment U7 calculus count point word) =
      effect root recognition visit successor transition alignment U7 calculus count actor
        (Inventory.normal root recognition visit successor transition alignment U7 calculus count point word) := by
  simp only [programme,Expr.eval,environment,environmentAt,AddMonoidHom.neg_apply,LinearMap.toAddMonoidHom_coe,
    LinearMap.restrictScalars_apply,LinearIsometry.coe_toLinearMap,
    effect,SourceGeneratedIntegralCoherentCovariance.couplingResidual,action,sub_eq_add_neg]

theorem programme_next : (programme root recognition visit successor transition alignment U7 calculus count actor).eval
    (updatedEnvironment root recognition visit successor transition alignment U7 calculus count actor point word) =
      effect root recognition visit successor transition alignment U7 calculus count actor
        (advance root recognition visit successor transition alignment U7 calculus count (letter root recognition visit successor actor)
          (Inventory.normal root recognition visit successor transition alignment U7 calculus count point word)) := by
  simp only [programme,Expr.eval,updatedEnvironment,environmentAt,AddMonoidHom.neg_apply,LinearMap.toAddMonoidHom_coe,
    LinearMap.restrictScalars_apply,LinearIsometry.coe_toLinearMap,
    effect,SourceGeneratedIntegralCoherentCovariance.couplingResidual,action,sub_eq_add_neg]

def pairSourceRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=SourceOperationScalarInventoryLift.PairValue (Value root recognition visit successor transition alignment U7 calculus count))
    (Var:=Var) (sort:=Slot.measured) :=
  ⟨SourceOperationScalarInventoryLift.pairEnvironment
      (environment root recognition visit successor transition alignment U7 calculus count point word)
      (updatedEnvironment root recognition visit successor transition alignment U7 calculus count actor point word-
        environment root recognition visit successor transition alignment U7 calculus count point word),
    SourceOperationScalarInventoryLift.liftExpr (programme root recognition visit successor transition alignment U7 calculus count actor)⟩

theorem programme_cost : remaining (programme root recognition visit successor transition alignment U7 calculus count actor) = 7 := rfl
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Covariance
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
