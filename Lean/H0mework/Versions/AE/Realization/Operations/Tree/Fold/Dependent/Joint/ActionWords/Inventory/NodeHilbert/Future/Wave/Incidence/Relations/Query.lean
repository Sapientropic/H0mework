import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Relations.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceIncidenceRelations
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


open SourceOperationScalarPresentation SourceOperationScalarRelations
variable (letter : Letter root recognition visit successor)
variable (point : Carrier root recognition visit successor) (seedWord : List (Letter root recognition visit successor))
variable (bound : Nat) (queryWord : List (Letter root recognition visit successor))
abbrev actual := PaidSourceIncidenceBranch.current root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord
abbrev actualNext := PaidSourceIncidenceBranch.normal root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter

theorem actual_environment : SourceSubstitution.sourceEnvironment (binding root recognition visit successor transition alignment U7 calculus count letter)
    (PaidSourceIncidenceBranch.orbitEnvironment root recognition visit successor transition alignment U7 calculus count (actual root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord))=
      PaidSourceIncidenceBranch.orbitEnvironment root recognition visit successor transition alignment U7 calculus count (actualNext root recognition visit successor transition alignment U7 calculus count letter point seedWord bound queryWord) := by
  have square := environment_source root recognition visit successor transition alignment U7 calculus count letter
    (PaidSourceIncidenceBranch.current root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)
  have next := PaidSourceIncidenceBranch.normal_value root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter
  exact square.trans (congrArg (PaidSourceIncidenceBranch.orbitEnvironment root recognition visit successor transition alignment U7 calculus count) next.symm)

def queryRaw (slot : PaidSourceOrbit.NativeOrbitProgramme.Slot) (expression : Expr (Value root recognition visit successor transition alignment U7 calculus count) Var slot) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value:=Value root recognition visit successor transition alignment U7 calculus count) (Var:=Var) (sort:=slot) :=
  ⟨PaidSourceIncidenceBranch.orbitEnvironment root recognition visit successor transition alignment U7 calculus count (actual root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord),expression.subst (binding root recognition visit successor transition alignment U7 calculus count letter)⟩
def queryReader (slot : PaidSourceOrbit.NativeOrbitProgramme.Slot) (expression : Expr (Value root recognition visit successor transition alignment U7 calculus count) Var slot)
    {current : V.Current} (_ : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :=
  queryRaw root recognition visit successor transition alignment U7 calculus count letter point seedWord bound queryWord slot expression
abbrev queryValue (slot : PaidSourceOrbit.NativeOrbitProgramme.Slot) (expression : Expr (Value root recognition visit successor transition alignment U7 calculus count) Var slot) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value root.toAuthoritativeRoot visit.current
    (queryReader root recognition visit successor transition alignment U7 calculus count letter point seedWord bound queryWord slot expression)
theorem query_source (slot : PaidSourceOrbit.NativeOrbitProgramme.Slot) (expression : Expr (Value root recognition visit successor transition alignment U7 calculus count) Var slot) :
    queryValue root recognition visit successor transition alignment U7 calculus count letter point seedWord bound queryWord slot expression=
      expression.eval (PaidSourceIncidenceBranch.orbitEnvironment root recognition visit successor transition alignment U7 calculus count (actualNext root recognition visit successor transition alignment U7 calculus count letter point seedWord bound queryWord)) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source _ _ _).trans
    ((expression.eval_subst _ _).trans (congrArg expression.eval (actual_environment root recognition visit successor transition alignment U7 calculus count letter point seedWord bound queryWord)))
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceIncidenceRelations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
