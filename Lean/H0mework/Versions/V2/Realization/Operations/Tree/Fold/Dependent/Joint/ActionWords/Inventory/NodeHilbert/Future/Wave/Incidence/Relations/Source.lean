import H0mework.Versions.V2.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Relations.Generic
import H0mework.Realization.Operations.Substitution.Complex
import Lean.LibrarySuggestions.Basic
-- Complete relation/query signatures use a local suggestion metadata exclusion.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceIncidenceRelations"
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
abbrev Value := PaidSourceIncidence.Value root recognition visit successor transition alignment U7 calculus count
abbrev Var := PaidSourceIncidence.Var
def binding : ∀ slot, Var slot → Expr (Value root recognition visit successor transition alignment U7 calculus count) Var slot
 | .model,name => .linear (s:=PaidSourceIncidence.Slot.model)
     (Inventory.advance root recognition visit successor transition alignment U7 calculus count letter).toAddMonoidHom (.var name)
 | .orbit,name => .linear (s:=PaidSourceIncidence.Slot.orbit)
     (PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count letter).toAddMonoidHom (.var name)
theorem environment_source (value : PaidSourceFullOrbit.FullCarrier root recognition visit successor transition alignment U7 calculus count) :
    SourceSubstitution.sourceEnvironment (binding root recognition visit successor transition alignment U7 calculus count letter)
      (PaidSourceIncidenceBranch.orbitEnvironment root recognition visit successor transition alignment U7 calculus count value)=
      PaidSourceIncidenceBranch.orbitEnvironment root recognition visit successor transition alignment U7 calculus count (PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count letter value) := by
  funext slot name
  cases slot <;> rfl
abbrev words (slot : PaidSourceOrbit.NativeOrbitProgramme.Slot) :=
  substitution (R:=ℤ) (s:=slot) (binding root recognition visit successor transition alignment U7 calculus count letter)
def relationIndex (slot : PaidSourceOrbit.NativeOrbitProgramme.Slot)
    (value : PaidSourceFullOrbit.FullCarrier root recognition visit successor transition alignment U7 calculus count) :=
  ActualRelationSubstitution.index (s:=slot) (binding root recognition visit successor transition alignment U7 calculus count letter)
    (PaidSourceIncidenceBranch.orbitEnvironment root recognition visit successor transition alignment U7 calculus count value)
    (PaidSourceIncidenceBranch.orbitEnvironment root recognition visit successor transition alignment U7 calculus count (PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count letter value))
    (environment_source root recognition visit successor transition alignment U7 calculus count letter value)
def relationWords (slot : PaidSourceOrbit.NativeOrbitProgramme.Slot)
    (value : PaidSourceFullOrbit.FullCarrier root recognition visit successor transition alignment U7 calculus count) := Finsupp.lmapDomain ℤ ℤ (relationIndex root recognition visit successor transition alignment U7 calculus count letter slot value)
def complexMorphism (slot : PaidSourceOrbit.NativeOrbitProgramme.Slot)
    (value : PaidSourceFullOrbit.FullCarrier root recognition visit successor transition alignment U7 calculus count) :=
  SourceSubstitution.complexMorphism (R:=ℤ) (s:=slot) (binding root recognition visit successor transition alignment U7 calculus count letter)
    (PaidSourceIncidenceBranch.orbitEnvironment root recognition visit successor transition alignment U7 calculus count value)
theorem relation_index_boundary (slot : PaidSourceOrbit.NativeOrbitProgramme.Slot)
    (value : PaidSourceFullOrbit.FullCarrier root recognition visit successor transition alignment U7 calculus count)
    (generator : RelationIndex ℤ (PaidSourceIncidenceBranch.orbitEnvironment root recognition visit successor transition alignment U7 calculus count
      (PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count letter value)) slot) :
    relation (R:=ℤ) (PaidSourceIncidenceBranch.orbitEnvironment root recognition visit successor transition alignment U7 calculus count value)
      (relationIndex root recognition visit successor transition alignment U7 calculus count letter slot value generator)=
      (words root recognition visit successor transition alignment U7 calculus count letter slot) (relation (R:=ℤ)
        (PaidSourceIncidenceBranch.orbitEnvironment root recognition visit successor transition alignment U7 calculus count (PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count letter value)) generator) :=
  ActualRelationSubstitution.index_boundary _ _ _ (environment_source root recognition visit successor transition alignment U7 calculus count letter value) generator
theorem relation_square (slot : PaidSourceOrbit.NativeOrbitProgramme.Slot)
    (value : PaidSourceFullOrbit.FullCarrier root recognition visit successor transition alignment U7 calculus count) :
    (relationMap (R:=ℤ) (s:=slot) (PaidSourceIncidenceBranch.orbitEnvironment root recognition visit successor transition alignment U7 calculus count value)).comp
      (relationWords root recognition visit successor transition alignment U7 calculus count letter slot value)=
      (words root recognition visit successor transition alignment U7 calculus count letter slot).comp
        (relationMap (R:=ℤ) (s:=slot) (PaidSourceIncidenceBranch.orbitEnvironment root recognition visit successor transition alignment U7 calculus count
          (PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count letter value))) := by
  apply Finsupp.lhom_ext
  intro generator coefficient
  simp only [LinearMap.comp_apply,relationWords,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,relationMap,Finsupp.linearCombination_single,map_smul]
  exact congrArg (fun value => coefficient • value) (relation_index_boundary root recognition visit successor transition alignment U7 calculus count letter slot value generator)
theorem expression_source (slot : PaidSourceOrbit.NativeOrbitProgramme.Slot)
    (expression : Expr (Value root recognition visit successor transition alignment U7 calculus count) Var slot) (value : PaidSourceFullOrbit.FullCarrier root recognition visit successor transition alignment U7 calculus count) :
    (expression.subst (binding root recognition visit successor transition alignment U7 calculus count letter)).eval (PaidSourceIncidenceBranch.orbitEnvironment root recognition visit successor transition alignment U7 calculus count value)=
      expression.eval (PaidSourceIncidenceBranch.orbitEnvironment root recognition visit successor transition alignment U7 calculus count (PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count letter value)) :=
  (expression.eval_subst _ _).trans
    (congrArg expression.eval (environment_source root recognition visit successor transition alignment U7 calculus count letter value))
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceIncidenceRelations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
