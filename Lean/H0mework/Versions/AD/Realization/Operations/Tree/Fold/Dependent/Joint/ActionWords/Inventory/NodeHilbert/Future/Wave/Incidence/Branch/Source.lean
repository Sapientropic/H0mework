import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Mouth
import Lean.LibrarySuggestions.Basic
-- Exclude only the complete incidence runtime namespace from suggestion export.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceIncidenceBranch"
-- Scope suggestion export to this complete branch runtime namespace.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceIncidenceBranch"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceIncidenceBranch
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


variable (point : Carrier root recognition visit successor) (seedWord : List (Letter root recognition visit successor))
variable (bound : Nat) (queryWord : List (Letter root recognition visit successor))
abbrev selected := Wave.selected root recognition visit successor transition alignment U7 calculus count bound queryWord
abbrev selectedPoint := Wave.selectedPoint root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord
def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=PaidSourceIncidence.Value root recognition visit successor transition alignment U7 calculus count) (Var:=PaidSourceIncidence.Var) (sort:=PaidSourceIncidence.Slot.orbit) :=
  ⟨PaidSourceFullOrbit.environmentAt root recognition visit successor transition alignment U7 calculus count (selectedPoint root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord),
    PaidSourceIncidence.programme root recognition visit successor transition alignment U7 calculus count queryWord⟩
def reader {current : V.Current} (_ : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :=
  raw root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord
abbrev result := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt root.toAuthoritativeRoot
  (reader root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord) (root.emitted visit.current)
abbrev current := RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value root.toAuthoritativeRoot visit.current
  (reader root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)
theorem source_value : current root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord=
    (PaidSourceFullOrbit.input root recognition visit successor transition alignment U7 calculus count).incidence queryWord (selectedPoint root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source _ _ _).trans
    (PaidSourceIncidence.programme_value root recognition visit successor transition alignment U7 calculus count queryWord (selectedPoint root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord))
theorem observed : (PaidSourceFullOrbit.input root recognition visit successor transition alignment U7 calculus count).coherentFace
    (current root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord) bound=
    Wave.effect root recognition visit successor transition alignment U7 calculus count bound queryWord (selectedPoint root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord) :=
  (congrArg (fun value => (PaidSourceFullOrbit.input root recognition visit successor transition alignment U7 calculus count).coherentFace value bound)
    (source_value root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)).trans
      (PaidSourceFullOrbit.exact_future root recognition visit successor transition alignment U7 calculus count bound queryWord (selectedPoint root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord))
theorem effect : SourceGeneratedCovarianceExecution.EffectPredicate
    (Future.observation root recognition visit successor transition alignment U7 calculus count bound) (Wave.action root recognition visit successor transition alignment U7 calculus count bound queryWord)
    (selected root recognition visit successor transition alignment U7 calculus count bound queryWord)
    ((PaidSourceFullOrbit.input root recognition visit successor transition alignment U7 calculus count).coherentFace (current root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord) bound) := by
  rw [observed]
  exact SourceGeneratedCovarianceExecution.source_effect_predicate _ _ _ _
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceIncidenceBranch
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
