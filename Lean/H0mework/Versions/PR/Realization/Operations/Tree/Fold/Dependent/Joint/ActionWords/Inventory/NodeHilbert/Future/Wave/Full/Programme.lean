import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Full.Kernel
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceFullOrbit
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


abbrev Value := PaidSourceOrbit.NativeOrbitProgramme.Value
  (I:=Model root recognition visit successor transition alignment U7 calculus count)
  (O:=FullCarrier root recognition visit successor transition alignment U7 calculus count)
abbrev Var := PaidSourceOrbit.NativeOrbitProgramme.Var
namespace Slot
export PaidSourceOrbit.NativeOrbitProgramme.Slot (model orbit)
end Slot
abbrev environmentAt := PaidSourceOrbit.NativeOrbitProgramme.environment
  (seed root recognition visit successor transition alignment U7 calculus count).toAddMonoidHom
abbrev programme (letters : List (Letter root recognition visit successor)) :=
  PaidSourceWordOrbit.NativeWordProgramme.programme (seed root recognition visit successor transition alignment U7 calculus count)
    (advance root recognition visit successor transition alignment U7 calculus count) letters
theorem programme_value (letters : List (Letter root recognition visit successor))
    (value : Model root recognition visit successor transition alignment U7 calculus count) :
    (programme root recognition visit successor transition alignment U7 calculus count letters).eval
      (environmentAt root recognition visit successor transition alignment U7 calculus count value)=
      SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) letters
        (seed root recognition visit successor transition alignment U7 calculus count value) := PaidSourceWordOrbit.NativeWordProgramme.programme_value _ _ letters value
theorem programme_budget (letters : List (Letter root recognition visit successor)) :
    remaining (programme root recognition visit successor transition alignment U7 calculus count letters)=letters.length+2 :=
  PaidSourceWordOrbit.NativeWordProgramme.programme_budget _ _ letters
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceFullOrbit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
