import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Relations.Source
import H0mework.Realization.Operations.Substitution.Complex
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


open CategoryTheory SourceOperationScalarPresentation SourceOperationScalarRelations
variable (letter : Letter root recognition visit successor) (slot : PaidSourceOrbit.NativeOrbitProgramme.Slot.{u})
variable (value : PaidSourceFullOrbit.FullCarrier root recognition visit successor transition alignment U7 calculus count)
def actualComplex : presentationComplex (R:=ℤ) (s:=slot)
    (PaidSourceIncidenceBranch.orbitEnvironment root recognition visit successor transition alignment U7 calculus count (PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count letter value)) ⟶
    presentationComplex (R:=ℤ) (s:=slot) (PaidSourceIncidenceBranch.orbitEnvironment root recognition visit successor transition alignment U7 calculus count value) where
 τ₁ := ModuleCat.ofHom (relationWords root recognition visit successor transition alignment U7 calculus count letter slot value)
 τ₂ := ModuleCat.ofHom (words root recognition visit successor transition alignment U7 calculus count letter slot)
 τ₃ := 𝟙 _
 comm₁₂ := by
   apply ModuleCat.hom_ext
   exact relation_square root recognition visit successor transition alignment U7 calculus count letter slot value
 comm₂₃ := by
   apply ModuleCat.hom_ext
   change (evaluation (R:=ℤ) (s:=slot) (PaidSourceIncidenceBranch.orbitEnvironment root recognition visit successor transition alignment U7 calculus count value)).comp
     (words root recognition visit successor transition alignment U7 calculus count letter slot)=evaluation (R:=ℤ) (s:=slot)
       (PaidSourceIncidenceBranch.orbitEnvironment root recognition visit successor transition alignment U7 calculus count (PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count letter value))
   have square := evaluation_substitution (R:=ℤ) (s:=slot) (binding root recognition visit successor transition alignment U7 calculus count letter)
     (PaidSourceIncidenceBranch.orbitEnvironment root recognition visit successor transition alignment U7 calculus count value)
   exact square.trans (congrArg (evaluation (R:=ℤ) (s:=slot))
     (environment_source root recognition visit successor transition alignment U7 calculus count letter value))
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceIncidenceRelations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
