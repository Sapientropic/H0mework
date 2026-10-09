import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Origin.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Selected
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage : Nat)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current
 (frameAt root visit recognition U7 calculus anchor sourceStage stage).registered}
variable (supplied : Dynamic.C.Occurrence (frameAt root visit recognition U7 calculus anchor sourceStage stage) (current:=current))
theorem current_word : Dynamic.actorWordAt root visit recognition
 (frameAt root visit recognition U7 calculus anchor sourceStage stage) supplied=
 Finsupp.single (nextActorAt root visit recognition U7 calculus anchor sourceStage stage) 1 := by
 have result := Dynamic.actor_word_of_origin root visit recognition
  (frameAt root visit recognition U7 calculus anchor sourceStage stage)
  (Dynamic.currentRead root visit recognition (frameAt root visit recognition U7 calculus anchor sourceStage stage)) supplied
  (birthCount root visit recognition U7 calculus anchor sourceStage stage)
  (Origin.uniform_origin root visit recognition U7 calculus anchor sourceStage stage current supplied)
 change _=Finsupp.single (Dynamic.actorAtCount root visit recognition
  (birthCount root visit recognition U7 calculus anchor sourceStage stage+1)) 1 at result
 simpa only [nextActorAt,nodeAt,Dynamic.actorAtCount,Function.iterate_succ_apply'] using result
theorem current_support : Dynamic.supportAt root visit recognition
 (frameAt root visit recognition U7 calculus anchor sourceStage stage) supplied=
 [nextActorAt root visit recognition U7 calculus anchor sourceStage stage] := by
 classical
 change (Dynamic.actorWordAt root visit recognition
  (frameAt root visit recognition U7 calculus anchor sourceStage stage) supplied).support.toList=_
 rw [current_word]
 simp
theorem current_catalogue : Dynamic.indicesFor root visit recognition
 (frameAt root visit recognition U7 calculus anchor sourceStage stage)
 (Dynamic.currentRead root visit recognition (frameAt root visit recognition U7 calculus anchor sourceStage stage)) supplied=
 CurrentChild.indices root recognition (nextActorAt root visit recognition U7 calculus anchor sourceStage stage) := by
 change (Dynamic.supportAt root visit recognition
  (frameAt root visit recognition U7 calculus anchor sourceStage stage) supplied).flatMap (CurrentChild.indices root recognition)=_
 rw [current_support]
 simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
theorem next_word : Dynamic.actorWordFor root visit recognition
 (frameAt root visit recognition U7 calculus anchor sourceStage stage)
 (Dynamic.nextRead root visit recognition (frameAt root visit recognition U7 calculus anchor sourceStage stage)) supplied=
 Finsupp.single (Dynamic.actorAtCount root visit recognition
  (birthCount root visit recognition U7 calculus anchor sourceStage stage+2)) 1 := by
 apply Dynamic.actor_word_of_origin root visit recognition
  (frameAt root visit recognition U7 calculus anchor sourceStage stage)
  (Dynamic.nextRead root visit recognition (frameAt root visit recognition U7 calculus anchor sourceStage stage)) supplied
  (birthCount root visit recognition U7 calculus anchor sourceStage stage+1)
 intro datum
 have shift : Dynamic.generatedEnvironmentAt root visit recognition
   (frameAt root visit recognition U7 calculus anchor sourceStage stage) supplied
   (Origin.coreSlot root recognition) (datum,.old) (0:Fin 2)=
   Dynamic.environmentAt root visit recognition
    (frameAt root visit recognition U7 calculus anchor sourceStage stage) supplied
    (Origin.coreSlot root recognition) (Branch.nextNode root visit recognition datum,.old) (0:Fin 2) := rfl
 apply shift.trans
 apply (Origin.uniform_origin root visit recognition U7 calculus anchor sourceStage stage current supplied
  (Branch.nextNode root visit recognition datum)).trans
 unfold Origin.pairAt Dynamic.orbitPair
 rw [←Function.iterate_succ_apply,←Function.iterate_succ_apply]
theorem next_support : Dynamic.supportFor root visit recognition
 (frameAt root visit recognition U7 calculus anchor sourceStage stage)
 (Dynamic.nextRead root visit recognition (frameAt root visit recognition U7 calculus anchor sourceStage stage)) supplied=
 [Dynamic.actorAtCount root visit recognition (birthCount root visit recognition U7 calculus anchor sourceStage stage+2)] := by
 classical
 unfold Dynamic.supportFor
 rw [next_word]
 simp
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Selected
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
