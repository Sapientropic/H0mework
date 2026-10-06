import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Next.Pursuit
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Next.Pursuit
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
variable (oldWord : Tr.TargetWord root visit recognition successor)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
variable (nextSuccessor : StepLedgerSuccessorAt (nextStep root visit recognition successor))
variable (transition : GeneratedStepJointTransitionAt (nextStep root visit recognition successor) nextSuccessor)
variable (node : GeneratedNodeAt (nextStep root visit recognition successor) nextSuccessor transition.history)
variable (targetWord : Tr.TargetWord root (nextVisit root visit recognition successor) recognition nextSuccessor)
namespace C
export SourceOperationNative.Tree.Fold.Dependent.Joint.Transport (targetMaterialFace target_source_word_read target_programme_cost target_query_answer_next target_whole_next target_normal_inverse)
end C

theorem actual_source_word (count : Nat) :
    (C.targetMaterialFace root (nextVisit root visit recognition successor) recognition nextSuccessor transition node
      (Material.generatedNextWord root visit recognition successor oldWord) targetWord U7 calculus count).rootRead.2.1.val = oldWord.val :=
  (congrArg Subtype.val (C.target_source_word_read root (nextVisit root visit recognition successor) recognition nextSuccessor transition node
    (Material.generatedNextWord root visit recognition successor oldWord) targetWord U7 calculus count)).trans
      (Material.generated_next_word_value root visit recognition successor oldWord)

theorem cost : type_of% (C.target_programme_cost root (nextVisit root visit recognition successor) recognition nextSuccessor transition node
    (Material.generatedNextWord root visit recognition successor oldWord) targetWord) :=
  C.target_programme_cost root (nextVisit root visit recognition successor) recognition nextSuccessor transition node
    (Material.generatedNextWord root visit recognition successor oldWord) targetWord

theorem whole_next (count : Nat) : type_of% (C.target_whole_next root (nextVisit root visit recognition successor) recognition nextSuccessor transition node
    (Material.generatedNextWord root visit recognition successor oldWord) targetWord count) :=
  C.target_whole_next root (nextVisit root visit recognition successor) recognition nextSuccessor transition node
    (Material.generatedNextWord root visit recognition successor oldWord) targetWord count

theorem query_answer_next (count : Nat) : type_of% (C.target_query_answer_next root (nextVisit root visit recognition successor) recognition nextSuccessor transition node
    (Material.generatedNextWord root visit recognition successor oldWord) targetWord U7 calculus count) :=
  C.target_query_answer_next root (nextVisit root visit recognition successor) recognition nextSuccessor transition node
    (Material.generatedNextWord root visit recognition successor oldWord) targetWord U7 calculus count

theorem inverse_read : type_of% (C.target_normal_inverse root (nextVisit root visit recognition successor) recognition nextSuccessor transition node
    (Material.generatedNextWord root visit recognition successor oldWord) targetWord) :=
  C.target_normal_inverse root (nextVisit root visit recognition successor) recognition nextSuccessor transition node
    (Material.generatedNextWord root visit recognition successor oldWord) targetWord

theorem tree_preserved (generatedTree : RootedAccountedUnfolding (GeneratedNodeAt (nextStep root visit recognition successor) nextSuccessor transition.history)) :
    (eliminate root visit recognition successor oldWord U7 calculus nextSuccessor transition (.inl generatedTree)).down.map Sigma.fst = generatedTree := by
  change (generatedTree.map (nodeFollow root visit recognition successor oldWord U7 calculus nextSuccessor transition)).map Sigma.fst = _
  rw [RootedAccountedUnfolding.map_map]
  exact RootedAccountedUnfolding.map_id _

theorem residual_preserved (coordinate : ExactResidualAt (nextStep root visit recognition successor) nextSuccessor transition.history) :
    (eliminate root visit recognition successor oldWord U7 calculus nextSuccessor transition (.inr coordinate)).down = coordinate := rfl
end SourceOperationNative.Tree.Fold.Dependent.Next.Pursuit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
