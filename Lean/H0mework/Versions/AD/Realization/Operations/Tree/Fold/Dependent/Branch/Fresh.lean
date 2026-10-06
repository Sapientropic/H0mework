import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Branch.RichConsumer
import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Branch.Readback
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.Fresh
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
variable (packet : Side.Packet root recognition)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
abbrev current (count : Nat) := feed root recognition (actualSide root visit recognition U7 calculus count)
abbrev next (count : Nat) := feed root recognition (actualNextSide root visit recognition U7 calculus count)
theorem actual_feed (count : Nat) : current root recognition visit U7 calculus count =
    feed root recognition (outcome root visit recognition).2.2 := rfl
theorem next_feed (count : Nat) : next root recognition visit U7 calculus count =
    feed root recognition (nextOutcome root visit recognition).2.2 := rfl
theorem outcome_feed : (outcome root visit recognition).nativeFeed =
    feed root recognition (outcome root visit recognition).sides.2 := rfl

theorem next_outcome_feed : (nextOutcome root visit recognition).nativeFeed =
    feed root recognition (nextOutcome root visit recognition).sides.2 := rfl

abbrev Complete := Σ packet : Side.Packet root recognition, Feed root recognition packet

def Outcome.complete (output : Outcome root visit recognition) : Complete root recognition :=
  ⟨output.sides.2,output.nativeFeed⟩

theorem normal_inventory : Finsupp.mapDomain (Outcome.complete root recognition visit)
    (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value root.toAuthoritativeRoot visit.current
      (installedReader root visit recognition)).1 =
      Finsupp.single (Outcome.complete root recognition visit (outcome root visit recognition)) (1 : ℤ) := by
  rw [Branch.normal_inventory]
  exact Finsupp.mapDomain_single

theorem effect_inventory : Finsupp.mapDomain (Outcome.complete root recognition visit)
    (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value root.toAuthoritativeRoot visit.current
      (installedReader root visit recognition)).2 =
      Finsupp.single (Outcome.complete root recognition visit (nextOutcome root visit recognition)) (1 : ℤ) -
        Finsupp.single (Outcome.complete root recognition visit (outcome root visit recognition)) 1 := by
  rw [Branch.normal_inventory,Finsupp.mapDomain_sub,Finsupp.mapDomain_single,Finsupp.mapDomain_single]

variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
theorem next_code : (nextNode root visit recognition (node root visit recognition)).2 =
    SourceTemporalMaterial.encode root.toAuthoritativeRoot.toLedgerRoot (visit.next successor.next_eq) := by
  change (SourceTemporalMaterial.Action.nextCode root
    (SourceTemporalMaterial.encode root.toAuthoritativeRoot.toLedgerRoot visit)).getD _ = _
  have encoded := SourceTemporalMaterial.Action.nextCode_exact root
    (SourceTemporalMaterial.encode root.toAuthoritativeRoot.toLedgerRoot visit) successor.next_eq
  rw [encoded]
  exact SourceTemporalMaterial.encode_next root.toAuthoritativeRoot.toLedgerRoot visit successor.next_eq

private theorem visit_feed_heq
    (first second : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (same : first=second) :
    HEq (SourceOperationNative.Tree.Fold.Dependent.generatedFeed recognition first)
      (SourceOperationNative.Tree.Fold.Dependent.generatedFeed recognition second) := by
  cases same
  rfl

theorem fresh_next_feed (count : Nat) : HEq (next root recognition visit U7 calculus count)
    (SourceOperationNative.Tree.Fold.Dependent.generatedFeed recognition (visit.next successor.next_eq)) := by
  change HEq (feed root recognition (Side.packet root recognition
    (nextNode root visit recognition (node root visit recognition)).2)) _
  rw [next_code root recognition visit successor]
  have same : Side.visit root (Side.packet root recognition
      (SourceTemporalMaterial.encode root.toAuthoritativeRoot.toLedgerRoot (visit.next successor.next_eq))).1 =
        visit.next successor.next_eq := SourceTemporalMaterial.decode_encode _ _
  exact visit_feed_heq root recognition _ _ same

include U7 calculus in
theorem fresh_next_output (count : Nat) : HEq (nextOutcome root visit recognition).nativeFeed
    (SourceOperationNative.Tree.Fold.Dependent.generatedFeed recognition (visit.next successor.next_eq)) :=
  fresh_next_feed root recognition visit U7 calculus successor count

end SourceOperationNative.Tree.Fold.Dependent.Branch.Fresh
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
