import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Branch.SideOutput
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
namespace D
export SourceOperationNative.Tree.Fold.Dependent (FeedAt sourceFeed)
end D
namespace F
export SourceOperationNative.Tree.Fold (Value Var environment program program_value program_budget)
end F
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
open RootInquiryCompletion
theorem old_side_generated : (outcome root visit recognition).2.2 = Side.packet root recognition
    (SourceTemporalMaterial.encode root.toAuthoritativeRoot.toLedgerRoot visit) := rfl

theorem next_side_generated : (nextOutcome root visit recognition).2.2 = Side.packet root recognition
    (nextNode root visit recognition (node root visit recognition)).2 := rfl

variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
abbrev actualSide (count : Nat) : Side.Packet root recognition :=
  (face root visit recognition U7 calculus count).rootRead.2.2.1
abbrev actualNextSide (count : Nat) : Side.Packet root recognition :=
  (face root visit recognition U7 calculus count).rootRead.2.2.2

theorem actual_side_generated (count : Nat) : actualSide root visit recognition U7 calculus count =
    (outcome root visit recognition).2.2 := rfl

theorem actual_next_side_generated (count : Nat) : actualNextSide root visit recognition U7 calculus count =
    (nextOutcome root visit recognition).2.2 := rfl

abbrev actualSideOutput (count : Nat) := Side.packetOutput root recognition (actualSide root visit recognition U7 calculus count)
abbrev actualNextSideOutput (count : Nat) := Side.packetOutput root recognition (actualNextSide root visit recognition U7 calculus count)

abbrev completeRuntime := (runtime root visit recognition U7 calculus,
  actualSideOutput root visit recognition U7 calculus 0,actualNextSideOutput root visit recognition U7 calculus 0)
end SourceOperationNative.Tree.Fold.Dependent.Branch
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
