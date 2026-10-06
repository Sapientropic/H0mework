import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint
open SourceOperationEffects SourceOperationExecution
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
namespace T
export SourceTemporalMaterial.Action (Result actual receipt nextCode residualRaw materialRoot materialVisit)
end T
namespace D
export SourceOperationNative.Tree.Fold.Dependent (nativeTree nativeRaw nativeReader)
end D
namespace F
export SourceOperationNative.Tree.Fold (Value Var environment program program_value program_budget budget)
end F
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (successor : StepLedgerSuccessorAt (step root visit recognition))
variable (transition : GeneratedStepJointTransitionAt (step root visit recognition) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (step root visit recognition))
  (stepTargetPairingOccurrence (step root visit recognition) successor))
open RootInquiryCompletion SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceGeneratedScalarDifferentialResidual
theorem common_raw : (sourceOutcome root visit recognition successor transition alignment).2.2.1 =
    SourceHistoryCommon.Root.actualRaw root visit recognition successor := by
  unfold sourceOutcome
  cases tree root visit recognition successor transition alignment
  rfl

variable (U7' : U7ProducerCalculus N) (calculus' : U7ObstructionEvolutionCalculus N U7')
abbrev commonPacket (count : Nat) :=
  ((face root visit recognition successor transition alignment U7' calculus' count).rootRead.1.fold
    (constructor root visit recognition successor transition)).2.2.1
abbrev commonRead (count : Nat) :=
  CofinalHistorySettlement.RootGeneratedCofinalHistoryAt.generate
    (rootOccurrence:=RootedAccountedUnfolding.zero
      (commonPacket root visit recognition successor transition alignment U7' calculus' count).receipt.1)
    (seedOccurrence:=(commonPacket root visit recognition successor transition alignment U7' calculus' count).seed)
    (continuationOccurrence:=(commonPacket root visit recognition successor transition alignment U7' calculus' count).continuation)

theorem common_packet_generated (count : Nat) : commonPacket root visit recognition successor transition alignment U7' calculus' count =
    SourceHistoryCommon.Root.actualRaw root visit recognition successor :=
  common_raw root visit recognition successor transition alignment

theorem common_history_read (count : Nat) : HEq (commonRead root visit recognition successor transition alignment U7' calculus' count)
    (SourceHistoryCommon.Root.common root visit recognition successor) := by
  unfold commonRead
  rw [common_packet_generated]
  rfl
def commonLeft (count : Nat) : CofinalHistoryTransition.GeneratedTransition
    (SourceHistoryCommon.Root.sourceHistory root visit recognition)
    (commonRead root visit recognition successor transition alignment U7' calculus' count) := by
  unfold commonRead
  rw [common_packet_generated]
  exact SourceHistoryCommon.Root.left root visit recognition successor

def commonRight (count : Nat) : CofinalHistoryTransition.GeneratedTransition
    (SourceHistoryCommon.Root.targetHistory root visit recognition successor)
    (commonRead root visit recognition successor transition alignment U7' calculus' count) := by
  unfold commonRead
  rw [common_packet_generated]
  exact SourceHistoryCommon.Root.right root visit recognition successor

theorem common_source_read (count : Nat) : (commonPacket root visit recognition successor transition alignment U7' calculus' count).source =
    SourceHistoryCommon.Root.sourceRaw root visit recognition :=
  congrArg SourceHistoryCommon.Root.Raw.source (common_packet_generated root visit recognition successor transition alignment U7' calculus' count)

theorem common_target_read (count : Nat) : (commonPacket root visit recognition successor transition alignment U7' calculus' count).target =
    SourceHistoryCommon.Root.targetRaw root visit recognition successor :=
  congrArg SourceHistoryCommon.Root.Raw.target (common_packet_generated root visit recognition successor transition alignment U7' calculus' count)
theorem common_source_fibre (count : Nat)
    (word : (SourceHistoryCommon.Root.sourceHistory root visit recognition).generatorClosure) :
    CofinalHistoryTransition.GeneratedTransition.completionMap
      (SourceHistoryCommon.Root.sourceHistory root visit recognition)
      (commonRead root visit recognition successor transition alignment U7' calculus' count)
      (commonLeft root visit recognition successor transition alignment U7' calculus' count)
      ((SourceHistoryCommon.Root.sourceHistory root visit recognition).completionProjection word) = 0 ↔
        word.val ∈ (commonRead root visit recognition successor transition alignment U7' calculus' count).relationClosure := by
  exact SourceHistoryCommon.transition_fibre_zero _ _
    (commonLeft root visit recognition successor transition alignment U7' calculus' count) word

theorem common_target_fibre (count : Nat)
    (word : (SourceHistoryCommon.Root.targetHistory root visit recognition successor).generatorClosure) :
    CofinalHistoryTransition.GeneratedTransition.completionMap
      (SourceHistoryCommon.Root.targetHistory root visit recognition successor)
      (commonRead root visit recognition successor transition alignment U7' calculus' count)
      (commonRight root visit recognition successor transition alignment U7' calculus' count)
      ((SourceHistoryCommon.Root.targetHistory root visit recognition successor).completionProjection word) = 0 ↔
        word.val ∈ (commonRead root visit recognition successor transition alignment U7' calculus' count).relationClosure := by
  exact SourceHistoryCommon.transition_fibre_zero _ _
    (commonRight root visit recognition successor transition alignment U7' calculus' count) word
end SourceOperationNative.Tree.Fold.Dependent.Joint
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
