import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Source

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Origin
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage : Nat)
abbrev coreSlot : CurrentChild.Slot root recognition := .inl (CurrentActor.coreSlot root recognition)
def pairAt (count : Nat) (datum : Branch.Node root visit recognition) :=
 (Finsupp.single ((Branch.nextNode root visit recognition)^[count] datum) (1:ℤ),
  Finsupp.single ((Branch.nextNode root visit recognition)^[count+1] datum) (1:ℤ) -
   Finsupp.single ((Branch.nextNode root visit recognition)^[count] datum) (1:ℤ))
def UniformAt (frame : Dynamic.Frame root visit recognition) (count : Nat) : Prop :=
 ∀ (current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered)
 (supplied : Dynamic.C.Occurrence frame (current:=current)) (datum : Branch.Node root visit recognition),
 Dynamic.environmentAt root visit recognition frame supplied (coreSlot root recognition) (datum,.old) (0:Fin 2)=
 pairAt root visit recognition count datum
theorem uniform_origin (stage : Nat) : UniformAt root visit recognition
 (frameAt root visit recognition U7 calculus anchor sourceStage stage)
 (birthCount root visit recognition U7 calculus anchor sourceStage stage) := by
 induction stage with
 | zero =>
   intro current supplied datum
   change Observer.Action.environmentAt root visit recognition
    (Observer.Live.frameAt root visit recognition U7 calculus anchor sourceStage)
    (Observer.Live.E.Shared.actualOccurrence (Observer.Live.frameAt root visit recognition U7 calculus anchor sourceStage))
    (CurrentActor.coreSlot root recognition) (datum,.old) (0:Fin 2)=_
   exact CurrentActor.uniform_origin root visit recognition U7 calculus anchor sourceStage _ _ datum
 | succ stage previous =>
   change UniformAt root visit recognition
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
     (frameAt root visit recognition U7 calculus anchor sourceStage stage)
     (programme root visit recognition U7 calculus anchor sourceStage))
    (match (frameAt root visit recognition U7 calculus anchor sourceStage stage).action with
     | .inr _ => birthCount root visit recognition U7 calculus anchor sourceStage stage
     | .inl _ => birthCount root visit recognition U7 calculus anchor sourceStage stage+1)
   unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
   cases (frameAt root visit recognition U7 calculus anchor sourceStage stage).action with
   | inr paid => exact previous
   | inl settled =>
     intro current supplied datum
     change Dynamic.generatedEnvironmentAt root visit recognition
      (E.epoch (frameAt root visit recognition U7 calculus anchor sourceStage stage))
      (E.Shared.actualOccurrence (frameAt root visit recognition U7 calculus anchor sourceStage stage))
      (coreSlot root recognition) (datum,.old) (0:Fin 2)=_
     have shift : Dynamic.generatedEnvironmentAt root visit recognition
       (E.epoch (frameAt root visit recognition U7 calculus anchor sourceStage stage))
       (E.Shared.actualOccurrence (frameAt root visit recognition U7 calculus anchor sourceStage stage))
       (coreSlot root recognition) (datum,.old) (0:Fin 2)=
       Dynamic.environmentAt root visit recognition
        (E.epoch (frameAt root visit recognition U7 calculus anchor sourceStage stage))
        (E.Shared.actualOccurrence (frameAt root visit recognition U7 calculus anchor sourceStage stage))
        (coreSlot root recognition) (Branch.nextNode root visit recognition datum,.old) (0:Fin 2) := rfl
     apply shift.trans
     apply (previous _ (E.Shared.actualOccurrence (frameAt root visit recognition U7 calculus anchor sourceStage stage))
      (Branch.nextNode root visit recognition datum)).trans
     unfold pairAt
     rw [←Function.iterate_succ_apply,←Function.iterate_succ_apply]
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Origin
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
