import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Epoch.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Main.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Children.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Selected.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Observed.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Action.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Physical
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationScalarInventoryLift
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage : Nat)
abbrev actualFrame := E.epoch (frameAt root visit recognition U7 calculus anchor sourceStage stage)
abbrev actualSource := Dynamic.actorAtCount root visit recognition
 (birthCount root visit recognition U7 calculus anchor sourceStage stage+1)
abbrev actualOccurrence := E.Shared.actualOccurrence (frameAt root visit recognition U7 calculus anchor sourceStage stage)
abbrev actualRead : Dynamic.Read root visit recognition (actualFrame root visit recognition U7 calculus anchor sourceStage stage) :=
 Dynamic.currentRead root visit recognition (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
local instance : AddCommGroup (CurrentChild.Value root visit recognition (CurrentChild.resultSlot root recognition)) :=
 CurrentChild.instAddCommGroupValue root visit recognition (CurrentChild.resultSlot root recognition)
abbrev mainResult := Main.actualResult root visit recognition U7 calculus anchor
 (frameAt root visit recognition U7 calculus anchor sourceStage stage)
 (sourceSeed root visit recognition U7 calculus anchor sourceStage)
 (E.Shared.actualOccurrence (frameAt root visit recognition U7 calculus anchor sourceStage stage))
abbrev recovered := Main.recoveredAt root visit recognition U7 calculus anchor
 (frameAt root visit recognition U7 calculus anchor sourceStage stage)
 (sourceSeed root visit recognition U7 calculus anchor sourceStage)
 (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage)
private theorem recovered_current : (recovered root visit recognition U7 calculus anchor sourceStage stage).1=
 (Dynamic.paidAt root visit recognition U7 calculus anchor
  (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
  (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage)).2.2.1 :=
 Main.recovered_current root visit recognition U7 calculus anchor _ _ _
private theorem child_from_paid {X : Type u} (value : X → CurrentChild.Output root visit recognition) (x : X)
 (frame : Dynamic.Frame root visit recognition) (read : Dynamic.Read root visit recognition frame)
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : Dynamic.C.Occurrence frame (current:=current))
 (source : CurrentChild.SourceActor root recognition)
 (sourceSupport : Dynamic.supportFor root visit recognition frame read supplied=[source])
 (same : value x=(Dynamic.paidFor root visit recognition U7 calculus anchor frame read supplied).2.2.1) :
 (value x).1=
 (Observer.Action.observerSyntax root visit recognition U7 calculus anchor).eval
  (Dynamic.Children.baseEnvironment root visit recognition frame read supplied) +
 Observer.oldInjection root visit recognition
  ((Inventory.childExpressionAtCode root visit recognition source.1.1).eval
   (Dynamic.Children.childEnvironment root visit recognition frame read supplied)) := by
 have result := (congrArg (fun output : CurrentChild.Output root visit recognition => output.1) same).trans
  (Dynamic.Children.paid_old_output root visit recognition U7 calculus anchor frame read supplied)
 rw [sourceSupport,List.map_singleton,List.sum_singleton] at result
 exact result
private theorem observation_from_paid {X : Type u} (value : X → CurrentChild.Output root visit recognition) (x : X)
 (frame : Dynamic.Frame root visit recognition) (read : Dynamic.Read root visit recognition frame)
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : Dynamic.C.Occurrence frame (current:=current))
 (source : CurrentChild.SourceActor root recognition)
 (sourceSupport : Dynamic.supportFor root visit recognition frame read supplied=[source])
 (same : value x=(Dynamic.paidFor root visit recognition U7 calculus anchor frame read supplied).2.2.1)
 (position : Fin (CurrentChild.rowsAtActor root recognition source).length) (kind : Fin 4) :
 (value x).2.2.1 ⟨source,position⟩ kind=
 Dynamic.Observed.observationValueAt root visit recognition frame read supplied ⟨source,position⟩ kind :=
 (congrArg (fun output : CurrentChild.Output root visit recognition => output.2.2.1 ⟨source,position⟩ kind) same).trans
 (Dynamic.Observed.paid_observation_of_support root visit recognition U7 calculus anchor frame read supplied source sourceSupport position kind)
private theorem gram_from_paid {X : Type u} (value : X → CurrentChild.Output root visit recognition) (x : X)
 (frame : Dynamic.Frame root visit recognition) (read : Dynamic.Read root visit recognition frame)
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : Dynamic.C.Occurrence frame (current:=current))
 (source : CurrentChild.SourceActor root recognition)
 (sourceSupport : Dynamic.supportFor root visit recognition frame read supplied=[source])
 (same : value x=(Dynamic.paidFor root visit recognition U7 calculus anchor frame read supplied).2.2.1)
 (first second : Fin (CurrentChild.rowsAtActor root recognition source).length × Fin 4) :
 ((value x).2.2.2 (⟨source,first.1⟩,first.2) (⟨source,second.1⟩,second.2)).down=
 inner ℂ (Dynamic.Observed.observationValueAt root visit recognition frame read supplied ⟨source,first.1⟩ first.2)
  (Dynamic.Observed.observationValueAt root visit recognition frame read supplied ⟨source,second.1⟩ second.2) :=
 (congrArg (fun output : CurrentChild.Output root visit recognition =>
  (output.2.2.2 (⟨source,first.1⟩,first.2) (⟨source,second.1⟩,second.2)).down) same).trans
 (Dynamic.Observed.paid_gram_of_support root visit recognition U7 calculus anchor frame read supplied source sourceSupport first second)
theorem current_child : type_of% (
 child_from_paid root visit recognition U7 calculus anchor
  (fun _ : PUnit => (recovered root visit recognition U7 calculus anchor sourceStage stage).1) PUnit.unit
  (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
  (actualRead root visit recognition U7 calculus anchor sourceStage stage)
  (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage)
  (actualSource root visit recognition U7 calculus anchor sourceStage stage)
  (Epoch.current_support root visit recognition (frameAt root visit recognition U7 calculus anchor sourceStage stage) (birthCount root visit recognition U7 calculus anchor sourceStage stage) (Origin.uniform_origin root visit recognition U7 calculus anchor sourceStage stage) (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage))
  (recovered_current root visit recognition U7 calculus anchor sourceStage stage)) :=
 child_from_paid root visit recognition U7 calculus anchor
  (fun _ : PUnit => (recovered root visit recognition U7 calculus anchor sourceStage stage).1) PUnit.unit
  (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
  (actualRead root visit recognition U7 calculus anchor sourceStage stage)
  (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage)
  (actualSource root visit recognition U7 calculus anchor sourceStage stage)
  (Epoch.current_support root visit recognition (frameAt root visit recognition U7 calculus anchor sourceStage stage) (birthCount root visit recognition U7 calculus anchor sourceStage stage) (Origin.uniform_origin root visit recognition U7 calculus anchor sourceStage stage) (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage))
  (recovered_current root visit recognition U7 calculus anchor sourceStage stage)
theorem current_observation
 (position : Fin (CurrentChild.rowsAtActor root recognition (actualSource root visit recognition U7 calculus anchor sourceStage stage)).length) (kind : Fin 4) : type_of% (
 observation_from_paid root visit recognition U7 calculus anchor
  (fun _ : PUnit => (recovered root visit recognition U7 calculus anchor sourceStage stage).1) PUnit.unit
  (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
  (actualRead root visit recognition U7 calculus anchor sourceStage stage)
  (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage)
  (actualSource root visit recognition U7 calculus anchor sourceStage stage)
  (Epoch.current_support root visit recognition (frameAt root visit recognition U7 calculus anchor sourceStage stage) (birthCount root visit recognition U7 calculus anchor sourceStage stage) (Origin.uniform_origin root visit recognition U7 calculus anchor sourceStage stage) (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage))
  (recovered_current root visit recognition U7 calculus anchor sourceStage stage) position kind) :=
 observation_from_paid root visit recognition U7 calculus anchor
  (fun _ : PUnit => (recovered root visit recognition U7 calculus anchor sourceStage stage).1) PUnit.unit
  (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
  (actualRead root visit recognition U7 calculus anchor sourceStage stage)
  (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage)
  (actualSource root visit recognition U7 calculus anchor sourceStage stage)
  (Epoch.current_support root visit recognition (frameAt root visit recognition U7 calculus anchor sourceStage stage) (birthCount root visit recognition U7 calculus anchor sourceStage stage) (Origin.uniform_origin root visit recognition U7 calculus anchor sourceStage stage) (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage))
  (recovered_current root visit recognition U7 calculus anchor sourceStage stage) position kind
theorem current_gram
 (first second : Fin (CurrentChild.rowsAtActor root recognition (actualSource root visit recognition U7 calculus anchor sourceStage stage)).length × Fin 4) : type_of% (
 gram_from_paid root visit recognition U7 calculus anchor
  (fun _ : PUnit => (recovered root visit recognition U7 calculus anchor sourceStage stage).1) PUnit.unit
  (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
  (actualRead root visit recognition U7 calculus anchor sourceStage stage)
  (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage)
  (actualSource root visit recognition U7 calculus anchor sourceStage stage)
  (Epoch.current_support root visit recognition (frameAt root visit recognition U7 calculus anchor sourceStage stage) (birthCount root visit recognition U7 calculus anchor sourceStage stage) (Origin.uniform_origin root visit recognition U7 calculus anchor sourceStage stage) (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage))
  (recovered_current root visit recognition U7 calculus anchor sourceStage stage) first second) :=
 gram_from_paid root visit recognition U7 calculus anchor
  (fun _ : PUnit => (recovered root visit recognition U7 calculus anchor sourceStage stage).1) PUnit.unit
  (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
  (actualRead root visit recognition U7 calculus anchor sourceStage stage)
  (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage)
  (actualSource root visit recognition U7 calculus anchor sourceStage stage)
  (Epoch.current_support root visit recognition (frameAt root visit recognition U7 calculus anchor sourceStage stage) (birthCount root visit recognition U7 calculus anchor sourceStage stage) (Origin.uniform_origin root visit recognition U7 calculus anchor sourceStage stage) (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage))
  (recovered_current root visit recognition U7 calculus anchor sourceStage stage) first second
abbrev followingSource := Dynamic.actorAtCount root visit recognition
 (birthCount root visit recognition U7 calculus anchor sourceStage stage+2)
abbrev followingRead : Dynamic.Read root visit recognition (actualFrame root visit recognition U7 calculus anchor sourceStage stage) :=
 Dynamic.nextRead root visit recognition (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
abbrev followingPaid := Dynamic.Action.paidAt root visit recognition U7 calculus anchor
 (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
 (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage)
theorem next_child : type_of% (
 child_from_paid root visit recognition U7 calculus anchor
  (fun _ : PUnit => (followingPaid root visit recognition U7 calculus anchor sourceStage stage).2.2.1) PUnit.unit
  (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
  (followingRead root visit recognition U7 calculus anchor sourceStage stage)
  (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage)
  (followingSource root visit recognition U7 calculus anchor sourceStage stage)
  (Epoch.next_support root visit recognition (frameAt root visit recognition U7 calculus anchor sourceStage stage) (birthCount root visit recognition U7 calculus anchor sourceStage stage) (Origin.uniform_origin root visit recognition U7 calculus anchor sourceStage stage) (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage))
  (Dynamic.Action.paid_value_at root visit recognition U7 calculus anchor _ _)) :=
 child_from_paid root visit recognition U7 calculus anchor
  (fun _ : PUnit => (followingPaid root visit recognition U7 calculus anchor sourceStage stage).2.2.1) PUnit.unit
  (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
  (followingRead root visit recognition U7 calculus anchor sourceStage stage)
  (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage)
  (followingSource root visit recognition U7 calculus anchor sourceStage stage)
  (Epoch.next_support root visit recognition (frameAt root visit recognition U7 calculus anchor sourceStage stage) (birthCount root visit recognition U7 calculus anchor sourceStage stage) (Origin.uniform_origin root visit recognition U7 calculus anchor sourceStage stage) (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage))
  (Dynamic.Action.paid_value_at root visit recognition U7 calculus anchor _ _)
theorem next_observation
 (position : Fin (CurrentChild.rowsAtActor root recognition (followingSource root visit recognition U7 calculus anchor sourceStage stage)).length) (kind : Fin 4) : type_of% (
 observation_from_paid root visit recognition U7 calculus anchor
  (fun _ : PUnit => (followingPaid root visit recognition U7 calculus anchor sourceStage stage).2.2.1) PUnit.unit
  (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
  (followingRead root visit recognition U7 calculus anchor sourceStage stage)
  (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage)
  (followingSource root visit recognition U7 calculus anchor sourceStage stage)
  (Epoch.next_support root visit recognition (frameAt root visit recognition U7 calculus anchor sourceStage stage) (birthCount root visit recognition U7 calculus anchor sourceStage stage) (Origin.uniform_origin root visit recognition U7 calculus anchor sourceStage stage) (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage))
  (Dynamic.Action.paid_value_at root visit recognition U7 calculus anchor _ _) position kind) :=
 observation_from_paid root visit recognition U7 calculus anchor
  (fun _ : PUnit => (followingPaid root visit recognition U7 calculus anchor sourceStage stage).2.2.1) PUnit.unit
  (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
  (followingRead root visit recognition U7 calculus anchor sourceStage stage)
  (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage)
  (followingSource root visit recognition U7 calculus anchor sourceStage stage)
  (Epoch.next_support root visit recognition (frameAt root visit recognition U7 calculus anchor sourceStage stage) (birthCount root visit recognition U7 calculus anchor sourceStage stage) (Origin.uniform_origin root visit recognition U7 calculus anchor sourceStage stage) (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage))
  (Dynamic.Action.paid_value_at root visit recognition U7 calculus anchor _ _) position kind
theorem next_gram
 (first second : Fin (CurrentChild.rowsAtActor root recognition (followingSource root visit recognition U7 calculus anchor sourceStage stage)).length × Fin 4) : type_of% (
 gram_from_paid root visit recognition U7 calculus anchor
  (fun _ : PUnit => (followingPaid root visit recognition U7 calculus anchor sourceStage stage).2.2.1) PUnit.unit
  (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
  (followingRead root visit recognition U7 calculus anchor sourceStage stage)
  (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage)
  (followingSource root visit recognition U7 calculus anchor sourceStage stage)
  (Epoch.next_support root visit recognition (frameAt root visit recognition U7 calculus anchor sourceStage stage) (birthCount root visit recognition U7 calculus anchor sourceStage stage) (Origin.uniform_origin root visit recognition U7 calculus anchor sourceStage stage) (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage))
  (Dynamic.Action.paid_value_at root visit recognition U7 calculus anchor _ _) first second) :=
 gram_from_paid root visit recognition U7 calculus anchor
  (fun _ : PUnit => (followingPaid root visit recognition U7 calculus anchor sourceStage stage).2.2.1) PUnit.unit
  (actualFrame root visit recognition U7 calculus anchor sourceStage stage)
  (followingRead root visit recognition U7 calculus anchor sourceStage stage)
  (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage)
  (followingSource root visit recognition U7 calculus anchor sourceStage stage)
  (Epoch.next_support root visit recognition (frameAt root visit recognition U7 calculus anchor sourceStage stage) (birthCount root visit recognition U7 calculus anchor sourceStage stage) (Origin.uniform_origin root visit recognition U7 calculus anchor sourceStage stage) (actualOccurrence root visit recognition U7 calculus anchor sourceStage stage))
  (Dynamic.Action.paid_value_at root visit recognition U7 calculus anchor _ _) first second
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Physical
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
