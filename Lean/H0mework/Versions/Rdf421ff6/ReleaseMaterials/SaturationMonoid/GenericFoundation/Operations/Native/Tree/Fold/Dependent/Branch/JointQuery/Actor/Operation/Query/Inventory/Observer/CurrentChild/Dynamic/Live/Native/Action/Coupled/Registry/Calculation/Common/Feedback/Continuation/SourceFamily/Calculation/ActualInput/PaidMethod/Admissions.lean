import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.PaidMethod.Recovery
import H0mework.Versions.Rdf421ff6.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Runtime
import H0mework.Versions.Rdf421ff6.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Factory
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.EnvironmentUpdate.CurrentMaterial.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation.PaidMethod.Admissions
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace D
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
 (packetAt packetAt_successor packetAt_successor_grade actual_index historyAt index history_end_index distance strictMono complete_word actual_source_action)
end D
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (admissionPresentation)
end AS
namespace Origin
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Activated (frameAt cfg)
end Origin
namespace Owner
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Foresight.Contextual (factory)
end Owner
namespace Binding
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action (lowBinding)
end Binding
namespace Current
export SourceFamilyActualCurrentMaterialEnvironmentUpdate (queryFactory)
end Current
namespace Act
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action
 (LowValue LowVar sort)
end Act

namespace Generic
variable {process : SourceNativeInquiryEngineProcess.{u}}
theorem field_segment (runtime : SourceNativeInquiryRuntime process) (start fuel : Nat) :
 (fun value : SourceOperationInquiry.Field runtime => SourceOperationInquiry.fieldAction runtime value)^[fuel]
  (SourceOperationInquiry.fieldPoint runtime ((runtime).stateAt start)) =
 SourceOperationInquiry.fieldPoint runtime ((runtime).stateAt (start+fuel)) := by
 induction fuel with
 | zero => simp only [Function.iterate_zero, Nat.add_zero, id_eq]
 | succ fuel previous =>
  rw [Function.iterate_succ_apply', previous]
  simpa only [Nat.add_assoc] using SourceOperationInquiry.actual_field_action runtime (start+fuel)
end Generic

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance sourceGroups (t) : AddCommGroup (Act.LowValue root visit rec t) := inferInstance
local instance familyGroups (n : Nat) (t) : AddCommGroup (L.Value (Act.LowValue root visit rec) n t) :=
 L.groups (Act.LowValue root visit rec) n t
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
variable (anchor sourceStage stage count : Nat)
abbrev Operator : Type _ := by
 letI := sourceGroups root visit rec (Act.sort root rec)
 exact (Act.LowValue root visit rec (Act.sort root rec) →+ Act.LowValue root visit rec (Act.sort root rec))
variable (f : Operator root visit rec)

-- All authority inputs are recovered from the existing installed owner.
abbrev originalFrame := Origin.frameAt root visit rec U7 calculus anchor sourceStage stage count
abbrev originalProgramme := Faces.configuration (Origin.cfg root visit rec U7 calculus anchor sourceStage stage)
theorem originalLanguage : (originalProgramme root visit rec U7 calculus anchor sourceStage stage).LowVar = Act.LowVar root visit rec := rfl
abbrev baseFactory := Current.queryFactory (Owner.factory (s := Act.sort root rec) (Binding.lowBinding root visit rec))
def queryFactory := factory (baseFactory root visit rec) f
def sourceRuntime := SF.runtime (queryFactory root visit rec f)
 (originalFrame root visit rec U7 calculus anchor sourceStage stage count)
 (originalProgramme root visit rec U7 calculus anchor sourceStage stage)
 (originalLanguage root visit rec U7 calculus anchor sourceStage stage)

abbrev actualPacket (k : Nat) := D.packetAt (queryFactory root visit rec f)
 (originalFrame root visit rec U7 calculus anchor sourceStage stage count)
 (originalProgramme root visit rec U7 calculus anchor sourceStage stage)
 (originalLanguage root visit rec U7 calculus anchor sourceStage stage) k

local notation "method" => queryFactory root visit rec f
local notation "initial" => originalFrame root visit rec U7 calculus anchor sourceStage stage count
local notation "cfg" => originalProgramme root visit rec U7 calculus anchor sourceStage stage
local notation "language" => originalLanguage root visit rec U7 calculus anchor sourceStage stage
local notation "packet" => actualPacket root visit rec U7 calculus anchor sourceStage stage count f
local notation "runtime" => sourceRuntime root visit rec U7 calculus anchor sourceStage stage count f

def PaidFeed
 (current next : AS.AdmissionPacket (W := Act.LowValue root visit rec)
  (X := Act.LowVar root visit rec) (s := Act.sort root rec)) : Prop :=
 HEq (retainedValue next)
  (R.actionResultAt current.2.1.1 current.2.2.1 (S.actualOccurrence current.2.1.1)).2.2.1

theorem actual_paid_recovery (k : Nat) : PaidFeed root visit rec (packet k) (packet (k+1)) := by
 exact (congrArg (fun next => PaidFeed root visit rec (packet k) next)
  (D.packetAt_successor method initial cfg language k)).mpr
  (after_native_value method (packet k))

theorem actual_method_step (k : Nat) : WholeStep f (packet k) (packet (k+1)) := by
 exact (congrArg (fun next => WholeStep f (packet k) next)
  (D.packetAt_successor method initial cfg language k)).mpr
  (after_native_whole_action (baseFactory root visit rec) f (packet k))

theorem actual_written_next (k : Nat) :
 ((runtime).tickAt (D.index method initial cfg language (k+1)-1)).next.node =
 .active (AS.admissionPresentation method (packet (k+1))) := by
 have positive : 1 ≤ D.index method initial cfg language (k+1) :=
  Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le (D.index method initial cfg language k))
   ((D.strictMono method initial cfg language) (Nat.lt_succ_self k)))
 have indexEq : D.index method initial cfg language (k+1)-1+1 =
  D.index method initial cfg language (k+1) := Nat.sub_add_cancel positive
 have native := congrArg (fun engine => engine.node)
  (SourceNativeInquiryRuntime.stateAt_succ_engine runtime
   (D.index method initial cfg language (k+1)-1)).symm
 have same := congrArg (fun tick => ((runtime).stateAt tick).engine.node) indexEq
 exact native.trans (same.trans (D.actual_index method initial cfg language (k+1)))

theorem actual_method_field_segment (k : Nat) :
 let start := D.index method initial cfg language k
 let fuel := 1 + D.distance method initial cfg language (start+1)
 (fun value : SourceOperationInquiry.Field runtime => SourceOperationInquiry.fieldAction runtime value)^[fuel]
  (SourceOperationInquiry.fieldPoint runtime ((runtime).stateAt start)) =
 SourceOperationInquiry.fieldPoint runtime ((runtime).stateAt (D.index method initial cfg language (k+1))) := by
 let start := D.index method initial cfg language k
 let fuel := 1 + D.distance method initial cfg language (start+1)
 exact (Generic.field_segment runtime start fuel).trans
  (congrArg (fun tick => SourceOperationInquiry.fieldPoint runtime ((runtime).stateAt tick))
   (D.history_end_index method initial cfg language k))

-- The four faces consume the installed action coordinate, while the inventory query
-- keeps its independently generated disposition at the same actual occurrence.
def cofinal_paid_method_faces (k : Nat) :=
 let current := packet k
 let native := AS.nativeAfterAdmission method current
 let faces := actual_native_faces (baseFactory root visit rec) f current
 PProd.mk (D.packetAt_successor method initial cfg language k) <|
 PProd.mk (D.packetAt_successor_grade method initial cfg language k) <|
 PProd.mk (actual_paid_recovery root visit rec U7 calculus anchor sourceStage stage count f k) <|
 PProd.mk (actual_method_step root visit rec U7 calculus anchor sourceStage stage count f k) <|
 PProd.mk (actual_complete_query_written (baseFactory root visit rec) f current) <|
 PProd.mk (actual_born_stock native) <|
 PProd.mk faces <|
 PProd.mk (SourceOperationScalarCochain.evaluation_boundary (R := ℤ) (s := Act.sort root rec)
  faces.packet.2.1.raw.environment
  (faces.packet.2.1.nextRaw.environment - faces.packet.2.1.raw.environment)) <|
 PProd.mk (D.actual_index method initial cfg language k) <|
 PProd.mk (D.actual_index method initial cfg language (k+1)) <|
 PProd.mk (actual_written_next root visit rec U7 calculus anchor sourceStage stage count f k) <|
 PProd.mk (SF.actual_receipt method initial cfg language (D.index method initial cfg language k)) <|
 PProd.mk (SF.actual_whole method initial cfg language (D.index method initial cfg language k)) <|
 PProd.mk (SF.actual_next method initial cfg language (D.index method initial cfg language k)) <|
 PProd.mk (SF.actual_whole method initial cfg language (D.index method initial cfg language (k+1)-1)) <|
 PProd.mk (D.history_end_index method initial cfg language k) <|
 PProd.mk (D.complete_word method initial cfg language k) <|
 PProd.mk (D.actual_source_action method initial cfg language (D.index method initial cfg language k)) <|
 PProd.mk (actual_method_field_segment root visit rec U7 calculus anchor sourceStage stage count f k) <|
 PProd.mk (SourceOperationInquiry.source_word runtime
  (SourceOperationInquiry.fieldPoint runtime ((runtime).stateAt (D.index method initial cfg language k)))) <|
 PProd.mk (SourceOperationInquiry.word_action runtime
  (SourceOperationInquiry.fieldPoint runtime ((runtime).stateAt (D.index method initial cfg language k))))
 (D.historyAt method initial cfg language k)

def finiteHistory (updates : Nat) := (runtime).run (D.index method initial cfg language (updates+1)+1)

theorem step_within_history (updates : Nat) (k : Fin (updates+1)) :
 D.index method initial cfg language (k.val+1)+1 ≤ D.index method initial cfg language (updates+1)+1 := by
 exact Nat.succ_le_succ ((D.strictMono method initial cfg language).monotone (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)))

def finite_paid_method_faces (updates : Nat) :=
 PProd.mk (finiteHistory root visit rec U7 calculus anchor sourceStage stage count f updates)
 (fun k : Fin (updates+1) => PProd.mk
  (step_within_history root visit rec U7 calculus anchor sourceStage stage count f updates k)
  (cofinal_paid_method_faces root visit rec U7 calculus anchor sourceStage stage count f k.val))
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation.PaidMethod.Admissions
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
