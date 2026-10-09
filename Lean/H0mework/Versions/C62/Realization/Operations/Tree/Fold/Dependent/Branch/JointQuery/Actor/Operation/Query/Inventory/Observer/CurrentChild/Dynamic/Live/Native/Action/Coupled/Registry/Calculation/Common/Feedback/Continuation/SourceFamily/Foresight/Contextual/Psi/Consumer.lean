import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Psi.Closure
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace Lower.SourceFamily.Foresight.Contextual.Psi.Actual
namespace Cl
export Lower.SourceFamily.Foresight.Contextual.Psi.Closure
 (terminal_in_stock terminal_written terminal_in_history boundary_relation boundaryGenerator boundaryRelation
  actual_after_boundary presented_boundary_zero actual_disposition_read next_query_consumes)
end Cl
namespace Wr
export Lower.SourceFamily.Foresight.Contextual.Written (receiver_pair receiver stock)
end Wr
namespace Term
export Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Terminal (written)
end Term
namespace Lift
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (liftEvent)
end Lift
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.Profile.Kernel.Actual.physicalGroups
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.Profile.Kernel.Actual.currentGroups
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
variable (anchor sourceStage stage count : Nat)
namespace Run
export Lower.SourceFamily.Foresight.Contextual.Profile.Kernel.Actual.Run (binding data actual_depth)
end Run

theorem actual_next_inventory (k : Nat) :
 (Run.data root visit rec U7 calculus anchor sourceStage stage count (k+1)).1.pairInventory=
 some (Wr.stock (Run.binding root visit rec) (k+1)
  (Run.data root visit rec U7 calculus anchor sourceStage stage count k)) :=
 (congrArg (fun packet=>packet.1.pairInventory)
  (Lower.SourceFamily.Foresight.Contextual.Profile.Kernel.Actual.next_packet
   root visit rec U7 calculus anchor sourceStage stage count k)).symm.trans (Wr.receiver_pair _ _ _)

theorem actual_terminal_in_next (k : Nat) (event)
 (present : event∈(Term.written (Run.binding root visit rec) (k+1)
  (Run.data root visit rec U7 calculus anchor sourceStage stage count k)).trace) :
 match (Run.data root visit rec U7 calculus anchor sourceStage stage count (k+1)).1.pairInventory with
 | none => False
 | some inventory => Lift.liftEvent event∈inventory.trace := by
 rw [actual_next_inventory root visit rec U7 calculus anchor sourceStage stage count k]
 exact Cl.terminal_in_stock _ _ _ event present

theorem actual_terminal_written (k : Nat) : type_of% (Cl.terminal_written (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)) := Cl.terminal_written _ _ _

theorem actual_all_paid_history (k : Nat) (event)
 (present : event∈(Term.written (Run.binding root visit rec) (k+1)
  (Run.data root visit rec U7 calculus anchor sourceStage stage count k)).trace) : type_of%
 (Cl.terminal_in_history (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k) event present) :=
 Cl.terminal_in_history _ _ _ event present

theorem actual_boundary_relation (k : Nat) : type_of% (Cl.actual_after_boundary (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)) := Cl.actual_after_boundary _ _ _

theorem actual_completion_zero (k : Nat) : type_of% (Cl.presented_boundary_zero (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)) := Cl.presented_boundary_zero _ _ _

theorem actual_scope_disposition (k : Nat) : type_of% (Cl.actual_disposition_read (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)) := Cl.actual_disposition_read _ _ _

theorem actual_source_query (k : Nat) : type_of% (Cl.next_query_consumes (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)) := Cl.next_query_consumes _ _ _

theorem consume (k : Nat) : type_of% (And.intro
 (Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.TerminalConsumption.Actual.consume
  root visit rec U7 calculus anchor sourceStage stage count k)
 (And.intro (actual_boundary_relation root visit rec U7 calculus anchor sourceStage stage count k)
 (And.intro (actual_completion_zero root visit rec U7 calculus anchor sourceStage stage count k)
 (And.intro (actual_scope_disposition root visit rec U7 calculus anchor sourceStage stage count k)
 (And.intro (actual_source_query root visit rec U7 calculus anchor sourceStage stage count k)
 (Lower.SourceFamily.Replay.Activated.actual_whole_next root visit rec U7 calculus anchor sourceStage stage count (k+1))))))) :=
 ⟨Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.TerminalConsumption.Actual.consume _ _ _ _ _ _ _ _ _ _,
 actual_boundary_relation _ _ _ _ _ _ _ _ _ _,actual_completion_zero _ _ _ _ _ _ _ _ _ _,
 actual_scope_disposition _ _ _ _ _ _ _ _ _ _,actual_source_query _ _ _ _ _ _ _ _ _ _,
 Lower.SourceFamily.Replay.Activated.actual_whole_next _ _ _ _ _ _ _ _ _ _⟩
end Lower.SourceFamily.Foresight.Contextual.Psi.Actual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
