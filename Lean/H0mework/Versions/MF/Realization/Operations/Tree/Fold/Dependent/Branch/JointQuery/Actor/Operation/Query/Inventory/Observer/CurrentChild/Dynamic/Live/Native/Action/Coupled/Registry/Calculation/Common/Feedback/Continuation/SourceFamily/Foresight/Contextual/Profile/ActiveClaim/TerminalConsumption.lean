import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Terminal
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Environment
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace SourceRegisteredTerminalTransport
namespace J
export RootGeneratedDebtActivationJointSource.Successor.Inquiry (mathCurrent mathAnswerFace)
end J
namespace R
export RootGeneratedDebtActivationJointSource.Successor.Restructuring
 (finiteVisit runtimeCurrent mathFace authoritySource oldInstallation)
end R
namespace C
export RootGeneratedDebtActivationJointSource.Successor.Restructuring.Completion
 (runtime_depth completedRuntime completedEvent)
end C
namespace Install
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Assembly (baseInstallation)
end Install
variable {S : Type u} {U X : S → Type u} [∀t,AddCommGroup (U t)] {s : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=U) (Var:=X) (sort:=s))
variable (clock : frame.depth+1=remaining frame.registered.input.expression)
include clock in
theorem source_current : J.mathCurrent frame.old frame.registered frame.packetAt frame.depth=
 R.runtimeCurrent frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt
  (C.completedRuntime frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt) := by
 have before:=SourceRegisteredClaimClock.source_current frame (frame.depth+1)
 change J.mathCurrent frame.old frame.registered frame.packetAt frame.depth=
  (R.finiteVisit frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt (frame.depth+1)).current at before
 rw [clock] at before
 have depth:=C.runtime_depth frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt
  (remaining frame.registered.input.expression)
 exact before.trans (congrArg (fun count=>(R.finiteVisit frame.old.root.toAuthoritativeRoot
  frame.registered frame.packetAt count).current) depth).symm

include clock in
theorem source_face : (J.mathAnswerFace frame.old frame.registered frame.packetAt frame.depth).rootRead=
 (R.mathFace frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt
  (C.completedRuntime frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt)).rootRead :=
 congrArg (RootGeneratedDebtActivationJointSource.Native.mathReadout frame.registered) (source_current frame clock)

theorem inherited_outcome (count : Nat) : type_of% ((Install.baseInstallation frame.old frame.registered frame.packetAt).outcome_heq
 (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.emitted frame.registered frame.packetAt
  (R.runtimeCurrent frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt
   (RootGeneratedDebtActivationJointSource.Successor.Restructuring.Completion.runtime
    frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt count)))
 ((R.oldInstallation frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt).embed (.inr PUnit.unit))) :=
 (Install.baseInstallation frame.old frame.registered frame.packetAt).outcome_heq _ _
end SourceRegisteredTerminalTransport
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
namespace Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.TerminalConsumption
namespace T
export Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Terminal
 (receiver budget endpointFrame source_clock endpointState endpointFace answerConsumer completed completedEvent written
  terminal_value compiled endpoint_budget completed_fee no_paid endpointDebt sameDebt canonical_next actual_tick)
end T
namespace Claim
export Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim (material activeEnv activeExpression)
end Claim
namespace Sealed
export SourceRegisteredClaimClock (suffixHistory suffix_no_restart source_suffix_factorizes)
export Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Clock (active_remainder_positive active_suffix_completed)
end Sealed
variable {S : Type u} {W X : S → Type u} [∀t,AddCommGroup (W t)] {s : S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding : ∀t,X t→Expr W X t) (n : Nat)
variable (packet : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)

theorem terminal_source_current : type_of% (SourceRegisteredTerminalTransport.source_current
 (T.endpointFrame binding n packet) (T.source_clock binding n packet)) :=
 SourceRegisteredTerminalTransport.source_current _ (T.source_clock binding n packet)

theorem terminal_source_face : type_of% (SourceRegisteredTerminalTransport.source_face
 (T.endpointFrame binding n packet) (T.source_clock binding n packet)) :=
 SourceRegisteredTerminalTransport.source_face _ (T.source_clock binding n packet)

theorem original_suffix : type_of% (Sealed.active_suffix_completed binding n packet) :=
 Sealed.active_suffix_completed binding n packet

theorem terminal_suffix_face : (T.endpointFace binding n packet).rootRead=
 (RootGeneratedDebtActivationJointSource.Successor.Restructuring.mathFace
  (T.receiver binding n packet).old.root.toAuthoritativeRoot
  (T.receiver binding n packet).registered (T.receiver binding n packet).packetAt
  (Sealed.suffixHistory (T.receiver binding n packet)).target).rootRead :=
 (terminal_source_face binding n packet).trans
 (congrArg (fun runtime=>(RootGeneratedDebtActivationJointSource.Successor.Restructuring.mathFace
  (T.receiver binding n packet).old.root.toAuthoritativeRoot
  (T.receiver binding n packet).registered (T.receiver binding n packet).packetAt runtime).rootRead)
  (Sealed.active_suffix_completed binding n packet)).symm

theorem source_ledger_factorization : type_of% (Sealed.source_suffix_factorizes (T.receiver binding n packet)) :=
 Sealed.source_suffix_factorizes (T.receiver binding n packet)

theorem terminal_inverse : type_of% ((RootGeneratedDebtActivationJointSource.Native.ResidualRequest.residual_value
 (R:=ℤ) (Claim.material binding n packet)).trans (T.terminal_value binding n packet).symm) :=
 (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.residual_value
  (R:=ℤ) (Claim.material binding n packet)).trans (T.terminal_value binding n packet).symm

namespace Actual
open RootLawDependentJointStateController
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
abbrev actual_answer (k : Nat) := T.answerConsumer (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)

theorem actual_compiled (k : Nat) : type_of% (T.compiled (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)) := T.compiled _ _ _

theorem actual_suffix (k : Nat) : type_of% (original_suffix (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)) := original_suffix _ _ _

theorem actual_original_face (k : Nat) : type_of% (terminal_source_face (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)) := terminal_source_face _ _ _

theorem actual_suffix_face (k : Nat) : type_of% (terminal_suffix_face (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)) := terminal_suffix_face _ _ _

abbrev actual_debt (k : Nat) := T.endpointDebt (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)

theorem actual_debt_claim (k : Nat) : type_of% (actual_debt root visit rec U7 calculus anchor sourceStage stage count k).sameDebt.claim_eq :=
 (actual_debt root visit rec U7 calculus anchor sourceStage stage count k).sameDebt.claim_eq

theorem actual_tick (k depth : Nat) : type_of% (T.actual_tick (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k) depth) := T.actual_tick _ _ _ depth

theorem actual_inverse (k : Nat) : type_of% (terminal_inverse (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)) := terminal_inverse _ _ _

theorem actual_no_paid (k : Nat) : type_of% (T.no_paid (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)) := T.no_paid _ _ _

theorem actual_all_fee (k : Nat) : type_of% (T.completed_fee (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)) := T.completed_fee _ _ _

theorem actual_ledger_factorization (k : Nat) : type_of% (source_ledger_factorization (Run.binding root visit rec) (k+1)
 (Run.data root visit rec U7 calculus anchor sourceStage stage count k)) := source_ledger_factorization _ _ _

theorem consume (k : Nat) : type_of% (And.intro
 (actual_compiled root visit rec U7 calculus anchor sourceStage stage count k)
 (And.intro (actual_suffix_face root visit rec U7 calculus anchor sourceStage stage count k)
 (And.intro (actual_ledger_factorization root visit rec U7 calculus anchor sourceStage stage count k)
 (And.intro (actual_debt_claim root visit rec U7 calculus anchor sourceStage stage count k)
 (And.intro (actual_inverse root visit rec U7 calculus anchor sourceStage stage count k)
 (actual_no_paid root visit rec U7 calculus anchor sourceStage stage count k)))))) :=
 ⟨actual_compiled _ _ _ _ _ _ _ _ _ _,actual_suffix_face _ _ _ _ _ _ _ _ _ _,
 actual_ledger_factorization _ _ _ _ _ _ _ _ _ _,actual_debt_claim _ _ _ _ _ _ _ _ _ _,
 actual_inverse _ _ _ _ _ _ _ _ _ _,actual_no_paid _ _ _ _ _ _ _ _ _ _⟩
end Actual
end Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.TerminalConsumption
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
