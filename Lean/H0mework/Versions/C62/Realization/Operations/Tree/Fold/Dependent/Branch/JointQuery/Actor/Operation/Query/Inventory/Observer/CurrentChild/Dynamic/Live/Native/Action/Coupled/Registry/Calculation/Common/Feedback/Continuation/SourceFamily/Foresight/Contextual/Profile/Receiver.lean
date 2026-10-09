import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Origin
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation

open RootInquiryCompletion SourceOperationEffects SourceOperationScalarInventoryLift SourceOperationScalarPresentation SourceOperationScalarRelations
namespace Lower.SourceFamily.Foresight.Contextual.Profile.Receiver
namespace O
export SourceOperationInquiry.Context.Native.Orbit.Installation (ofFrame)
end O
namespace P
export Lower.SourceFamily.Foresight.Contextual.Profile.Producer (physical pair)
end P
namespace A
export Lower.SourceFamily.Foresight.Contextual.Profile.Ordinal (parentAdvance registeredAdvance registered_parent_prefix)
end A
namespace E
export Lower.SourceFamily.Foresight.Contextual.Profile.Origin (physical_prefix pair_prefix parentPair)
end E
namespace Ctx
export Lower.SourceFamily.Foresight.Contextual (factory)
namespace R
export Lower.SourceFamily.Foresight.Contextual.Reader (raw_environment)
end R
end Ctx
variable {S : Type u} {W X : S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat) (seed:Lower.SourceFamily.Seed W X s n)
variable (frame:M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s))
abbrev cfg:=Lower.SourceFamily.cfg (Ctx.factory (s:=s) binding) n seed
abbrev receiver:=Lower.SourceFamily.receiver (Ctx.factory (s:=s) binding) n ⟨frame,seed⟩
abbrev cursor:=O.ofFrame (receiver binding n seed frame)
abbrev sigma:=Future.Replay.Binding.at binding n

theorem receiver_callback
 (current:RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered) :
 (receiver binding n seed frame).environment
  ((SourceGeneratedInquiryReceiptAction.old frame (cfg binding n seed)).root.toAuthoritativeRoot.toLedgerRoot.emitted current)=
 Future.Replay.Source.pairEnvironment (sigma binding n)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame)
  ((SourceGeneratedInquiryReceiptAction.old frame (cfg binding n seed)).root.toAuthoritativeRoot.toLedgerRoot.emitted current) :=
 Ctx.R.raw_environment binding n seed (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame)
  ⟨current,(SourceGeneratedInquiryReceiptAction.old frame (cfg binding n seed)).root.toAuthoritativeRoot.toLedgerRoot.emitted current⟩

theorem receiver_parent_prefix (k:Nat) :
 (A.parentAdvance (cursor binding n seed frame).old (cursor binding n seed frame).packetAt k
  (cursor binding n seed frame).current.1).1=
 A.parentAdvance (O.ofFrame frame).old (O.ofFrame frame).packetAt (k+1) (O.ofFrame frame).current.1 :=by
 have shift : A.parentAdvance frame.old.root.toAuthoritativeRoot.toLedgerRoot frame.packetAt k
   (frame.packetAt (O.ofFrame frame).current.1).targetCurrent=
  A.parentAdvance frame.old.root.toAuthoritativeRoot.toLedgerRoot frame.packetAt (k+1)
   (O.ofFrame frame).current.1 :=by
  induction k with
  | zero=>rfl
  | succ k previous=>exact congrArg (fun c=>(frame.packetAt c).targetCurrent) previous
 have original := A.registered_parent_prefix frame.old.root.toAuthoritativeRoot.toLedgerRoot
  frame.registered frame.packetAt k
  (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.targetCurrent
   frame.registered frame.packetAt (O.ofFrame frame).current)
 exact original.trans shift

theorem receiver_physical_prefix (k:Nat) :
 P.physical ((cursor binding n seed frame).advance k)=
 P.pair (sigma binding n) ((O.ofFrame frame).advance (k+1)) :=by
 have first := E.physical_prefix (cursor binding n seed frame) k
 have second := receiver_callback binding n seed frame
  (A.parentAdvance (cursor binding n seed frame).old (cursor binding n seed frame).packetAt k
   (cursor binding n seed frame).current.1)
 have projected := congrArg (fun c => frame.environment (frame.old.root.toAuthoritativeRoot.toLedgerRoot.emitted c))
  (receiver_parent_prefix binding n seed frame k)
 have paired := congrArg (fun base : Env (Lower.Value W n) X =>
  pairEnvironment base (SourceSubstitution.sourceEnvironment (sigma binding n) base-base)) projected
 have last := E.pair_prefix (O.ofFrame frame) (sigma binding n) (k+1)
 exact first.trans (second.trans (paired.trans last.symm))
end Lower.SourceFamily.Foresight.Contextual.Profile.Receiver
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
