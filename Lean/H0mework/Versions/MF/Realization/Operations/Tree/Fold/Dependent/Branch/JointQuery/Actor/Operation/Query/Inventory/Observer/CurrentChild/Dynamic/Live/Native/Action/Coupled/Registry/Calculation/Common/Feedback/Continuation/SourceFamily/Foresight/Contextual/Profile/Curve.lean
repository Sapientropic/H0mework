import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Receiver
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation

open RootInquiryCompletion SourceOperationEffects SourceOperationScalarInventoryLift SourceOperationScalarPresentation SourceOperationScalarRelations
namespace Lower.SourceFamily.Foresight.Contextual.Profile.Curve
namespace O
export SourceOperationInquiry.Context.Native.Orbit.Installation (ofFrame)
end O
namespace P
export Lower.SourceFamily.Foresight.Contextual.Profile.Producer (physical pair)
end P
namespace A
export Lower.SourceFamily.Foresight.Contextual.Profile.Ordinal (parentAdvance registeredAdvance registered_parent_prefix)
end A
namespace Origin
export Lower.SourceFamily.Foresight.Contextual.Profile.Origin (physical_prefix)
end Origin
namespace R
export Lower.SourceFamily.Foresight.Contextual.Profile.Receiver (cfg receiver cursor sigma receiver_callback receiver_physical_prefix)
end R
namespace E
export Lower.SourceFamily.Foresight.Contextual.Profile.Erasure (reader_environment)
end E
variable {S : Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat) (seed:Lower.SourceFamily.Seed W X s n)
variable (frame:M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s))
abbrev replayCfg:=Lower.SourceFamily.cfg (Lower.SourceFamily.Replay.factory (s:=s) binding) n seed
abbrev replayReceiver:=Lower.SourceFamily.receiver (Lower.SourceFamily.Replay.factory (s:=s) binding) n ⟨frame,seed⟩
abbrev replayCursor:=O.ofFrame (replayReceiver binding n seed frame)

theorem replay_callback
 (current:RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered) :
 (replayReceiver binding n seed frame).environment
  ((SourceGeneratedInquiryReceiptAction.old frame (replayCfg binding n seed)).root.toAuthoritativeRoot.toLedgerRoot.emitted current)=
 Future.Replay.Source.pairEnvironment (R.sigma binding n)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame)
  ((SourceGeneratedInquiryReceiptAction.old frame (replayCfg binding n seed)).root.toAuthoritativeRoot.toLedgerRoot.emitted current) :=rfl

theorem replay_parent_prefix (k:Nat) :
 (A.parentAdvance (replayCursor binding n seed frame).old (replayCursor binding n seed frame).packetAt k
  (replayCursor binding n seed frame).current.1).1=
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

theorem replay_physical_prefix (k:Nat) :
 P.physical ((replayCursor binding n seed frame).advance k)=
 P.pair (R.sigma binding n) ((O.ofFrame frame).advance (k+1)) :=by
 have first := Origin.physical_prefix (replayCursor binding n seed frame) k
 have second := replay_callback binding n seed frame
  (A.parentAdvance (replayCursor binding n seed frame).old (replayCursor binding n seed frame).packetAt k
   (replayCursor binding n seed frame).current.1)
 have projected := congrArg (fun c => frame.environment (frame.old.root.toAuthoritativeRoot.toLedgerRoot.emitted c))
  (replay_parent_prefix binding n seed frame k)
 have paired := congrArg (fun base : Env (Lower.Value W n) X =>
  pairEnvironment base (SourceSubstitution.sourceEnvironment (R.sigma binding n) base-base)) projected
 have last := Lower.SourceFamily.Foresight.Contextual.Profile.Origin.pair_prefix (O.ofFrame frame) (R.sigma binding n) (k+1)
 exact first.trans (second.trans (paired.trans last.symm))

theorem replay_actual_curve (k:Nat) :
 P.physical ((replayCursor binding n seed frame).advance k)=
 P.physical ((R.cursor binding n seed frame).advance k) :=
 (replay_physical_prefix binding n seed frame k).trans (R.receiver_physical_prefix binding n seed frame k).symm

abbrev EnvCurve (n:Nat) := Nat→Env (Lower.Value W n) X
def curve (data:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n) : EnvCurve (W:=W) (X:=X) n :=
 fun k=>P.physical ((O.ofFrame data.1).advance k)
def push (current:EnvCurve (W:=W) (X:=X) n) : EnvCurve (W:=W) (X:=X) (n+1) :=fun k=>
 pairEnvironment (current (k+1))
  (SourceSubstitution.sourceEnvironment (R.sigma binding n) (current (k+1))-current (k+1))
variable (data:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
theorem actual_step_curve :
 curve (n+1) (Lower.SourceFamily.step (Lower.SourceFamily.Foresight.Contextual.factory (s:=s) binding) n data)=
 push binding n (curve n data) :=by
 funext k
 exact R.receiver_physical_prefix binding n data.2 data.1 k

theorem replay_step_curve :
 curve (n+1) (Lower.SourceFamily.step (Lower.SourceFamily.Replay.factory (s:=s) binding) n data)=
 push binding n (curve n data) :=by
 funext k
 exact replay_physical_prefix binding n data.2 data.1 k

end Lower.SourceFamily.Foresight.Contextual.Profile.Curve
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
