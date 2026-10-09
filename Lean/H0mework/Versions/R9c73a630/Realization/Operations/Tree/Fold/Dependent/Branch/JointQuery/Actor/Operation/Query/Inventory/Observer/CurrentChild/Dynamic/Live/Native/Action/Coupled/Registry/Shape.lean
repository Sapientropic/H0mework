import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
inductive Shape : Type
 | var | const | add (left right : Shape) | linear (argument : Shape) | bilinear (left right : Shape)
def Shape.fee : Shape → Nat
 | .var => 1
 | .const => 0
 | .add first second => first.fee+second.fee+1
 | .linear argument => argument.fee+1
 | .bilinear first second => first.fee+second.fee+1
variable {S : Type u} {Value Var : S → Type u} [∀ s,AddCommGroup (Value s)] {s : S}
def shape : {target : S} → Expr Value Var target → Shape
 | _,.var _ => .var
 | _,.const _ => .const
 | _,.add first second => .add (shape first) (shape second)
 | _,.linear _ argument => .linear (shape argument)
 | _,.bilinear _ first second => .bilinear (shape first) (shape second)
theorem shape_fee {target : S} (expression : Expr Value Var target) : (shape expression).fee=remaining expression := by
 induction expression with
 | var => rfl
 | const => rfl
 | add _ _ first second => exact congrArg₂ (fun a b : Nat => a+b+1) first second
 | linear _ _ prior => exact congrArg (fun a : Nat => a+1) prior
 | bilinear _ _ _ first second => exact congrArg₂ (fun a b : Nat => a+b+1) first second
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (root frames next_progress frames_forward visit)
end Shared
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=s))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=s))
def shapeSource := {(Shared.root frame cfg).source.base with
 observationAt:=fun {_current} _ => ⟨ULift.{u} Shape,ULift.up (shape frame.rawRead.expression)⟩}
def shapeAuthority : SourceNativeAuthoritativeRootClosure
 (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World frame.registered)
 (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV frame.registered frame.packetAt) where
 source:=shapeSource frame cfg
 emitted:=(Shared.root frame cfg).emitted
 compiler_commutes:=(Shared.root frame cfg).compiler_commutes
-- Same source compiler, current and whole-ledger are retained; the public read actually changes.
theorem shape_ledger : (shapeAuthority frame cfg).toLedgerRoot=(Shared.root frame cfg).toAuthoritativeRoot.toLedgerRoot := rfl
theorem shape_observation (current) : (shapeAuthority frame cfg).observationAt current=
 ⟨ULift.{u} Shape,ULift.up (shape frame.rawRead.expression)⟩ := rfl
-- All later actual receivers have source syntax charge at least the first receiver's charge.
theorem tail_rank_monotone (offset : Nat) : frame.rank.1≤
 (Shared.frames frame cfg offset).rank.1 := by
 cases offset with
 | zero => exact Nat.le_refl _
 | succ offset =>
  have grows := Shared.frames_forward frame cfg 0 offset
  rw [Nat.zero_add] at grows
  rcases grows with increases | ⟨same,_⟩
  · exact Nat.le_of_lt increases
  · exact Nat.le_of_eq same
def shapeCurrent : AnyAuthoritativeRootCurrent.{u} :=
 ⟨RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World frame.registered,
  ⟨RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV frame.registered frame.packetAt,
   shapeAuthority frame cfg,Shared.visit frame cfg⟩⟩
theorem current_observation : RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.observation
 (shapeCurrent frame cfg)=⟨ULift.{u} Shape,ULift.up (shape frame.rawRead.expression)⟩ := rfl
theorem current_depth : RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.erasedDepth
 (shapeCurrent frame cfg)=frame.rank.2 := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.depth_source frame cfg
-- Fixed Shape exposes the same original-syntax fee for different physical vocabularies.
variable {T : Type u} {OtherValue OtherVar : T → Type u} [∀ target,AddCommGroup (OtherValue target)] {t : T}
variable (other : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=OtherValue) (Var:=OtherVar) (sort:=t))
variable (otherCfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue:=OtherValue) (PhysicalVar:=OtherVar) (sort:=t))
theorem heterogeneous_fee (same : shapeCurrent frame cfg=shapeCurrent other otherCfg) :
 remaining frame.rawRead.expression=remaining other.rawRead.expression := by
 have reads := congrArg RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.observation same
 rw [current_observation,current_observation] at reads
 have shapes := congrArg ULift.down (eq_of_heq (Sigma.mk.inj reads).2)
 exact (shape_fee frame.rawRead.expression).symm.trans
  ((congrArg Shape.fee shapes).trans (shape_fee other.rawRead.expression))
theorem first_tail_separated (strict : frame.rank.1<other.rank.1) (offset : Nat) :
 shapeCurrent frame cfg≠shapeCurrent (Shared.frames other otherCfg offset) otherCfg := by
 intro same
 have fees := heterogeneous_fee frame cfg (Shared.frames other otherCfg offset) otherCfg same
 have monotone := tail_rank_monotone other otherCfg offset
 change frame.rank.1=(Shared.frames other otherCfg offset).rank.1 at fees
 omega
namespace C
export RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw (World JointV)
end C
theorem noFaithful (current : (C.JointV frame.registered frame.packetAt).Current) :
 IsEmpty ((C.JointV frame.registered frame.packetAt).FaithfulTerminalAt current) := by
 constructor
 intro terminal
 have actual := (frame.packetAt current.1).actual_next
 rw [terminal.2] at actual
 cases actual
def observedRoot := (shapeAuthority frame cfg).toLivingWithoutFaithfulTerminal (noFaithful frame)
theorem observed_root_observation (current) : (observedRoot frame cfg).toAuthoritativeRoot.observationAt current=
 ⟨ULift.{u} Shape,ULift.up (shape frame.rawRead.expression)⟩ := rfl
namespace Original
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (query query_unique base resultAt resultFace queryInstallation resultInstallation consumerInstallation compilationInstallation actualOccurrence visit)
end Original
abbrev Germ := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Query frame cfg
namespace I
export RootGeneratedDebtActivationJointSource.Successor.Inquiry (finiteVisit patch_destination_math)
end I
abbrev finiteVisit (depth : Nat) : RootVisit (observedRoot frame cfg).toAuthoritativeRoot.toRoot :=
 I.finiteVisit frame.old frame.registered frame.packetAt depth
abbrev visitAt (depth : Nat) := SourceNativeTemporalVisitAt.finite (finiteVisit frame cfg depth)
def initialRow : ((observedRoot frame cfg).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit (visitAt frame cfg 0)).GeneratedEntryRowAt
 (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.mathEntry frame.registered (finiteVisit frame cfg 0).current) :=
 (((observedRoot frame cfg).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit (visitAt frame cfg 0)).canonicalGeneratedEntryRow?
  (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.mathEntry frame.registered (finiteVisit frame cfg 0).current)).get (by rfl)
def authorityAt : (depth : Nat) → SourceNativeLivingTemporalCausalEntryAuthorityAt
 (observedRoot frame cfg) (visitAt frame cfg depth)
 (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.mathEntry frame.registered (finiteVisit frame cfg depth).current)
 | 0 => .generatedFromInitialRow (observedRoot frame cfg) _ (initialRow frame cfg)
 | depth+1 => by
  have next := (authorityAt depth).next (by rfl)
  have entryEq : (observedRoot frame cfg).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext (by rfl)
   (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.mathEntry frame.registered (finiteVisit frame cfg depth).current)=
   RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.mathEntry frame.registered (finiteVisit frame cfg (depth+1)).current :=
   I.patch_destination_math frame.old frame.registered frame.packetAt (finiteVisit frame cfg depth).current
  exact entryEq ▸ next
abbrev visit := Original.visit frame cfg
def authority : SourceNativeLivingTemporalCausalEntryAuthorityAt (observedRoot frame cfg) (visit frame cfg)
 (frame.currentState.entryAt PUnit.unit) := authorityAt frame cfg (frame.depth+1)
def queryInput : SourceNativeRootInquiryInputAt (observedRoot frame cfg) (visit frame cfg) (Germ frame cfg) where
 projection:=(Original.queryInstallation frame cfg).embed PUnit.unit
 active:=PUnit.unit
 classifier_eq:=rfl
 queryType_eq:=rfl
abbrev query := (queryInput frame cfg).query
def resultFace : SourceNativeRootSemanticFaceAt (observedRoot frame cfg) (visit frame cfg) where
 projection:=(Original.resultInstallation frame cfg).embed PUnit.unit
 active:=PUnit.unit
 classifier_eq:=rfl
def consumer : SourceNativeInquiryAnswerConsumerAt (root:=observedRoot frame cfg) (visit:=visit frame cfg) (query frame cfg)
 (ULift.up.{u+1,u} (Original.actualOccurrence frame)) (frame.currentState.entryAt PUnit.unit) (resultFace frame cfg) where
 projection:=(Original.consumerInstallation frame cfg).embed PUnit.unit
 active:=PUnit.unit
 classifier_eq:=rfl
 project_heq:=HEq.rfl
def answeredCompilation : SourceNativeInquiryCompilationProgramAt (observedRoot frame cfg) (visit frame cfg)
 (Original.base frame).U7 (Original.base frame).calculus (observedRoot frame cfg).source.base.lawSurface
 (query frame cfg) (ULift.up.{u+1,u} (Original.actualOccurrence frame))
 (frame.currentState.entryAt PUnit.unit) (authority frame cfg) where
 compile:=fun _ => .answered (resultFace frame cfg) (consumer frame cfg)
def answeredState : RootInquiryStateAt (C.World frame.registered) (C.JointV frame.registered frame.packetAt) where
 root:=observedRoot frame cfg
 visit:=visit frame cfg
 U7:=(Original.base frame).U7
 calculus:=(Original.base frame).calculus
 Query:=Germ frame cfg
 entryAt:=fun _ => frame.currentState.entryAt PUnit.unit
 authorityAt:=fun _ => authority frame cfg
 compilationProgramAt:=fun candidate => Original.query_unique frame cfg candidate ▸ answeredCompilation frame cfg
 compilationFaceAt:=fun candidate => by
  cases Original.query_unique frame cfg candidate
  exact {projection:=(Original.compilationInstallation frame cfg).embed PUnit.unit
         active:=PUnit.unit
         classifier_eq:=rfl
         project_heq:=HEq.rfl}
 u7RootDisposition_commutes:=by
  intro candidate _ _ impossible
  cases Original.query_unique frame cfg candidate
  exact nomatch impossible
theorem answered_compiles : (answeredState frame cfg).compileInquiry (query frame cfg)=
 .answered (resultFace frame cfg) (consumer frame cfg) := rfl
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
