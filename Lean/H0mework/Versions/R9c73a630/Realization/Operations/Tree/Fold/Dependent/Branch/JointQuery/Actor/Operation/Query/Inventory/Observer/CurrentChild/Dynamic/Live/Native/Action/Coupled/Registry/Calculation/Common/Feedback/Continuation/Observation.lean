import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Bootstrap.Source
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
namespace StockObservation
variable {S : Type u} {W X : S → Type u} [∀ s,AddCommGroup (W s)] {s : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=W) (Var:=X) (sort:=s))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
abbrev size := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.Stock.size frame
def read : SourceNativeMaterialBox.{u} :=
 ⟨ULift.{u} (Shape × Nat),ULift.up (shape frame.rawRead.expression,size frame)⟩
def root := Observation.Material.root (Shared.root frame cfg).toAuthoritativeRoot (read frame) (noFaithful frame)
theorem observation (current) : (root frame cfg).toAuthoritativeRoot.observationAt current=read frame := rfl
-- Scalar inventory contents/order stay inside the existing source; this read exposes their actual size.
theorem same_ledger : (root frame cfg).toAuthoritativeRoot.toLedgerRoot=(Shared.root frame cfg).toAuthoritativeRoot.toLedgerRoot := rfl

abbrev finiteVisit (depth : Nat) : RootVisit (root frame cfg).toAuthoritativeRoot.toRoot :=
 I.finiteVisit frame.old frame.registered frame.packetAt depth
abbrev visitAt (depth : Nat) := SourceNativeTemporalVisitAt.finite (finiteVisit frame cfg depth)
abbrev visit := Original.visit frame cfg

def initialRow : ((root frame cfg).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit (visitAt frame cfg 0)).GeneratedEntryRowAt
 (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.mathEntry frame.registered (finiteVisit frame cfg 0).current) :=
 (((root frame cfg).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit (visitAt frame cfg 0)).canonicalGeneratedEntryRow?
  (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.mathEntry frame.registered (finiteVisit frame cfg 0).current)).get (by rfl)

def authorityAt (depth : Nat) : SourceNativeLivingTemporalCausalEntryAuthorityAt (root frame cfg) (visitAt frame cfg depth)
 (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.mathEntry frame.registered (finiteVisit frame cfg depth).current)
 := Nat.rec (.generatedFromInitialRow (root frame cfg) _ (initialRow frame cfg))
  (fun depth prior => by
   have next := prior.next (by rfl)
   have entryEq : (root frame cfg).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext (by rfl)
    (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.mathEntry frame.registered (finiteVisit frame cfg depth).current)=
    RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.mathEntry frame.registered (finiteVisit frame cfg (depth+1)).current :=
    I.patch_destination_math frame.old frame.registered frame.packetAt (finiteVisit frame cfg depth).current
   exact entryEq ▸ next) depth

def authority : SourceNativeLivingTemporalCausalEntryAuthorityAt (root frame cfg) (visit frame cfg)
 (frame.currentState.entryAt PUnit.unit) := authorityAt frame cfg (frame.depth+1)

def current : AnyAuthoritativeRootCurrent.{u} :=
 ⟨C.World frame.registered,⟨C.JointV frame.registered frame.packetAt,(root frame cfg).toAuthoritativeRoot,visit frame cfg⟩⟩

theorem current_observation : RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.observation (current frame cfg)=read frame := rfl

theorem canonical_initial_next : (root frame cfg).generatedNextCurrentAt (.finite (root frame cfg).toAuthoritativeRoot.toRoot.initialVisit)=
 ⟨C.JointV frame.registered frame.packetAt,(root frame cfg).toAuthoritativeRoot,visitAt frame cfg 1⟩ := by
 apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
 rfl
end StockObservation
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
