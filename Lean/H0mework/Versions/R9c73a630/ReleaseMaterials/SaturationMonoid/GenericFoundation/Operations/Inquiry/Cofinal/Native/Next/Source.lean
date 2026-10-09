import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Consumer
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "ActualCanonicalBornSource"

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCanonicalBornSource
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarPresentation
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily
 (Factory actual_node)
end SF
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (presentationAt successor_valid stockCfg localNativeReceipt AdmissionPacket)
end AS
namespace D
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
 (distance index sourceRuntime history_end_index)
end D
namespace R
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry
 (query)
end R
namespace ST
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockTarget
 (presentation successor_valid compiles_settled birthProgram target_root)
end ST
namespace SO
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation
 (root current visit)
end SO
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (next nextBorn actualOccurrence)
end S
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
end A
namespace C
export ActualSourceSegmentBornEffect (selected selected_settled NativeSegmentAt cofinalSegment)
end C
namespace B
export ActualNativeBornSourceEffect (born bornMaterial actual_born_registered_expression)
end B
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (MaterialAt expression input)
end N
namespace T
export ActualNativeRelationTransport (paid)
end T
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower
 (Value groups)
end L
private theorem settled_recognition
 {Sorts : Type u} {Value Var : Sorts → Type u} [∀ target, AddCommGroup (Value target)] {s : Sorts}
 (frame : M.Frame (Value := Value) (Var := Var) (sort := s))
 (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := s))
 (settled : SourceOperationExecutionDebt.Settlement frame.event.state)
 (actual : frame.action = .inl settled)
 (source target : RootInquiryStatePresentation.{u})
 (sameSource : source = ST.presentation frame cfg)
 (valid : ∀ query : source.Query,
  target.erase = (RootInquiryProcessNode.answered source query).erase ∧
  (.active source : RootInquiryProcessNode).PreservesGeneratedLivingLawAt query (.active target)) :
 target.erase = SO.current (S.nextBorn frame cfg) cfg ∧
 HEq target.state.base.root (SO.root (S.nextBorn frame cfg) cfg) := by
 subst source
 have generated := valid (R.query frame cfg)
 have standard := ST.successor_valid frame cfg (R.query frame cfg)
 have nextBorn : S.next frame cfg = S.nextBorn frame cfg := by
  unfold S.next
  rw [actual]
 have current : target.erase = SO.current (S.nextBorn frame cfg) cfg :=
  generated.1.trans (standard.1.symm.trans
   (congrArg (fun next => (ST.presentation next cfg).erase) nextBorn))
 have preserves := generated.2
 dsimp only [RootInquiryProcessNode.PreservesGeneratedLivingLawAt] at preserves
 have resolved := RootInquiryProcessNode.active_debtAdmission_resolution_eq
  (ST.presentation frame cfg) (R.query frame cfg)
  ((ST.birthProgram frame cfg).generate
   ((SO.root frame cfg).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (SO.visit frame cfg)))
  (ST.compiles_settled frame cfg settled actual)
 have specialized := Eq.mp
  (congrArg (fun resolution : InternalInquiryResolutionAt
    (ST.presentation frame cfg) (R.query frame cfg) =>
   resolution.PreservesTargetLivingRootAt target) resolved) preserves
 change HEq target.state.base.root
  ((ST.birthProgram frame cfg).generate
   ((SO.root frame cfg).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (SO.visit frame cfg))).target.targetRoot at specialized
 exact ⟨current,specialized.trans (heq_of_eq (ST.target_root frame cfg _))⟩

section Material
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ target, AddCommGroup (Value target)] {s : Sorts}

abbrev MaterialAtCurrent (current : AnyAuthoritativeRootCurrent.{u}) :=
 N.MaterialAt (Value := Value) (Var := Var) (sort := s)
  (lower := current.current.root.toLedgerRoot)
  (current.current.root.emitted current.current.visit.current)

private def materialAtRootCurrent
 (frame : M.Frame (Value := Value) (Var := Var) (sort := s))
 (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := s)) :
 MaterialAtCurrent (Value := Value) (Var := Var) (s := s) (SO.current frame cfg) :=
 T.paid frame

private theorem material_transport_data
 (first second : AnyAuthoritativeRootCurrent.{u}) (same : first = second)
 (material : MaterialAtCurrent (Value := Value) (Var := Var) (s := s) first) :
 (Eq.mp (congrArg (MaterialAtCurrent (Value := Value) (Var := Var) (s := s)) same) material).raw = material.raw ∧
 (Eq.mp (congrArg (MaterialAtCurrent (Value := Value) (Var := Var) (s := s)) same) material).environment = material.environment := by
 subst second
 exact ⟨rfl,rfl⟩

abbrev RequestAtCurrent (current : AnyAuthoritativeRootCurrent.{u}) :=
 RootGeneratedDebtActivationJointSource.RawInputAt
  (Value := Value) (Var := Var) (sort := s)
  current.current.root.toLedgerRoot current.current.visit.current
  (current.current.root.emitted current.current.visit.current)

end Material

variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
local instance familyGroups (grade : Nat) (target : Sorts) : AddCommGroup
 (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.Value W grade target) :=
 SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.groups W grade target
variable (factory : SF.Factory W X s)
variable (initial : M.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)
attribute [local irreducible] AS.localNativeReceipt AS.presentationAt

theorem selected_actual_presentation (start : Nat)
 (branch : C.NativeSegmentAt factory initial cfg language start) :
 AS.presentationAt factory initial cfg language (start+(AS.localNativeReceipt branch.1).1) =
 ST.presentation (C.selected branch.1) (AS.stockCfg branch.1.2.2.1) :=
 RootInquiryProcessNode.active.inj
  ((SF.actual_node factory initial cfg language _).symm.trans
   (branch.2.2.2.down (AS.localNativeReceipt branch.1).1 (Nat.le_refl _)))

theorem actual_born_root_current (start : Nat)
 (branch : C.NativeSegmentAt factory initial cfg language start) :
 (AS.presentationAt factory initial cfg language (start+D.distance factory initial cfg language start)).erase =
  SO.current (B.born (C.selected branch.1) branch.1.2.2.1) (AS.stockCfg branch.1.2.2.1) ∧
 HEq (AS.presentationAt factory initial cfg language (start+D.distance factory initial cfg language start)).state.base.root
  (SO.root (B.born (C.selected branch.1) branch.1.2.2.1) (AS.stockCfg branch.1.2.2.1)) := by
 have recognized := settled_recognition
  (C.selected branch.1) (AS.stockCfg branch.1.2.2.1)
  (AS.localNativeReceipt branch.1).2.1 (AS.localNativeReceipt branch.1).2.2.2
  (AS.presentationAt factory initial cfg language (start+(AS.localNativeReceipt branch.1).1))
  (AS.presentationAt factory initial cfg language ((start+(AS.localNativeReceipt branch.1).1)+1))
  (selected_actual_presentation factory initial cfg language start branch)
  (AS.successor_valid factory initial cfg language (start+(AS.localNativeReceipt branch.1).1))
 have endpoint : ((start+(AS.localNativeReceipt branch.1).1)+1) =
  start+D.distance factory initial cfg language start :=
  (Nat.add_assoc start (AS.localNativeReceipt branch.1).1 1).trans
   (congrArg (fun distance => start+distance) branch.2.1.down).symm
 exact Eq.mp
  (congrArg (fun tick =>
   (AS.presentationAt factory initial cfg language tick).erase =
    SO.current (B.born (C.selected branch.1) branch.1.2.2.1) (AS.stockCfg branch.1.2.2.1) ∧
   HEq (AS.presentationAt factory initial cfg language tick).state.base.root
    (SO.root (B.born (C.selected branch.1) branch.1.2.2.1) (AS.stockCfg branch.1.2.2.1))) endpoint)
  recognized


/-- The actual next source occurrence owns the unchanged native material and responsibility. -/
def materialAtNext (start : Nat) (branch : C.NativeSegmentAt factory initial cfg language start) :
 MaterialAtCurrent (Value := L.Value W branch.1.1) (Var := X) (s := s)
  (AS.presentationAt factory initial cfg language (start+D.distance factory initial cfg language start)).erase :=
 Eq.mp (congrArg (MaterialAtCurrent (Value := L.Value W branch.1.1) (Var := X) (s := s))
  (actual_born_root_current factory initial cfg language start branch).1.symm)
  (materialAtRootCurrent (B.born (C.selected branch.1) branch.1.2.2.1) (AS.stockCfg branch.1.2.2.1))

/-- Retain the registered execution environment; decoded active-Env evaluation is a separate readout. -/
def registeredAtNext (start : Nat) (branch : C.NativeSegmentAt factory initial cfg language start) :
 RequestAtCurrent (Value := L.Value W branch.1.1) (Var := X) (s := s)
  (AS.presentationAt factory initial cfg language (start+D.distance factory initial cfg language start)).erase where
 environment := (materialAtNext factory initial cfg language start branch).environment
 expression := (materialAtNext factory initial cfg language start branch).raw
 owner := (materialAtNext factory initial cfg language start branch).owner

theorem registeredAtNext_source (start : Nat)
 (branch : C.NativeSegmentAt factory initial cfg language start) :
 (registeredAtNext factory initial cfg language start branch).expression =
  N.expression (T.paid (C.selected branch.1)) ∧
 (registeredAtNext factory initial cfg language start branch).environment =
  (B.born (C.selected branch.1) branch.1.2.2.1).registered.input.environment := by
 have copied := material_transport_data
  (SO.current (B.born (C.selected branch.1) branch.1.2.2.1) (AS.stockCfg branch.1.2.2.1))
  (AS.presentationAt factory initial cfg language (start+D.distance factory initial cfg language start)).erase
  (actual_born_root_current factory initial cfg language start branch).1.symm
  (materialAtRootCurrent (B.born (C.selected branch.1) branch.1.2.2.1) (AS.stockCfg branch.1.2.2.1))
 exact ⟨copied.1.trans (B.actual_born_registered_expression (C.selected branch.1) branch.1.2.2.1),copied.2⟩

def cofinalRegisteredAtNext (ordinal : Nat)
 (branch : C.NativeSegmentAt factory initial cfg language (D.index factory initial cfg language ordinal+1)) :
 RequestAtCurrent (Value := L.Value W branch.1.1) (Var := X) (s := s)
  (AS.presentationAt factory initial cfg language (D.index factory initial cfg language (ordinal+1))).erase :=
 registeredAtNext factory initial cfg language (D.index factory initial cfg language ordinal+1) branch

theorem cofinalRegisteredAtNext_source (ordinal : Nat)
 (branch : C.NativeSegmentAt factory initial cfg language (D.index factory initial cfg language ordinal+1)) :
 (cofinalRegisteredAtNext factory initial cfg language ordinal branch).expression =
  N.expression (T.paid (C.selected branch.1)) ∧
 (cofinalRegisteredAtNext factory initial cfg language ordinal branch).environment =
  (B.born (C.selected branch.1) branch.1.2.2.1).registered.input.environment :=
 registeredAtNext_source factory initial cfg language (D.index factory initial cfg language ordinal+1) branch

end ActualCanonicalBornSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
