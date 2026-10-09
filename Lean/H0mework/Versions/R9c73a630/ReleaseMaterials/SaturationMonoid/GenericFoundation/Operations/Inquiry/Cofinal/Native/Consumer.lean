import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Consumer
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "ActualSourceSegmentBornEffect"
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w z
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualSourceSegmentBornEffect
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily (Factory)
end SF
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (AdmissionPacket localNativeReceipt localPaidAt nativePresentation stockCfg)
end AS
namespace D
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
 (sourceRuntime actual_segment startAt index historyAt actual_index distance)
end D
namespace ST
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockTarget (compiles_settled)
end ST
namespace Steps
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (frames)
end Steps
namespace B
export ActualNativeBornSourceEffect (born actual_born_effect actual_born_relation_residual actual_born_affine_write actual_born_inverse bornEnvArrow)
end B
namespace T
export ActualNativeRelationTransport (paid new_relation_in_born new_relation_face new_full_trace stock_paid_trace)
end T
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
local instance familyGroups (grade : Nat) (target : Sorts) : AddCommGroup
 (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.Value W grade target) :=
 SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.groups W grade target

abbrev selected (native : AS.AdmissionPacket (W := W) (X := X) (s := s)) :=
 Steps.frames native.2.1.1 (AS.stockCfg native.2.2.1) (0+(AS.localNativeReceipt native).1)

theorem selected_settled (native : AS.AdmissionPacket (W := W) (X := X) (s := s)) : type_of%
 (ST.compiles_settled (selected native) (AS.stockCfg native.2.2.1)
  (AS.localNativeReceipt native).2.1 (AS.localNativeReceipt native).2.2.2) :=
 ST.compiles_settled _ _ _ (AS.localNativeReceipt native).2.2.2

def nativePayload (native : AS.AdmissionPacket (W := W) (X := X) (s := s)) :=
 (PLift.up (selected_settled native),
  PLift.up (T.stock_paid_trace (selected native) native.2.2.1),
  PLift.up (T.new_relation_in_born (selected native) native.2.2.1),
  PLift.up (T.new_relation_face (selected native)),
  PLift.up (T.new_full_trace (selected native)),
  PLift.up (B.actual_born_effect (selected native) native.2.2.1),
  PLift.up (B.actual_born_relation_residual (selected native) native.2.2.1),
  PLift.up (B.actual_born_affine_write (selected native) native.2.2.1),
  PLift.up (B.actual_born_inverse (selected native) native.2.2.1),
  B.bornEnvArrow (selected native) native.2.2.1)

variable (factory : SF.Factory W X s)
variable (initial : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)

abbrev NativeSegmentAt (start : Nat) :=
 Σ native : AS.AdmissionPacket (W := W) (X := X) (s := s),
  PLift (D.distance factory initial cfg language start = (AS.localNativeReceipt native).1+1) ×
  ((offset : Fin (AS.localNativeReceipt native).1) → type_of% (AS.localPaidAt native offset)) ×
  PLift (∀ offset, offset ≤ (AS.localNativeReceipt native).1 →
   ((D.sourceRuntime factory initial cfg language).stateAt (start+offset)).engine.node =
    .active (AS.nativePresentation native offset))

attribute [local irreducible] AS.localNativeReceipt D.actual_segment

/-- Enrich the already-generated dependent source segment; all original node and paid witnesses remain inside. -/
def realizedSegment (start : Nat) :=
 (D.actual_segment factory initial cfg language start).map id
  (fun native => (⟨native,nativePayload native.1⟩ : Σ branch : NativeSegmentAt factory initial cfg language start, type_of% (nativePayload branch.1)))

def cofinalSegment (ordinal : Nat) := realizedSegment factory initial cfg language
 (D.index factory initial cfg language ordinal+1)

private theorem enrichment_erases {Admission : Type v} {Native : Type w}
 {Payload : Native → Type z} (build : (native : Native) → Payload native)
 (original : Admission ⊕ Native) :
 (original.map id (fun native => (⟨native,build native⟩ : Σ node, Payload node))).map
  id (fun enriched => enriched.1) = original := by
 cases original <;> rfl

/-- Erasing the dependent enrichment returns the original generated segment. -/
theorem realizedSegment_source (start : Nat) :
 (realizedSegment factory initial cfg language start).map id
  (fun enriched : Σ branch : NativeSegmentAt factory initial cfg language start,
    type_of% (nativePayload branch.1) => enriched.1) =
 D.actual_segment factory initial cfg language start :=
 enrichment_erases
  (Admission := PLift (D.distance factory initial cfg language start = 0))
  (Native := NativeSegmentAt factory initial cfg language start)
  (Payload := fun branch => type_of% (nativePayload branch.1))
  (fun branch => nativePayload branch.1)
  (D.actual_segment factory initial cfg language start)

/-- Eliminate the generated branch while retaining its original dependent packet. -/
def consumeCofinalSegment {Result : Sort v} (ordinal : Nat)
 (atAdmission : D.distance factory initial cfg language
   (D.index factory initial cfg language ordinal+1) = 0 → Result)
 (atNative : (branch : NativeSegmentAt factory initial cfg language
   (D.index factory initial cfg language ordinal+1)) →
  type_of% (nativePayload branch.1) → Result) : Result :=
 Sum.elim
  (α := PLift (D.distance factory initial cfg language
    (D.index factory initial cfg language ordinal+1) = 0))
  (β := Σ branch : NativeSegmentAt factory initial cfg language
    (D.index factory initial cfg language ordinal+1), type_of% (nativePayload branch.1))
  (γ := Result)
  (fun already => atAdmission already.down)
  (fun enriched => atNative enriched.1 enriched.2)
  (cofinalSegment factory initial cfg language ordinal)


abbrev cofinalDiagram := SourceInquiryCofinalDiagram.Admission.diagram factory initial cfg language

theorem cofinal_source_span (ordinal : Nat) : type_of%
 (SourceInquiryCofinalDiagram.Admission.source_span factory initial cfg language ordinal) :=
 SourceInquiryCofinalDiagram.Admission.source_span _ _ _ _ _

end ActualSourceSegmentBornEffect
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
