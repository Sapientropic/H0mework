import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Admission
import H0mework.Versions.Rdf421ff6.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock

set_option autoImplicit false
set_option Elab.async false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

/-- An actual contiguous inventory segment, including its position and multiplicity. -/
structure SourceInventoryTraceSegment {A : Type u}
    (source target : RootedAccountedUnfolding A) where
  before : List A
  after : List A
  trace_eq : target.trace = before ++ source.trace ++ after

namespace SourceInventoryTraceSegment
variable {A : Type u} {source middle target : RootedAccountedUnfolding A}

def refl (source : RootedAccountedUnfolding A) : SourceInventoryTraceSegment source source :=
  ⟨[], [], by simp only [List.nil_append, List.append_nil]⟩

def left (source other : RootedAccountedUnfolding A) :
    SourceInventoryTraceSegment source (SourceHistoryCommon.seed source other) :=
  ⟨[source.root], other.trace, by
    change source.root :: (source.trace ++ (other.trace ++ [])) = _
    simp only [List.append_nil, List.nil_append, List.cons_append]⟩

def right (other source : RootedAccountedUnfolding A) :
    SourceInventoryTraceSegment source (SourceHistoryCommon.seed other source) :=
  ⟨other.root :: other.trace, [], by
    change other.root :: (other.trace ++ (source.trace ++ [])) = _
    simp only [List.append_nil, List.cons_append]⟩

def trans (first : SourceInventoryTraceSegment source middle)
    (second : SourceInventoryTraceSegment middle target) : SourceInventoryTraceSegment source target :=
  ⟨second.before ++ first.before, first.after ++ second.after, by
    rw [second.trace_eq, first.trace_eq]
    simp only [List.append_assoc]⟩

theorem present (segment : SourceInventoryTraceSegment source target)
    (event : A) (member : event ∈ source.trace) : event ∈ target.trace := by
  rw [segment.trace_eq]
  exact List.mem_append_left _ (List.mem_append_right _ member)

end SourceInventoryTraceSegment

namespace SourceInventoryExecutionFeed.WordReceipt.RelationOccurrence
open SourceOperationEffects SourceOperationScalarInventoryLift SourceOperationScalarRelations
open CofinalHistorySettlement
variable {S : Type u} {V X : S → Type u} [∀ t, AddCommGroup (V t)] {s : S}
variable {source target : Inventory (V := V) (X := X) (s := s)}

def transport (occurrence : WordReceipt.RelationOccurrence source)
    (segment : SourceInventoryTraceSegment source target) : WordReceipt.RelationOccurrence target :=
  ⟨segment.before ++ occurrence.before, occurrence.word,
    occurrence.after ++ segment.after, by
      rw [segment.trace_eq, occurrence.trace_eq]
      simp only [List.append_assoc, List.cons_append]⟩

theorem transport_word (occurrence : WordReceipt.RelationOccurrence source)
    (segment : SourceInventoryTraceSegment source target) :
    (occurrence.transport segment).word = occurrence.word := rfl

theorem transport_position (occurrence : WordReceipt.RelationOccurrence source)
    (segment : SourceInventoryTraceSegment source target) :
    (occurrence.transport segment).before.length = segment.before.length + occurrence.before.length :=
  List.length_append

namespace Stock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (mapped_trace)
end Stock

namespace T
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual (liftEvent)
end T

def lift (occurrence : WordReceipt.RelationOccurrence source) :
    WordReceipt.RelationOccurrence (source.map T.liftEvent) :=
  ⟨occurrence.before.map T.liftEvent, liftMap (R := ℤ) occurrence.word,
    occurrence.after.map T.liftEvent, by
      rw [Stock.mapped_trace, occurrence.trace_eq, List.map_append, List.map_cons]
      rfl⟩

theorem lift_word (occurrence : WordReceipt.RelationOccurrence source) :
    occurrence.lift.word = liftMap (R := ℤ) occurrence.word := rfl

theorem lift_position (occurrence : WordReceipt.RelationOccurrence source) :
    occurrence.lift.before.length = occurrence.before.length := List.length_map _

end SourceInventoryExecutionFeed.WordReceipt.RelationOccurrence

namespace SourceInventoryExecutionFeed.AdmissionReceipt.GeneratorOccurrence
open SourceOperationEffects SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {S : Type u} {V X : S → Type u} [∀ t, AddCommGroup (V t)] {s : S}
variable {source : Inventory (V := V) (X := X) (s := s)}
namespace T
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual (liftEvent)
end T
namespace Stock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (mapped_trace)
end Stock

def lift (occurrence : GeneratorOccurrence source) : GeneratorOccurrence (source.map T.liftEvent) :=
  ⟨occurrence.before.map T.liftEvent, liftExpr occurrence.expression,
    occurrence.after.map T.liftEvent, by
      rw [Stock.mapped_trace, occurrence.trace_eq, List.map_append, List.map_cons]
      rfl⟩

theorem lift_expression (occurrence : GeneratorOccurrence source) :
    occurrence.lift.expression = liftExpr occurrence.expression := rfl

end SourceInventoryExecutionFeed.AdmissionReceipt.GeneratorOccurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
