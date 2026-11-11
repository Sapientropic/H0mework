import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Occurrence.Transport

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryTraceSegment

universe u v
variable {A : Type u} {B : Type v} {source target : RootedAccountedUnfolding A}

open SourceInventoryExecutionFeed.WordReceipt.RelationOccurrence.Stock

/-- Apply the same event transport to the segment and its enclosing inventory. -/
def map (segment : SourceInventoryTraceSegment source target) (f : A → B) :
    SourceInventoryTraceSegment (source.map f) (target.map f) :=
  ⟨segment.before.map f, segment.after.map f, by
    rw [mapped_trace f target, segment.trace_eq, List.map_append, List.map_append,
      mapped_trace f source]⟩

theorem slice (segment : SourceInventoryTraceSegment source target) :
    (target.trace.drop segment.before.length).take source.trace.length = source.trace := by
  rw [segment.trace_eq, List.append_assoc, List.drop_left, List.take_left]

end SourceInventoryTraceSegment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
