import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Material
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Programme

/-! The orbit source programme is the complete occurrence material coface.
Its raw is read from that component at the supplied event; no result, root,
future query, or target certificate is supplied to the activation algorithm. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Installation.Activation
open RootInquiryCompletion SourceOperationEffects
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme SourceDatum)
end A
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}

def programme : A.Programme (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) where
  LowVar := Orbit.Var PhysicalVar
  datum frame := {
    component := some (component frame)
    reader := fun {_current} occurrence => ((component frame).project PUnit.unit occurrence PUnit.unit).pairRaw }

end SourceOperationInquiry.Context.Native.Orbit.Installation.Activation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
