import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Next.Source
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Source
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "ActualInstalledNativeRaw"
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualInstalledNativeRaw
open RootInquiryCompletion SourceOperationEffects
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
end A
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (root visit)
end S
namespace O
export SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation
 (rawRestriction readRaw raw_restriction)
end O
namespace SO
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation
 (root current)
end SO
namespace C
export ActualCanonicalBornSource
 (actual_born_root_current registeredAtNext_source cofinalRegisteredAtNext cofinalRegisteredAtNext_source)
end C
namespace N
export ActualSourceSegmentBornEffect (selected NativeSegmentAt)
end N
namespace B
export ActualNativeBornSourceEffect (born actual_born_registered_expression)
end B
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily
 (Factory)
end SF
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (stockCfg presentationAt)
end AS
namespace D
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
 (distance index)
end D
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower
 (Value groups)
end L

section Current
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ target, AddCommGroup (Value target)] {s : Sorts}
variable (frame : M.Frame (Value := Value) (Var := Var) (sort := s))
variable (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := s))

/-- The existing stock observation changes no raw projection or emitted source. -/
def stockRawRestriction : SourceOperationInquiry.Context.RawRestrictionAt
 (PhysicalValue := Value) (PhysicalVar := Var) (sort := s) (SO.current frame cfg) where
 projection := (O.rawRestriction frame cfg).projection
 active := (O.rawRestriction frame cfg).active
 classifier_eq := (O.rawRestriction frame cfg).classifier_eq
 payload_eq := (O.rawRestriction frame cfg).payload_eq

theorem stock_raw_read : O.readRaw _ (stockRawRestriction frame cfg) = frame.rawRead :=
 (show O.readRaw _ (stockRawRestriction frame cfg) = O.readRaw _ (O.rawRestriction frame cfg) from rfl).trans
  (O.raw_restriction frame cfg)

theorem raw_registered : frame.rawRead =
 (⟨frame.registered.input.environment,frame.registered.input.expression⟩ :
  SourceOperationInquiry.Context.Raw (PhysicalValue := Value) (PhysicalVar := Var) (sort := s)) := rfl

private theorem restriction_transport_read
 (first second : AnyAuthoritativeRootCurrent.{u}) (same : first = second)
 (restriction : SourceOperationInquiry.Context.RawRestrictionAt
  (PhysicalValue := Value) (PhysicalVar := Var) (sort := s) first) :
 O.readRaw second (Eq.mp (congrArg (SourceOperationInquiry.Context.RawRestrictionAt
  (PhysicalValue := Value) (PhysicalVar := Var) (sort := s)) same) restriction) =
 O.readRaw first restriction := by
 subst second
 rfl
end Current

variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
local instance familyGroups (grade : Nat) (target : Sorts) : AddCommGroup (L.Value W grade target) := L.groups W grade target
variable (factory : SF.Factory W X s)
variable (initial : M.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)
attribute [local irreducible] AS.presentationAt

def rawAtNext (start : Nat) (branch : N.NativeSegmentAt factory initial cfg language start) :
 SourceOperationInquiry.Context.RawRestrictionAt
  (PhysicalValue := L.Value W branch.1.1) (PhysicalVar := X) (sort := s)
  (AS.presentationAt factory initial cfg language (start+D.distance factory initial cfg language start)).erase :=
 Eq.mp (congrArg (SourceOperationInquiry.Context.RawRestrictionAt
   (PhysicalValue := L.Value W branch.1.1) (PhysicalVar := X) (sort := s))
  (C.actual_born_root_current factory initial cfg language start branch).1.symm)
  (stockRawRestriction (B.born (N.selected branch.1) branch.1.2.2.1) (AS.stockCfg branch.1.2.2.1))

theorem rawAtNext_read (start : Nat) (branch : N.NativeSegmentAt factory initial cfg language start) :
 O.readRaw _ (rawAtNext factory initial cfg language start branch) =
 (B.born (N.selected branch.1) branch.1.2.2.1).rawRead :=
 (restriction_transport_read
  (SO.current (B.born (N.selected branch.1) branch.1.2.2.1) (AS.stockCfg branch.1.2.2.1))
  (AS.presentationAt factory initial cfg language (start+D.distance factory initial cfg language start)).erase
  (C.actual_born_root_current factory initial cfg language start branch).1.symm
  (stockRawRestriction (B.born (N.selected branch.1) branch.1.2.2.1) (AS.stockCfg branch.1.2.2.1))).trans
  (stock_raw_read (B.born (N.selected branch.1) branch.1.2.2.1) (AS.stockCfg branch.1.2.2.1))

end ActualInstalledNativeRaw
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
