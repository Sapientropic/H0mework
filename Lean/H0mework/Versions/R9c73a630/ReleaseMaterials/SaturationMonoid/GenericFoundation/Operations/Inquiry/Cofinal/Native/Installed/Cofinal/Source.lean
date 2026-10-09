import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Consumer
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "ActualCofinalInstalledRaw"

/-! Source-generated installed raw at every actual cofinal admission.
The original packet selects its grade, full frame and programme; its actual
node identity transports the existing installed projection and complete
native material, including its trace and responsibility owner. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalInstalledRaw
open RootInquiryCompletion SourceOperationEffects
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily
 (Factory)
end SF
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (AdmissionPacket admissionPresentation)
end AS
namespace D
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
 (sourceRuntime packetAt actual_index index)
end D
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower
 (Value groups)
end L
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
end A
namespace SO
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation
 (current root)
end SO
namespace I
export ActualInstalledNativeRaw (stockRawRestriction stock_raw_read)
end I
namespace C
export ActualCanonicalBornSource (MaterialAtCurrent RequestAtCurrent)
end C
namespace T
export ActualNativeRelationTransport (paid paid_raw paid_environment paid_state)
end T
namespace O
export SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation (readRaw)
end O

section Transport
variable {Sorts : Type u} {Value Var : Sorts → Type u}
 [∀ target, AddCommGroup (Value target)] {s : Sorts}

private theorem restriction_transport_read
 (first second : AnyAuthoritativeRootCurrent.{u}) (same : first = second)
 (restriction : SourceOperationInquiry.Context.RawRestrictionAt
  (PhysicalValue := Value) (PhysicalVar := Var) (sort := s) first) :
 O.readRaw second (Eq.mp (congrArg (SourceOperationInquiry.Context.RawRestrictionAt
  (PhysicalValue := Value) (PhysicalVar := Var) (sort := s)) same) restriction) =
 O.readRaw first restriction := by
 subst second
 rfl

private theorem material_transport_data
 (first second : AnyAuthoritativeRootCurrent.{u}) (same : first = second)
 (material : C.MaterialAtCurrent (Value := Value) (Var := Var) (s := s) first) :
 let actual := Eq.mp
  (congrArg (C.MaterialAtCurrent (Value := Value) (Var := Var) (s := s)) same) material
 actual.environment = material.environment ∧ actual.raw = material.raw ∧
 HEq actual.state material.state ∧ HEq actual.owner material.owner := by
 subst second
 exact ⟨rfl,rfl,HEq.rfl,HEq.rfl⟩
end Transport

variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
local instance familyGroups (grade : Nat) (target : Sorts) :
 AddCommGroup (L.Value W grade target) := L.groups W grade target
variable (factory : SF.Factory W X s)
variable (initial : M.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)

/-- This is the original generated full packet, including the grade and LowVar equality. -/
abbrev packet (ordinal : Nat) := D.packetAt factory initial cfg language ordinal

/-- The complete sealed runtime state fixes the exact source current. -/
def currentAtStop (ordinal : Nat) :=
 SourceOperationInquiry.Context.current (D.sourceRuntime factory initial cfg language)
  ((D.sourceRuntime factory initial cfg language).stateAt (D.index factory initial cfg language ordinal))

private theorem admission_current (data : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 (AS.admissionPresentation factory data).erase = SO.current data.2.1.1 data.2.2.1 := rfl

/-- The source's actual node theorem recognizes the same complete packet current. -/
theorem actual_current (ordinal : Nat) : currentAtStop factory initial cfg language ordinal =
 SO.current (packet factory initial cfg language ordinal).2.1.1
  (packet factory initial cfg language ordinal).2.2.1 :=
 (congrArg RootInquiryProcessNode.erase (D.actual_index factory initial cfg language ordinal)).trans
  (admission_current factory (packet factory initial cfg language ordinal))

attribute [local irreducible] currentAtStop AS.admissionPresentation

/-- Every source-generated admission supplies its own installed restriction, at its own grade. -/
def rawAtStop (ordinal : Nat) : SourceOperationInquiry.Context.RawRestrictionAt
 (PhysicalValue := L.Value W (packet factory initial cfg language ordinal).1)
 (PhysicalVar := X) (sort := s) (currentAtStop factory initial cfg language ordinal) :=
 Eq.mp (congrArg (SourceOperationInquiry.Context.RawRestrictionAt
  (PhysicalValue := L.Value W (packet factory initial cfg language ordinal).1)
  (PhysicalVar := X) (sort := s)) (actual_current factory initial cfg language ordinal).symm)
  (I.stockRawRestriction (packet factory initial cfg language ordinal).2.1.1
   (packet factory initial cfg language ordinal).2.2.1)

/-- Reading the installed projection returns this packet's original registered raw. -/
theorem rawAtStop_read (ordinal : Nat) :
 O.readRaw _ (rawAtStop factory initial cfg language ordinal) =
 (packet factory initial cfg language ordinal).2.1.1.rawRead :=
 (restriction_transport_read
  (SO.current (packet factory initial cfg language ordinal).2.1.1
   (packet factory initial cfg language ordinal).2.2.1)
  (currentAtStop factory initial cfg language ordinal)
  (actual_current factory initial cfg language ordinal).symm
  (I.stockRawRestriction (packet factory initial cfg language ordinal).2.1.1
   (packet factory initial cfg language ordinal).2.2.1)).trans
  (I.stock_raw_read (packet factory initial cfg language ordinal).2.1.1
   (packet factory initial cfg language ordinal).2.2.1)

/-- The complete material and owner belong to that same emitted occurrence, not a scalar shadow. -/
def materialAtStop (ordinal : Nat) : C.MaterialAtCurrent
 (Value := L.Value W (packet factory initial cfg language ordinal).1) (Var := X) (s := s)
 (currentAtStop factory initial cfg language ordinal) :=
 Eq.mp (congrArg (C.MaterialAtCurrent
  (Value := L.Value W (packet factory initial cfg language ordinal).1) (Var := X) (s := s))
  (actual_current factory initial cfg language ordinal).symm)
  (T.paid (packet factory initial cfg language ordinal).2.1.1)

/-- Exact transport preserves registered coordinates, the full state/Trace, and the actual owner. -/
theorem materialAtStop_source (ordinal : Nat) :
 (materialAtStop factory initial cfg language ordinal).environment =
  (packet factory initial cfg language ordinal).2.1.1.registered.input.environment ∧
 (materialAtStop factory initial cfg language ordinal).raw =
  (packet factory initial cfg language ordinal).2.1.1.registered.input.expression ∧
 HEq (materialAtStop factory initial cfg language ordinal).state
  (packet factory initial cfg language ordinal).2.1.1.event.state ∧
 HEq (materialAtStop factory initial cfg language ordinal).owner
  (T.paid (packet factory initial cfg language ordinal).2.1.1).owner := by
 have source := material_transport_data
  (SO.current (packet factory initial cfg language ordinal).2.1.1
   (packet factory initial cfg language ordinal).2.2.1)
  (currentAtStop factory initial cfg language ordinal)
  (actual_current factory initial cfg language ordinal).symm
  (T.paid (packet factory initial cfg language ordinal).2.1.1)
 exact ⟨source.1.trans (T.paid_environment _),source.2.1.trans (T.paid_raw _),
  source.2.2.1.trans (heq_of_eq (T.paid_state _)),source.2.2.2⟩

/-- The same source material produces the registered request, retaining its actual responsibility. -/
def requestAtStop (ordinal : Nat) : C.RequestAtCurrent
 (Value := L.Value W (packet factory initial cfg language ordinal).1) (Var := X) (s := s)
 (currentAtStop factory initial cfg language ordinal) where
 environment := (materialAtStop factory initial cfg language ordinal).environment
 expression := (materialAtStop factory initial cfg language ordinal).raw
 owner := (materialAtStop factory initial cfg language ordinal).owner

end ActualCofinalInstalledRaw
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
