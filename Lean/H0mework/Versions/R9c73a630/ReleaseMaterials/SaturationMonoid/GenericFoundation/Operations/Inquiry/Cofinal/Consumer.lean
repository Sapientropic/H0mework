import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Activation.Admissions
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInquiryCofinalDiagram
open RootInquiryCompletion CategoryTheory SourceOperationEffects SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalProcessDiagram
namespace Admission
namespace D
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
 (sourceRuntime index strictMono cover packetAt actual_index historyAt history_end_index distance actual_segment)
end D
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily
 (Factory actual_node)
end SF
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (erasure_injective)
end AS
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
end A
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
variable (factory : SF.Factory W X s)
variable (initial : M.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)

abbrev currentRuntime := D.sourceRuntime factory initial cfg language
abbrev stop := D.index factory initial cfg language

def schedule : ℕ ⥤ ℕ := (D.strictMono factory initial cfg language).monotone.functor

def diagram : ℕᵒᵖ ⥤ ShortComplex (ModuleCat.{u+13} ℤ) :=
 (schedule factory initial cfg language).op ⋙ generatedDiagram (currentRuntime factory initial cfg language)

theorem actual_object (ordinal : Nat) :
 (diagram factory initial cfg language).obj (Opposite.op ordinal) =
 object (currentRuntime factory initial cfg language)
  ((currentRuntime factory initial cfg language).stateAt (stop factory initial cfg language ordinal)) := by
 change (localProcess (currentRuntime factory initial cfg language)).objectAt
  (stop factory initial cfg language ordinal) = _
 unfold CofinalDiagramSuccessorProcessAt.objectAt
 rw [generated_state]
 rfl

theorem actual_arrow (ordinal : Nat) :
 (diagram factory initial cfg language).map (homOfLE (Nat.le_add_right ordinal 1)).op =
 (generatedDiagram (currentRuntime factory initial cfg language)).map
  (homOfLE ((D.strictMono factory initial cfg language).monotone (Nat.le_add_right ordinal 1))).op := rfl

def cofinal_cover (bound : Nat) : Σ ordinal : Nat, PLift (bound ≤ stop factory initial cfg language ordinal) :=
 D.cover factory initial cfg language bound

abbrev field (ordinal : Nat) := SourceOperationInquiry.fieldPoint
 (currentRuntime factory initial cfg language)
 ((currentRuntime factory initial cfg language).stateAt (stop factory initial cfg language ordinal))

theorem full_word (ordinal : Nat) :
 SourceOperationInquiry.word (currentRuntime factory initial cfg language)
  (field factory initial cfg language ordinal) =
 SourceOperationInquiry.point (currentRuntime factory initial cfg language)
  ((currentRuntime factory initial cfg language).stateAt (stop factory initial cfg language ordinal)) :=
 SourceOperationInquiry.word_point _ _

theorem actual_admission (ordinal : Nat) : type_of% (D.actual_index factory initial cfg language ordinal) :=
 D.actual_index factory initial cfg language ordinal

abbrev span (ordinal : Nat) := 1+D.distance factory initial cfg language (stop factory initial cfg language ordinal+1)

theorem span_end (ordinal : Nat) : stop factory initial cfg language ordinal+span factory initial cfg language ordinal =
 stop factory initial cfg language (ordinal+1) := D.history_end_index factory initial cfg language ordinal

theorem source_span (ordinal : Nat) :
 (SourceOperationInquiry.sourceAction (currentRuntime factory initial cfg language))^[span factory initial cfg language ordinal]
  (SourceOperationInquiry.word (currentRuntime factory initial cfg language) (field factory initial cfg language ordinal)) =
 SourceOperationInquiry.word (currentRuntime factory initial cfg language) (field factory initial cfg language (ordinal+1)) := by
 rw [full_word, full_word, iterated_point, span_end]

theorem occurrence_injective : Function.Injective (field factory initial cfg language) := by
 intro left right sameField
 have sameState := SourceOperationInquiry.fieldPoint_injective
  (currentRuntime factory initial cfg language) sameField
 have sameNode := congrArg (fun state => state.engine.node) sameState
 rw [SF.actual_node, SF.actual_node] at sameNode
 have samePresentation := RootInquiryProcessNode.active.inj sameNode
 have sameStop := AS.erasure_injective factory initial cfg language
  (congrArg RootInquiryStatePresentation.erase samePresentation)
 exact (D.strictMono factory initial cfg language).injective sameStop

end Admission
end SourceInquiryCofinalDiagram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
