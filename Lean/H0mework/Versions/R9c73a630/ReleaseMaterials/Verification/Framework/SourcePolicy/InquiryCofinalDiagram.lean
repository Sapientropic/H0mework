import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Consumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceSuccessor
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePolicyActualInquiryDiagram
open RootInquiryCompletion CategoryTheory SourceOperationEffects SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation
namespace Q
export SourceInquiryCofinalDiagram (environment binding object transition generatedDiagram generated_state actual_environment actual_diagram_arrow iterated_point)
end Q
namespace D
export SourceInquiryCofinalDiagram.Admission
 (currentRuntime stop schedule diagram actual_object actual_arrow cofinal_cover field full_word actual_admission span span_end source_span occurrence_injective)
end D
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily (Factory actual_whole actual_branch_receipt)
end SF
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
end A
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
variable (factory : SF.Factory W X s)
variable (initial : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)

example (state : (D.currentRuntime factory initial cfg language).State) : type_of% (Q.actual_environment (D.currentRuntime factory initial cfg language) state) := Q.actual_environment _ _
example (count : Nat) : type_of% (Q.generated_state (D.currentRuntime factory initial cfg language) count) := Q.generated_state _ _
example (count : Nat) : type_of% (Q.actual_diagram_arrow (D.currentRuntime factory initial cfg language) count) := Q.actual_diagram_arrow _ _
example (ordinal : Nat) : type_of% (D.actual_object factory initial cfg language ordinal) := D.actual_object _ _ _ _ _
example (ordinal : Nat) : type_of% (D.actual_arrow factory initial cfg language ordinal) := D.actual_arrow _ _ _ _ _
example (bound : Nat) : type_of% (D.cofinal_cover factory initial cfg language bound) := D.cofinal_cover _ _ _ _ _
example (ordinal : Nat) : type_of% (D.full_word factory initial cfg language ordinal) := D.full_word _ _ _ _ _
example (ordinal : Nat) : type_of% (D.actual_admission factory initial cfg language ordinal) := D.actual_admission _ _ _ _ _
example (ordinal : Nat) : type_of% (D.span_end factory initial cfg language ordinal) := D.span_end _ _ _ _ _
example (ordinal : Nat) : type_of% (D.source_span factory initial cfg language ordinal) := D.source_span _ _ _ _ _
example (ordinal offset : Nat) : type_of% (SF.actual_whole factory initial cfg language (D.stop factory initial cfg language ordinal+offset)) := SF.actual_whole _ _ _ _ _
example (ordinal offset : Nat) : type_of% (SF.actual_branch_receipt factory initial cfg language (D.stop factory initial cfg language ordinal+offset)) := SF.actual_branch_receipt _ _ _ _ _

-- A scalar read may erase every occurrence, while the complete field still distinguishes them.
def erased : SourceOperationInquiry.Carrier (D.currentRuntime factory initial cfg language) →ₗ[ℤ] ℤ := 0

theorem scalar_equal (left right : Nat) :
 erased factory initial cfg language (SourceOperationInquiry.word (D.currentRuntime factory initial cfg language) (D.field factory initial cfg language left)) =
 erased factory initial cfg language (SourceOperationInquiry.word (D.currentRuntime factory initial cfg language) (D.field factory initial cfg language right)) := rfl

theorem occurrences_distinct (ordinal : Nat) :
 D.field factory initial cfg language ordinal ≠ D.field factory initial cfg language (ordinal+1) := by
 intro same
 have impossible := D.occurrence_injective factory initial cfg language same
 exact Nat.ne_of_lt (Nat.lt_succ_self ordinal) impossible

theorem full_field_nonzero (ordinal : Nat) : D.field factory initial cfg language ordinal ≠ 0 :=
 (SourceOwnedObservationHistory.FullWord.zero_not_native
  (SourceOperationInquiry.nextState (D.currentRuntime factory initial cfg language)) _).symm

namespace NamedOriginalK
namespace R
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombSourceSuccessor
 (factory data configuration)
end R
open NoIslandNoMagic.CanonicalRiemann
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1)) (depth : Nat)
variable (half : NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)
attribute [local irreducible] NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombPhysicalAction.code
example (ordinal : Nat) : type_of% (D.actual_object R.factory (R.data observation nontrivial depth half).1
 (R.configuration observation nontrivial half) (by rfl) ordinal) := D.actual_object _ _ _ _ _
example (ordinal : Nat) : type_of% (D.source_span R.factory (R.data observation nontrivial depth half).1
 (R.configuration observation nontrivial half) (by rfl) ordinal) := D.source_span _ _ _ _ _
example (ordinal : Nat) : type_of% (occurrences_distinct R.factory (R.data observation nontrivial depth half).1
 (R.configuration observation nontrivial half) (by rfl) ordinal) := occurrences_distinct _ _ _ _ _
end NamedOriginalK

#print axioms Q.actual_environment
#print axioms Q.generated_state
#print axioms Q.actual_diagram_arrow
#print axioms Q.iterated_point
#print axioms D.actual_object
#print axioms D.actual_arrow
#print axioms D.full_word
#print axioms D.actual_admission
#print axioms D.source_span
#print axioms D.occurrence_injective
#print axioms scalar_equal
#print axioms occurrences_distinct
#print axioms full_field_nonzero
end SourcePolicyActualInquiryDiagram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
