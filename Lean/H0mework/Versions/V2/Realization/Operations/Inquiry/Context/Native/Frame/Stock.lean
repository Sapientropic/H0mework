import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Native.Frame.Source
import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Frame.Stock
open SourceOperationEffects SourceOperationScalarInventoryLift
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch Programme)
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (frames runtime query root visit actualOccurrence resultFace datum targetAt target_next actual_query)
end A
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory
  (programme actual_query actual_value actual_trace_written born_complete_inventory decoder_preserved
   installed source_inventory raw)
end I
namespace R
export SourceGeneratedInquiryReceiptAction
  (actualMaterial actual_raw actual_calculation_state source_effect source_inverse whole_first literal_next)
end R
variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (initial : SourceFrame (Value := Value) (Var := Var) (sort := sort))
variable (configuration : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))

/-- This frame belongs to the existing inventory programme's canonical runtime. -/
abbrev frameAt (stage : Nat) := read initial (I.programme configuration)
  ((A.runtime initial (I.programme configuration)).stateAt stage)
theorem frame_actual (stage : Nat) :
    frameAt initial configuration stage = A.frames initial (I.programme configuration) stage :=
  actual initial (I.programme configuration) stage

theorem full_model_next (stage : Nat) :
    observer initial (I.programme configuration)
      (SourceOperationInquiry.Context.readCompletion (A.runtime initial (I.programme configuration))
        (SourceOperationInquiry.Context.completionAction (A.runtime initial (I.programme configuration))
          (SourceOperationInquiry.Context.completionPoint (A.runtime initial (I.programme configuration))
            ((A.runtime initial (I.programme configuration)).stateAt stage)))) =
      Finsupp.single (frameAt initial configuration (stage + 1)) 1 := by
  rw [frame_actual]
  exact model_next initial (I.programme configuration) stage

theorem sealed_query (stage : Nat) :
    HEq ((A.runtime initial (I.programme configuration)).stateAt stage).activation.query
      (A.query (frameAt initial configuration stage) (I.programme configuration)) := by
  rw [frame_actual]
  exact A.actual_query initial (I.programme configuration) stage
theorem source_query (stage : Nat) : type_of% (I.actual_query (frameAt initial configuration stage) configuration) :=
  I.actual_query (frameAt initial configuration stage) configuration
theorem source_value (stage : Nat) : type_of% (I.actual_value (frameAt initial configuration stage) configuration) :=
  I.actual_value (frameAt initial configuration stage) configuration
theorem source_trace (stage : Nat) : type_of% (I.actual_trace_written (frameAt initial configuration stage) configuration) :=
  I.actual_trace_written (frameAt initial configuration stage) configuration
theorem born_stock (stage : Nat) : type_of% (I.born_complete_inventory (frameAt initial configuration stage) configuration) :=
  I.born_complete_inventory (frameAt initial configuration stage) configuration
theorem source_decoder (stage : Nat) (pair : PairValue Value sort) :
    type_of% (I.decoder_preserved (frameAt initial configuration stage) configuration pair) :=
  I.decoder_preserved (frameAt initial configuration stage) configuration pair

theorem registered_raw (stage : Nat) :
    (R.actualMaterial (frameAt initial configuration stage) (I.programme configuration)).raw =
      (I.raw (A.epoch (frameAt initial configuration stage)) configuration
        (A.actualOccurrence (frameAt initial configuration stage))).expression := by
  rw [R.actual_raw]
  dsimp [SourceGeneratedInquiryReceiptAction.actionReader,
    SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum,
    SourceGeneratedInquiryReceiptAction.Inventory.programme,
    SourceGeneratedInquiryReceiptAction.Inventory.reader]
theorem registered_state (stage : Nat) : type_of%
    (R.actual_calculation_state (frameAt initial configuration stage) (I.programme configuration)) :=
  R.actual_calculation_state (frameAt initial configuration stage) (I.programme configuration)

/-- These receipts concern the registered inventory-query calculation. -/
theorem calculation_effect (stage : Nat) : type_of%
    (R.source_effect (frameAt initial configuration stage) (I.programme configuration)) :=
  R.source_effect (frameAt initial configuration stage) (I.programme configuration)
theorem calculation_inverse (stage : Nat) : type_of%
    (R.source_inverse (frameAt initial configuration stage) (I.programme configuration)) :=
  R.source_inverse (frameAt initial configuration stage) (I.programme configuration)
theorem calculation_whole (stage : Nat) : type_of%
    (R.whole_first (frameAt initial configuration stage) (I.programme configuration)) :=
  R.whole_first (frameAt initial configuration stage) (I.programme configuration)
theorem calculation_next (stage : Nat) : type_of%
    (R.literal_next (frameAt initial configuration stage) (I.programme configuration)) :=
  R.literal_next (frameAt initial configuration stage) (I.programme configuration)

theorem same_ledger (stage : Nat) :
    (A.root (frameAt initial configuration stage) (I.programme configuration)).toAuthoritativeRoot.toLedgerRoot =
      (A.root (frameAt initial configuration stage) configuration).toAuthoritativeRoot.toLedgerRoot := by
  cases (configuration.datum (A.epoch (frameAt initial configuration stage))).component <;> rfl
def physicalTarget (stage : Nat) :=
  A.targetAt (frameAt initial configuration stage) (I.programme configuration)
    ((A.root (frameAt initial configuration stage) (I.programme configuration)).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (A.visit (frameAt initial configuration stage) (I.programme configuration)))
theorem canonical_stock (stage : Nat) : type_of%
    (((physicalTarget initial configuration stage).oldOutcome_heq
      ((I.installed (frameAt initial configuration stage) configuration).embed PUnit.unit)).trans
        (I.source_inventory (frameAt initial configuration stage) configuration)) :=
  ((physicalTarget initial configuration stage).oldOutcome_heq
    ((I.installed (frameAt initial configuration stage) configuration).embed PUnit.unit)).trans
      (I.source_inventory (frameAt initial configuration stage) configuration)
/-- The original residual compiler supplies this canonical next independently. -/
theorem canonical_next (stage : Nat) : type_of%
    (A.target_next (frameAt initial configuration stage) (I.programme configuration)
      ((A.root (frameAt initial configuration stage) (I.programme configuration)).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (A.visit (frameAt initial configuration stage) (I.programme configuration)))) :=
  A.target_next (frameAt initial configuration stage) (I.programme configuration)
    ((A.root (frameAt initial configuration stage) (I.programme configuration)).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (A.visit (frameAt initial configuration stage) (I.programme configuration)))
end SourceOperationInquiry.Context.Native.Frame.Stock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
