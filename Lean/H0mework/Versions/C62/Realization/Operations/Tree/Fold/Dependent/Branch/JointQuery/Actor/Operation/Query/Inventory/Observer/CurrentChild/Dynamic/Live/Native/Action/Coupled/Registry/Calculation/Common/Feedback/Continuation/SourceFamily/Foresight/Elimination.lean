import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Born
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceGeneratedActionObservationHistory
namespace Lower.SourceFamily.Foresight.Elimination
namespace I
export Lower.SourceFamily.Foresight.Installed (configuration installation High nativeState modelValues native_actual_index)
end I
variable {S : Type u} {W X : S → Type u} [∀ t, AddCommGroup (W t)] {s : S}
attribute [local instance] sourceGroups
variable (binding : ∀ t, X t → Expr W X t) (n : Nat)
variable (seed : Lower.SourceFamily.Seed W X s n)
variable (frame : M.Frame (Value := Lower.Value W n) (Var := X) (sort := s))
def face : SourceNativeRootSemanticFaceAt (Lower.SourceFamily.StockObservation.root frame (I.configuration binding n seed))
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.visit frame (I.configuration binding n seed)) where
  projection := (I.installation binding n seed frame).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

def originalFace : SourceNativeRootSemanticFaceAt (Lower.SourceFamily.StockObservation.root frame (I.configuration binding n seed))
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.visit frame (I.configuration binding n seed)) where
  projection := .inherited (.inherited (.inherited (.inherited
    (.component (.inherited (.component (.component PUnit.unit)))))))
  active := PUnit.unit
  classifier_eq := rfl

theorem original_material : (originalFace binding n seed frame).rootRead =
    SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower.material
      (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame)
      (Future.Replay.Installed.programme (Future.Replay.Binding.at binding n) seed)
      (Future.Replay.Installed.Q.actualOccurrence frame) := rfl

variable (depth : frame.depth = 0)
def high : I.High binding n seed frame := (face binding n seed frame).rootRead.2 (I.native_actual_index n frame depth)
theorem model_read : high binding n seed frame depth = I.modelValues binding n seed frame := rfl
abbrev state := I.nativeState n seed frame
abbrev source := (high binding n seed frame depth).2.2.2.1
abbrev prefixRead := (high binding n seed frame depth).2.2.2.2.1
abbrev successor := (high binding n seed frame depth).2.2.2.2.2.2.1
abbrev logical := (high binding n seed frame depth).2.2.2.2.2.2.2.1
abbrev fullPrime := (high binding n seed frame depth).2.2.2.2.2.2.2.2.1
abbrev dual := (high binding n seed frame depth).2.2.2.2.2.2.2.2.2

theorem source_prefix (t : S) (bound : Nat) (word : Lower.SourceFamily.Foresight.Word binding (state n seed frame) t 0) :
    prefixRead binding n seed frame depth t bound (source binding n seed frame depth t word) =
      AlgebraicDependent.evaluator (Lower.SourceFamily.Foresight.action binding (state n seed frame) t)
        (Lower.SourceFamily.Foresight.read binding (state n seed frame) t) 0 bound word :=
  Lower.SourceFamily.Foresight.source_prefix binding (state n seed frame) t 0 bound word

theorem source_fibre (t : S) (left right : Lower.SourceFamily.Foresight.Word binding (state n seed frame) t 0) :
    source binding n seed frame depth t left = source binding n seed frame depth t right ↔
      ∀ j, Lower.SourceFamily.Foresight.read binding (state n seed frame) t (0+j)
        (AlgebraicDependent.advance (Lower.SourceFamily.Foresight.action binding (state n seed frame) t) 0 j left) =
        Lower.SourceFamily.Foresight.read binding (state n seed frame) t (0+j)
          (AlgebraicDependent.advance (Lower.SourceFamily.Foresight.action binding (state n seed frame) t) 0 j right) :=
  Lower.SourceFamily.Foresight.source_fibre binding (state n seed frame) t 0 left right

theorem next_source (t : S) (word : Lower.SourceFamily.Foresight.Word binding (state n seed frame) t 0) :
    successor binding n seed frame depth t (source binding n seed frame depth t word) =
      Lower.SourceFamily.Foresight.sourceMap binding (Tail.advance binding (state n seed frame)) t 0
        (Lower.SourceFamily.Foresight.action binding (state n seed frame) t 0 word) :=
  Lower.SourceFamily.Foresight.Successor.actual_next_source binding (state n seed frame) t word
end Lower.SourceFamily.Foresight.Elimination
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
