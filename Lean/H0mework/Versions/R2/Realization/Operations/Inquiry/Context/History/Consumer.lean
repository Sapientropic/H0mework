import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.History.Successor
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Installation.Runtime
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Faces.Execution.Mother

/-! The complete history reads the production frame source, including its
actual residual birth. No external evaluator or future query family enters. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.History
open SourceOperationEffects RootInquiryCompletion SourceOperationScalarRelations
namespace C
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation
  (Frame frames runtime)
end C
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (initial : C.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

abbrev actualSource := Installation.rawSource initial

theorem actual_old_environment (count : Nat) :
    readEnv (C.runtime initial) (actualSource initial) ((C.runtime initial).stateAt count) =
      (C.frames initial count).rawRead.environment :=
  congrArg (fun raw => raw.environment) (Installation.raw_actual initial count)

theorem actual_increment (count : Nat) :
    increment (C.runtime initial) (actualSource initial) ((C.runtime initial).stateAt count) =
      (C.frames initial (count + 1)).rawRead.environment -
        (C.frames initial count).rawRead.environment := by
  change readEnv (C.runtime initial) (actualSource initial) ((C.runtime initial).stateAt (count + 1)) -
    readEnv (C.runtime initial) (actualSource initial) ((C.runtime initial).stateAt count) = _
  rw [actual_old_environment, actual_old_environment]

theorem actual_stage (count : Nat) :
    stageInventory (C.runtime initial) (actualSource initial) count =
      updateInventory (R := ℤ) (s := sort) (C.frames initial count).rawRead.environment
        ((C.frames initial (count + 1)).rawRead.environment - (C.frames initial count).rawRead.environment) := by
  unfold stageInventory
  rw [actual_old_environment, actual_increment]

theorem actual_source_read (offset bound : Nat)
    (word : Words (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))
    (index : Fin (bound + 1)) :
    readPrefix (C.runtime initial) (actualSource initial) offset bound
    ((sourceMap (C.runtime initial) (actualSource initial) offset).hom word) index =
      updateInventory (R := ℤ) (s := sort) (C.frames initial (offset + index.val)).rawRead.environment
        ((C.frames initial (offset + index.val + 1)).rawRead.environment -
          (C.frames initial (offset + index.val)).rawRead.environment) word := by
  rw [source_stage, actual_stage]

theorem actual_source_tick (count : Nat) :
    ((C.runtime initial).stateAt count).tick.nextState.engine.node.erase =
      (C.frames initial (count + 1)).currentPresentation.erase :=
  RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.actual_current initial (count + 1)

theorem mother_raw (count : Nat) :
    (Faces.Execution.Mother.inheritedMaterialFace (C.frames initial count)).rootRead.raw =
      raw (C.runtime initial) (actualSource initial) ((C.runtime initial).stateAt count) :=
  (Installation.raw_actual initial count).symm

theorem mother_next_raw (count : Nat) :
    (Faces.Execution.Mother.inheritedMaterialFace (C.frames initial count)).rootRead.nextRaw =
      raw (C.runtime initial) (actualSource initial) ((C.runtime initial).stateAt (count + 1)) :=
  (Installation.next_raw_source (C.frames initial count)).trans
    (Installation.raw_actual initial (count + 1)).symm

end SourceOperationInquiry.Context.History
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
