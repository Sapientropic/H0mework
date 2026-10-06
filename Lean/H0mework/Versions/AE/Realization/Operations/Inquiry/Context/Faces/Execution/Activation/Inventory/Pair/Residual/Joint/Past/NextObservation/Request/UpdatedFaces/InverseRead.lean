import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.UpdatedFaces.Consumer
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Reverse.Consumer
import H0mework.Realization.Operations.Execution.Coefficients.Words
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.UpdatedFaces.InverseRead
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift CofinalHistorySettlement
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (initial : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
abbrev actual (count : Nat) := (inventoryRuntime seed initial).stateAt count
abbrev localFrame (count : Nat) := Request.frameAt seed initial count
abbrev nextWord (count : Nat) := Context.Faces.Reverse.nextWord (inventoryRuntime seed initial) (rawSource seed initial)
  (actual seed initial count)
abbrev installedResult (count : Nat) := Inverse.sourceResult seed (localFrame seed initial count)

theorem next_environment (count : Nat) : Context.readEnv (inventoryRuntime seed initial) (rawSource seed initial)
    (actual seed initial count).tick.nextState =
      Inverse.nextEnvironment (epoch (localFrame seed initial count))
        (Shared.actualOccurrence (localFrame seed initial count)) := by
  have actualRaw := raw_actual seed initial (count+1)
  have generated := Inverse.next_environment_actual seed (localFrame seed initial count) (installedConfiguration seed) rfl rfl
  exact (congrArg (fun raw => raw.environment) actualRaw).trans generated.symm

theorem installed_expression (count : Nat) : (installedResult seed initial count).2.1.1 =
    Expr.const ((Context.raw (inventoryRuntime seed initial) (rawSource seed initial)
      (actual seed initial count)).expression.eval
      (Context.readEnv (inventoryRuntime seed initial) (rawSource seed initial) (actual seed initial count).tick.nextState)) := by
  have final := RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.target_expression
    (Mother.baseState (epoch (localFrame seed initial count))).root.toAuthoritativeRoot
    (Shared.actualVisit (localFrame seed initial count)).current
    (fun _ => Inverse.reader seed (epoch (localFrame seed initial count))
      (Shared.actualOccurrence (localFrame seed initial count)))
  have aligned : Inverse.sourceResult seed (localFrame seed initial count) =
      Inverse.result seed (epoch (localFrame seed initial count))
        (Shared.actualOccurrence (localFrame seed initial count)) := rfl
  change (Inverse.result seed (epoch (localFrame seed initial count))
    (Shared.actualOccurrence (localFrame seed initial count))).2.1.1 = _
  have value : RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value
      (Mother.baseState (epoch (localFrame seed initial count))).root.toAuthoritativeRoot
      (Shared.actualVisit (localFrame seed initial count)).current
      (fun _ => Inverse.reader seed (epoch (localFrame seed initial count))
        (Shared.actualOccurrence (localFrame seed initial count))) =
      (occurrenceRaw seed (epoch (localFrame seed initial count))
        (Shared.actualOccurrence (localFrame seed initial count))).expression.eval
          (Inverse.nextEnvironment (epoch (localFrame seed initial count))
            (Shared.actualOccurrence (localFrame seed initial count))) :=
    RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source _ _ _
  have read := (congrArg₂ (fun raw environment => raw.expression.eval environment)
    (raw_actual seed initial count).symm (next_environment seed initial count).symm)
  exact final.trans (congrArg Expr.const (value.trans read))
abbrev sourceWord (count : Nat) := relationMap (R:=ℤ)
  (Inverse.nextEnvironment (epoch (localFrame seed initial count)) (Shared.actualOccurrence (localFrame seed initial count)))
  (Inverse.result seed (epoch (localFrame seed initial count))
    (Shared.actualOccurrence (localFrame seed initial count))).2.1.2.relationWords

theorem same_word (count : Nat) : sourceWord seed initial count = nextWord seed initial count := by
  have generated := Inverse.generated_boundary seed (epoch (localFrame seed initial count))
    (Shared.actualOccurrence (localFrame seed initial count))
  have endpoint := installed_expression seed initial count
  have sourceExpr := congrArg (fun raw => Finsupp.single raw.expression (1:ℤ)) (raw_actual seed initial count).symm
  have targetExpr := congrArg (fun expression => Finsupp.single expression (1:ℤ)) endpoint
  exact generated.trans ((congrArg₂ (· - ·) sourceExpr targetExpr).trans
    (Context.Faces.Reverse.source_boundary (inventoryRuntime seed initial) (rawSource seed initial)
      (actual seed initial count)).symm)

abbrev reverse (count : Nat) := Context.Faces.Reverse.reverse (inventoryRuntime seed initial) (rawSource seed initial)
  (actual seed initial count)
abbrev target (count : Nat) := Context.Faces.Reverse.target (inventoryRuntime seed initial) (rawSource seed initial)
  (actual seed initial count)
theorem full_target (count : Nat) : (target seed initial count).val =
    Context.Faces.Reverse.oldWord (inventoryRuntime seed initial) (rawSource seed initial)
      (actual seed initial count) + sourceWord seed initial count :=
  congrArg (_ + ·) (same_word seed initial count).symm
theorem full_reverse (count : Nat) : Context.Faces.recover (inventoryRuntime seed initial) (rawSource seed initial)
    (actual seed initial count) (reverse seed initial count) =
      Context.Faces.pairInventory (inventoryRuntime seed initial) (rawSource seed initial)
        (actual seed initial count) (sourceWord seed initial count) :=
  (Context.Faces.Reverse.reverse_recover (inventoryRuntime seed initial) (rawSource seed initial)
    (actual seed initial count)).trans (congrArg
      (Context.Faces.pairInventory (inventoryRuntime seed initial) (rawSource seed initial) (actual seed initial count))
      (same_word seed initial count).symm)
abbrev programme (count : Nat) := Context.Faces.Execution.pairRaw (inventoryRuntime seed initial) (rawSource seed initial)
  (actual seed initial count) (sourceWord seed initial count)
abbrev execution (count : Nat) := Context.Faces.Execution.initialRuntime (inventoryRuntime seed initial) (rawSource seed initial)
  (actual seed initial count) (sourceWord seed initial count)
theorem source_execution (count : Nat) : Context.Faces.Execution.value (inventoryRuntime seed initial) (rawSource seed initial)
    (actual seed initial count) (sourceWord seed initial count) =
      Context.Faces.recover (inventoryRuntime seed initial) (rawSource seed initial) (actual seed initial count)
        (reverse seed initial count) :=
  (Context.Faces.Execution.value_pair (inventoryRuntime seed initial) (rawSource seed initial)
    (actual seed initial count) (sourceWord seed initial count)).trans (full_reverse seed initial count).symm
theorem execution_whole (count : Nat) : type_of% (Context.Faces.Execution.actual_whole
    (inventoryRuntime seed initial) (rawSource seed initial) (actual seed initial count) (sourceWord seed initial count)) :=
  Context.Faces.Execution.actual_whole (inventoryRuntime seed initial) (rawSource seed initial)
    (actual seed initial count) (sourceWord seed initial count)
theorem execution_cost (count : Nat) : type_of% (Context.Faces.Execution.trace_cost
    (inventoryRuntime seed initial) (rawSource seed initial) (actual seed initial count) (sourceWord seed initial count)) :=
  Context.Faces.Execution.trace_cost (inventoryRuntime seed initial) (rawSource seed initial)
    (actual seed initial count) (sourceWord seed initial count)
theorem execution_original (count : Nat) : type_of% (Context.Faces.Execution.original_occurrence
    (inventoryRuntime seed initial) (rawSource seed initial) (actual seed initial count) (sourceWord seed initial count)) :=
  Context.Faces.Execution.original_occurrence (inventoryRuntime seed initial) (rawSource seed initial)
    (actual seed initial count) (sourceWord seed initial count)
theorem execution_next (count : Nat) : type_of% (Context.Faces.Execution.actual_tick
    (inventoryRuntime seed initial) (rawSource seed initial) (actual seed initial count) (sourceWord seed initial count)) :=
  Context.Faces.Execution.actual_tick (inventoryRuntime seed initial) (rawSource seed initial)
    (actual seed initial count) (sourceWord seed initial count)

abbrev generated := (UpdatedFaces.generated seed initial,
  fun count => (sourceWord seed initial count,target seed initial count,reverse seed initial count,
    programme seed initial count,execution seed initial count))

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.UpdatedFaces.InverseRead
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
