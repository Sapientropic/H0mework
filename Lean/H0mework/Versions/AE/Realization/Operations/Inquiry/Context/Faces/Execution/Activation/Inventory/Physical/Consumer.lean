import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Physical.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Physical
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
open SourceOperationScalarRelations SourceOperationScalarInventoryLift
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (initial : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
theorem word_read (count bound : Nat) (index : Fin (bound+1)) :
    Context.Faces.Cofinal.read (runtime seed initial) (source seed initial) count bound (wordField seed initial count) index =
      updateInventory (R:=ℤ)
        (frameAt seed initial (count+index.val)).rawRead.environment
        ((frameAt seed initial (count+index.val+1)).rawRead.environment -
          (frameAt seed initial (count+index.val)).rawRead.environment) (actualWord seed initial count) :=
  O.character_source_read initial (programme seed) count bound (actualWord seed initial count) index

theorem word_next_read (count bound : Nat) (index : Fin (bound+1)) :
    Context.Faces.Cofinal.read (runtime seed initial) (source seed initial) (count+1) bound
      (fieldNext seed initial count (wordField seed initial count)) index =
      updateInventory (R:=ℤ)
        (frameAt seed initial (count+1+index.val)).rawRead.environment
        ((frameAt seed initial (count+1+index.val+1)).rawRead.environment -
          (frameAt seed initial (count+1+index.val)).rawRead.environment) (actualWord seed initial count) :=
  O.character_next_read initial (programme seed) count bound (actualWord seed initial count) index

theorem word_complete (count : Nat) :
    (Context.Faces.Cofinal.fibreDecomposition (runtime seed initial) (source seed initial) count).symm
      ⟨SourceOperationLogic.q (fieldSource seed initial count) (actualWord seed initial count),wordWitness seed initial count⟩ =
        actualWord seed initial count := rfl

theorem receipt (count : Nat) : type_of% (O.actual_source_receipt initial (programme seed) count) :=
  O.actual_source_receipt initial (programme seed) count



theorem word_field_zero_iff (count : Nat) : wordField seed initial count = 0 ↔
    ∀ bound (index : Fin (bound+1)), updateInventory (R:=ℤ)
      (frameAt seed initial (count+index.val)).rawRead.environment
      ((frameAt seed initial (count+index.val+1)).rawRead.environment -
        (frameAt seed initial (count+index.val)).rawRead.environment) (actualWord seed initial count) = 0 := by
  constructor
  · intro zero bound index
    have actual := congrArg (fun value => Context.Faces.Cofinal.read
      (runtime seed initial) (source seed initial) count bound value index) zero
    rw [word_read, map_zero, Pi.zero_apply] at actual
    exact actual
  · intro zero
    have fibre := (Context.History.fibre (runtime seed initial) (source seed initial) count
      (actualWord seed initial count) 0).mpr (by
        intro bound index
        have generated := O.stage_actual initial (programme seed) (count+index.val)
        have atStage := LinearMap.congr_fun generated (actualWord seed initial count)
        exact (atStage.trans (zero bound index)).trans (map_zero _).symm)
    have current : (Context.History.sourceMap (runtime seed initial) (source seed initial) count).hom
        (actualWord seed initial count) = 0 := fibre.trans (map_zero _)
    exact (congrArg (Context.Faces.Cofinal.E.canonicalMap ℤ (fullHistory seed initial count)) current).trans (map_zero _)

theorem full_fibre (count : Nat) (left right : Formal ℤ PhysicalValue PhysicalVar sort) :
    type_of% (Context.Faces.Cofinal.source_fibre (runtime seed initial) (source seed initial) count left right) :=
  Context.Faces.Cofinal.source_fibre _ _ _ _ _

theorem relation_action (state : (runtime seed initial).State)
    (relations : SourceOperationScalarPresentation.RelationIndex ℤ
      (Context.Native.Orbit.environment (runtime seed initial) (source seed initial)
        (SourceOperationInquiry.point (runtime seed initial) state.tick.nextState)) sort →₀ ℤ) :
    type_of% (Context.Native.Orbit.actual_relation_update (runtime seed initial) (source seed initial) state relations) :=
  Context.Native.Orbit.actual_relation_update _ _ _ _

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Physical
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
