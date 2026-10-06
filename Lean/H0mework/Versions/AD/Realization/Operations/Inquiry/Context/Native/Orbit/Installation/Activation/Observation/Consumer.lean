import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Runtime
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Cofinal.Consumer

/-! Physical operation words enter the existing faithful history and
character consumer through the programme's actual inherited raw family. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarRelations
open SourceOperationScalarInventoryLift SourceOperationScalarPresentation
namespace F
export SourceOperationInquiry.Context.Faces.Cofinal
  (sourceMap read read_source source_fibre next next_source fibreDecomposition
    relationAt relationField relationWitness complete_word_readback actual_receipt)
end F
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (initial : A.M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
variable (configuration : A.Programme (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))

theorem stage_actual (count : Nat) :
    Context.History.stageInventory (D.runtime initial configuration) (rawSource initial configuration) count =
      updateInventory (R := ℤ)
        (D.frames initial configuration count).rawRead.environment
        ((D.frames initial configuration (count + 1)).rawRead.environment -
          (D.frames initial configuration count).rawRead.environment) := by
  unfold Context.History.stageInventory
  rw [environment_actual, increment_actual]

theorem character_source_read (offset bound : Nat)
    (word : Formal ℤ PhysicalValue PhysicalVar sort) (index : Fin (bound + 1)) :
    F.read (D.runtime initial configuration) (rawSource initial configuration) offset bound
      (F.sourceMap (D.runtime initial configuration) (rawSource initial configuration) offset word) index =
        updateInventory (R := ℤ)
          (D.frames initial configuration (offset + index.val)).rawRead.environment
          ((D.frames initial configuration (offset + index.val + 1)).rawRead.environment -
            (D.frames initial configuration (offset + index.val)).rawRead.environment) word :=
  (F.read_source (D.runtime initial configuration) (rawSource initial configuration)
    offset bound word index).trans
      (LinearMap.congr_fun (stage_actual initial configuration (offset + index.val)) word)

theorem character_next_read (offset bound : Nat)
    (word : Formal ℤ PhysicalValue PhysicalVar sort) (index : Fin (bound + 1)) :
    F.read (D.runtime initial configuration) (rawSource initial configuration) (offset + 1) bound
      (F.next (D.runtime initial configuration) (rawSource initial configuration) offset
        (F.sourceMap (D.runtime initial configuration) (rawSource initial configuration) offset word)) index =
        updateInventory (R := ℤ)
          (D.frames initial configuration (offset + 1 + index.val)).rawRead.environment
          ((D.frames initial configuration (offset + 1 + index.val + 1)).rawRead.environment -
            (D.frames initial configuration (offset + 1 + index.val)).rawRead.environment) word := by
  rw [F.next_source]
  exact character_source_read initial configuration (offset + 1) bound word index

theorem complete_source_word (count : Nat) :
    (F.fibreDecomposition (D.runtime initial configuration) (rawSource initial configuration) count).symm
      ⟨SourceOperationLogic.q
          (F.sourceMap (D.runtime initial configuration) (rawSource initial configuration) count)
          (F.relationAt (D.runtime initial configuration) (rawSource initial configuration) count),
        F.relationWitness (D.runtime initial configuration) (rawSource initial configuration) count⟩ =
      F.relationAt (D.runtime initial configuration) (rawSource initial configuration) count :=
  F.complete_word_readback (D.runtime initial configuration) (rawSource initial configuration) count

theorem actual_source_receipt (count : Nat) :
    type_of% (F.actual_receipt (D.runtime initial configuration) count) :=
  F.actual_receipt (D.runtime initial configuration) count

end SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
