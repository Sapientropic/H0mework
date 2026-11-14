import H0mework.Versions.Rfde5c14d.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Observation.Source
import H0mework.Versions.Rfde5c14d.Realization.Operations.Inquiry.Context.Faces.Cofinal.Consumer

/-! All actual prefixes of the newly activated source query retain the
original physical environment, complete word fibre and typed macro receipt.
The character inverse consumes the same generated history, including birth. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.Observation
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarInventoryLift
namespace H
export SourceOperationInquiry.Context.History (Words stageInventory)
end H
namespace F
export SourceOperationInquiry.Context.Faces.Cofinal
  (sourceMap read read_source source_fibre next next_source fibreDecomposition)
end F
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (initial : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

theorem environment_actual (count : Nat) :
    readEnv (A.runtime initial) (rawSource initial) ((A.runtime initial).stateAt count) =
      (A.frames initial count).rawRead.environment :=
  congrArg (fun raw => raw.environment) (raw_actual initial count)

theorem increment_actual (count : Nat) :
    increment (A.runtime initial) (rawSource initial) ((A.runtime initial).stateAt count) =
      (A.frames initial (count + 1)).rawRead.environment - (A.frames initial count).rawRead.environment := by
  change readEnv (A.runtime initial) (rawSource initial) ((A.runtime initial).stateAt (count + 1)) -
    readEnv (A.runtime initial) (rawSource initial) ((A.runtime initial).stateAt count) = _
  rw [environment_actual, environment_actual]

theorem stage_actual (count : Nat) : H.stageInventory (A.runtime initial) (rawSource initial) count =
    updateInventory (R := ℤ) (s := sort) (A.frames initial count).rawRead.environment
      ((A.frames initial (count + 1)).rawRead.environment - (A.frames initial count).rawRead.environment) := by
  unfold H.stageInventory
  rw [environment_actual, increment_actual]

def character (offset : Nat) := F.sourceMap (A.runtime initial) (rawSource initial) offset

theorem character_read (offset bound : Nat) (word : H.Words (PhysicalValue := PhysicalValue)
    (PhysicalVar := PhysicalVar) (sort := sort)) (index : Fin (bound + 1)) :
    F.read (A.runtime initial) (rawSource initial) offset bound (character initial offset word) index =
      updateInventory (R := ℤ) (s := sort) (A.frames initial (offset + index.val)).rawRead.environment
        ((A.frames initial (offset + index.val + 1)).rawRead.environment -
          (A.frames initial (offset + index.val)).rawRead.environment) word :=
  (F.read_source (A.runtime initial) (rawSource initial) offset bound word index).trans
    (LinearMap.congr_fun (stage_actual initial (offset + index.val)) word)

theorem character_fibre (offset : Nat) (left right : H.Words (PhysicalValue := PhysicalValue)
    (PhysicalVar := PhysicalVar) (sort := sort)) :
    character initial offset left = character initial offset right ↔
      ∀ bound (index : Fin (bound + 1)), liftMap (R := ℤ) (left - right) ∈ LinearMap.range
        (SourceOperationScalarPresentation.relationMap (R := ℤ)
          (pairEnvironment (A.frames initial (offset + index.val)).rawRead.environment
            ((A.frames initial (offset + index.val + 1)).rawRead.environment -
              (A.frames initial (offset + index.val)).rawRead.environment))) := by
  rw [character, F.source_fibre]
  constructor
  · intro same bound index
    have atStage := same bound index
    change liftMap (R := ℤ) (left - right) ∈ LinearMap.range
      (SourceOperationScalarPresentation.relationMap (R := ℤ)
        (pairEnvironment (readEnv (A.runtime initial) (rawSource initial) ((A.runtime initial).stateAt (offset + index.val)))
          (increment (A.runtime initial) (rawSource initial) ((A.runtime initial).stateAt (offset + index.val))))) at atStage
    rw [environment_actual initial, increment_actual initial] at atStage
    exact atStage
  · intro same bound index
    change liftMap (R := ℤ) (left - right) ∈ LinearMap.range
      (SourceOperationScalarPresentation.relationMap (R := ℤ)
        (pairEnvironment (readEnv (A.runtime initial) (rawSource initial) ((A.runtime initial).stateAt (offset + index.val)))
          (increment (A.runtime initial) (rawSource initial) ((A.runtime initial).stateAt (offset + index.val)))))
    rw [environment_actual initial, increment_actual initial]
    exact same bound index

def wordWitness (offset : Nat) (word : H.Words (PhysicalValue := PhysicalValue)
    (PhysicalVar := PhysicalVar) (sort := sort)) := SourceOperationLogic.sourceWitness (character initial offset) word

theorem word_readback (offset : Nat) (word : H.Words (PhysicalValue := PhysicalValue)
    (PhysicalVar := PhysicalVar) (sort := sort)) :
    (F.fibreDecomposition (A.runtime initial) (rawSource initial) offset).symm
      ⟨SourceOperationLogic.q (character initial offset) word, wordWitness initial offset word⟩ = word := rfl

theorem character_next_read (offset bound : Nat) (word : H.Words (PhysicalValue := PhysicalValue)
    (PhysicalVar := PhysicalVar) (sort := sort)) (index : Fin (bound + 1)) :
    F.read (A.runtime initial) (rawSource initial) (offset + 1) bound
      (F.next (A.runtime initial) (rawSource initial) offset (character initial offset word)) index =
      updateInventory (R := ℤ) (s := sort) (A.frames initial (offset + 1 + index.val)).rawRead.environment
        ((A.frames initial (offset + 1 + index.val + 1)).rawRead.environment -
          (A.frames initial (offset + 1 + index.val)).rawRead.environment) word := by
  rw [character, F.next_source]
  exact character_read initial (offset + 1) bound word index

theorem actual_operation (count : Nat) :
    type_of% (Context.actual_operation_receipt (A.runtime initial) (rawSource initial)
      ((A.runtime initial).stateAt count)) :=
  Context.actual_operation_receipt (A.runtime initial) (rawSource initial) ((A.runtime initial).stateAt count)

def materialInstallation (frame : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)) :=
  (SourceNativeProjectionLaw.InstallationAt.componentCoface frame.currentState.root.source.base
    (SourceOperationInquiry.Context.Installation.component (A.epoch frame))).trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (A.base frame).root.source.base (A.queryLaw frame)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (A.queryRoot frame).source.base (A.resultLaw frame)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (A.resultRoot frame).source.base (A.consumerLaw frame)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (A.consumerRoot frame).source.base (A.compilationLaw frame))

def materialFace (frame : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)) :
    SourceNativeRootSemanticFaceAt (A.root frame) (A.visit frame) where
  projection := (materialInstallation frame).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem material_read (count : Nat) : (materialFace (A.frames initial count)).rootRead.raw =
    Context.raw (A.runtime initial) (rawSource initial) ((A.runtime initial).stateAt count) :=
  (raw_actual initial count).symm

theorem material_next_raw (count : Nat) :
    (materialFace (A.frames initial count)).rootRead.nextRaw = Context.raw (A.runtime initial) (rawSource initial) ((A.runtime initial).stateAt (count + 1)) :=
  (next_raw (A.frames initial count)).trans (raw_actual initial (count + 1)).symm

end SourceOperationInquiry.Context.Faces.Execution.Activation.Observation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
