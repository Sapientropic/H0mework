import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Execution.Consumer
import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Consumer
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Faces.Fibre
import H0mework.Realization.HistoryTopology.Carrier

/-! The charged source face supplies its complete relation coefficients,
execution receipts and normal result to the existing independent consumers.
The mathematical write and the mother write retain their own worlds. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution.Faces
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceOperationScalarInventoryLift
open SourceOperationLogic SourceGeneratedScalarDifferentialResidual
namespace E
export SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution
  (face chargedProgramme runtime frames receipts stageState payment no_refill actual_answer actual_next actualResult
   actual_result settled_value stage_clock charged_write_receipt result_state_receipt material_stage_read)
end E
namespace O
export SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation
  (rawSource character_source_read character_next_read complete_source_word actual_source_receipt)
end O
namespace I
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (source_value)
end I
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (baseRoot datum actualOccurrence)
end S
namespace A
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end A
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : A.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

abbrev material := (E.face frame).rootRead.1
abbrev pairMap := updateInventory (R := ℤ) (s := sort) (material frame).environment
  ((material frame).nextEnvironment - (material frame).environment)
abbrev sourceWord := relationMap (R := ℤ) (material frame).environment (material frame).actedProgramme

def sourceComplex := SourceSubstitution.complexMorphism (R := ℤ) (s := sort)
  SourceOperationInquiry.Context.Native.Orbit.binding (material frame).environment

theorem source_complex :
    (presentationComplex (R := ℤ) (s := sort) (material frame).environment).Exact ∧
    type_of% (sourceComplex frame).comm₁₂ ∧ type_of% (sourceComplex frame).comm₂₃ :=
  ⟨presentationComplex_exact (R := ℤ) (material frame).environment,
    (sourceComplex frame).comm₁₂, (sourceComplex frame).comm₂₃⟩

abbrev ProgrammeEvidence (word : Formal ℤ PhysicalValue (Orbit.Var PhysicalVar) sort) :=
  {programme : RelationIndex ℤ (material frame).environment sort →₀ ℤ //
    relationMap (R := ℤ) (material frame).environment programme = word}

def retainedProgramme : ExistsEvidence (pairMap frame) (ProgrammeEvidence frame)
    (q (pairMap frame) (sourceWord frame)) :=
  retainEvidence (pairMap frame) ⟨(material frame).actedProgramme, rfl⟩

theorem recover_programme :
    (existsEvidenceElim (pairMap frame) (ProgrammeEvidence frame))
      ⟨q (pairMap frame) (sourceWord frame), retainedProgramme frame⟩ =
        ⟨sourceWord frame, ⟨(material frame).actedProgramme, rfl⟩⟩ := rfl

theorem source_cochain : SourceOperationScalarCochain.boundary (R := ℤ) (sourceWord frame) ∈
    LinearMap.range (relationMap (R := ℤ) (mixedEnvironment (material frame).environment
      ((material frame).nextEnvironment - (material frame).environment))) :=
  update_boundary_has_source_relations (material frame).environment
    ((material frame).nextEnvironment - (material frame).environment) (sourceWord frame)

theorem updated_inverse :
    (residualEquivRange (evaluation (R := ℤ) ((material frame).environment +
      ((material frame).nextEnvironment - (material frame).environment)))
      (canonicalResidual (evaluation (R := ℤ) ((material frame).environment +
        ((material frame).nextEnvironment - (material frame).environment))) (sourceWord frame))).val =
      effectEvaluator (R := ℤ) (material frame).environment
        ((material frame).nextEnvironment - (material frame).environment) (sourceWord frame) :=
  old_relation_updated_residual _ _ _
    (LinearMap.congr_fun (evaluation_relationMap (R := ℤ) (material frame).environment)
      (material frame).actedProgramme)

theorem normal_pair : (E.actualResult frame).2.2.1 = pairMap frame (sourceWord frame) := by
  apply (I.source_value (S.baseRoot frame E.chargedProgramme).toAuthoritativeRoot
    ((S.datum frame E.chargedProgramme).reader) (S.actualOccurrence frame)).trans
  exact SourceOperationInquiry.Context.Native.Orbit.Installation.Relations.pair_eval
    (SourceOperationInquiry.Context.Native.Orbit.Installation.ofFrame frame)

/-- A dependent consumer reads the exact coefficient programme, its generated
normal pair and original stage payment without selecting another source. -/
def consume (Result : Type*)
    (atSource : (programme : ProgrammeEvidence frame (sourceWord frame)) →
      (value : PhysicalValue sort × PhysicalValue sort) → value = pairMap frame (sourceWord frame) →
      (count : Fin (remaining (E.receipts frame).raw.expression + 1)) →
      type_of% (E.payment frame count) → type_of% (updated_inverse frame) →
      type_of% (E.material_stage_read frame count) → type_of% (E.stage_clock frame count) →
      type_of% (E.result_state_receipt frame) → Result)
    (count : Fin (remaining (E.receipts frame).raw.expression + 1)) : Result :=
  let recovered := existsEvidenceElim (pairMap frame) (ProgrammeEvidence frame)
    ⟨q (pairMap frame) (sourceWord frame), retainedProgramme frame⟩
  atSource (show ProgrammeEvidence frame (sourceWord frame) from recovered.2)
    (E.actualResult frame).2.2.1 (normal_pair frame) count (E.payment frame count)
      (updated_inverse frame) (E.material_stage_read frame count) (E.stage_clock frame count)
      (E.result_state_receipt frame)

variable (initial : A.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

theorem character_read (offset bound : Nat) (word : Formal ℤ PhysicalValue PhysicalVar sort)
    (index : Fin (bound + 1)) :
    type_of% (O.character_source_read initial E.chargedProgramme offset bound word index) :=
  O.character_source_read initial E.chargedProgramme offset bound word index

theorem character_next (offset bound : Nat) (word : Formal ℤ PhysicalValue PhysicalVar sort)
    (index : Fin (bound + 1)) :
    type_of% (O.character_next_read initial E.chargedProgramme offset bound word index) :=
  O.character_next_read initial E.chargedProgramme offset bound word index

abbrev historyData (offset : Nat) := Context.History.data
  (E.runtime initial) (O.rawSource initial E.chargedProgramme) offset
abbrev historyCompatible (offset : Nat) := Context.History.compatible
  (E.runtime initial) (O.rawSource initial E.chargedProgramme) offset

theorem source_topology (offset : Nat) :
    type_of% (SourceGeneratedScalarCofinalTopology.coordinates_isUniformEmbedding
      (historyData initial offset) (historyCompatible initial offset)) ∧
    type_of% (SourceGeneratedScalarCofinalTopology.completion_complete
      (historyData initial offset) (historyCompatible initial offset)) :=
  ⟨SourceGeneratedScalarCofinalTopology.coordinates_isUniformEmbedding
      (historyData initial offset) (historyCompatible initial offset),
    SourceGeneratedScalarCofinalTopology.completion_complete
      (historyData initial offset) (historyCompatible initial offset)⟩

theorem whole_word (count : Nat) : type_of% (O.complete_source_word initial E.chargedProgramme count) :=
  O.complete_source_word initial E.chargedProgramme count

theorem reverse_fibre (count : Nat) :
    Function.Injective (Context.Faces.recover (E.runtime initial) (O.rawSource initial E.chargedProgramme)
      ((E.runtime initial).stateAt count)) :=
  Context.Faces.recover_injective (E.runtime initial) (O.rawSource initial E.chargedProgramme)
    ((E.runtime initial).stateAt count)

theorem actual_answer_next (count : Nat) :
    type_of% (E.actual_answer initial count) ∧ type_of% (E.actual_next initial count) ∧
      type_of% (O.actual_source_receipt initial E.chargedProgramme count) :=
  ⟨E.actual_answer initial count, E.actual_next initial count,
    O.actual_source_receipt initial E.chargedProgramme count⟩

end SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution.Faces
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
