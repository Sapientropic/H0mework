import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Kernel.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : Context.Installation.Occurrence frame (current:=current))
variable (initial : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
abbrev runtime := Shared.runtime initial (programme seed)
theorem actual_query (count : Nat) : type_of% (Shared.actual_query initial (programme seed) count) := Shared.actual_query initial (programme seed) count
theorem actual_answer (count : Nat) : type_of% (Shared.actual_answer initial (programme seed) count) := Shared.actual_answer initial (programme seed) count
theorem actual_next (count : Nat) : type_of% (Shared.actual_next initial (programme seed) count) := Shared.actual_next initial (programme seed) count

abbrev frameAt (count : Nat) := Shared.frames initial (programme seed) count
abbrev outputAt (count : Nat) := readout seed (epoch (frameAt seed initial count))
  (Shared.actualOccurrence (frameAt seed initial count))
  (disposition seed (epoch (frameAt seed initial count)) (Shared.actualOccurrence (frameAt seed initial count)))

theorem actual_inventory (count : Nat) : type_of% (actual_updated_seed seed (frameAt seed initial count)) :=
  actual_updated_seed seed (frameAt seed initial count)

theorem actual_disposition_read (count : Nat) : type_of% (actual_disposition seed (frameAt seed initial count)) :=
  actual_disposition seed (frameAt seed initial count)

theorem actual_normal (count : Nat) : type_of% (query_value seed (frameAt seed initial count)) :=
  query_value seed (frameAt seed initial count)

theorem actual_cost (count : Nat) : type_of% (query_cost seed (frameAt seed initial count)) :=
  query_cost seed (frameAt seed initial count)


theorem full_history_preserved (first distance : Nat) :
    ∀ atom ∈ (materialFace seed (frameAt seed initial first)).rootRead.2.1.trace,
    atom ∈ (materialFace seed (frameAt seed initial (first+distance))).rootRead.2.1.trace := by
  induction distance with
  | zero => exact fun _ belongs => belongs
  | succ distance previous =>
      intro atom belongs
      have earlier := previous atom belongs
      have next := inventory_next seed (frameAt seed initial (first+distance)) atom earlier
      have index : first+(distance+1) = (first+distance)+1 := by omega
      rw [index]
      exact next


abbrev historyAt (count : Nat) := history seed (epoch (frameAt seed initial count))
  (Shared.actualOccurrence (frameAt seed initial count))

theorem all_generators_preserved (first distance : Nat) :
    (historyAt seed initial first).generatorClosure ≤ (historyAt seed initial (first+distance)).generatorClosure :=
  SourceOperationPaidRelations.generators_next _ _ _ _ (full_history_preserved seed initial first distance)

theorem all_relations_preserved (first distance : Nat) :
    (historyAt seed initial first).relationClosure ≤ (historyAt seed initial (first+distance)).relationClosure :=
  SourceOperationPaidRelations.relations_next _ _ _ _ (full_history_preserved seed initial first distance)


def RelationEvidenceAt (selected : ResidualDispositionOutcome
    (face seed (epoch frame) (Shared.actualOccurrence frame))) : Type u :=
  match selected with
  | .kernelResidual sound _ coordinate =>
      {certificate : SourceOperationScalarPresentation.RelationIndex ℤ
        (physical (epoch frame) (Shared.actualOccurrence frame)).raw.environment sort →₀ ℤ //
          SourceOperationScalarPresentation.relationMap (R:=ℤ)
            (physical (epoch frame) (Shared.actualOccurrence frame)).raw.environment certificate =
              (kernelWord seed (epoch frame) (Shared.actualOccurrence frame) sound coordinate).val}
  | other => ReadoutAt seed (epoch frame) (Shared.actualOccurrence frame) other

def relationEvidence (selected : ResidualDispositionOutcome
    (face seed (epoch frame) (Shared.actualOccurrence frame))) : RelationEvidenceAt seed frame selected :=
  match selected with
  | .kernelResidual sound _ coordinate =>
      ⟨KernelWrite.sourceCertificate seed (epoch frame) (Shared.actualOccurrence frame) sound coordinate,
       KernelWrite.sourceCertificate_read seed (epoch frame) (Shared.actualOccurrence frame) sound coordinate⟩
  | .faithful sound coverage realization => readout seed (epoch frame) (Shared.actualOccurrence frame) (.faithful sound coverage realization)
  | .unsound obstruction coordinate => readout seed (epoch frame) (Shared.actualOccurrence frame) (.unsound obstruction coordinate)
  | .coverageResidual sound obstruction coordinate => readout seed (epoch frame) (Shared.actualOccurrence frame) (.coverageResidual sound obstruction coordinate)

abbrev relationEvidenceAt (count : Nat) := relationEvidence seed (frameAt seed initial count)
  (disposition seed (epoch (frameAt seed initial count)) (Shared.actualOccurrence (frameAt seed initial count)))

abbrev generated := (runtime seed initial,outputAt seed initial,
  (fun count => transition seed (frameAt seed initial count)),relationEvidenceAt seed initial)

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
