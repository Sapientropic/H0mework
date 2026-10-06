import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.InverseConsumer
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.UpdatedFaces.Source
import H0mework.Realization.Operations.DerivationReduction
import H0mework.Realization.Perfectification.Cofinal.Topology.LivingLawRootGeneratedCofinalAllPrimeTopologyKernel
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.UpdatedFaces
open CategoryTheory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
abbrev sourceRaw := occurrenceRaw seed (epoch frame) (Shared.actualOccurrence frame)
abbrev evaluator := evaluation (R:=ℤ) (s:=sort) (sourceRaw seed frame).environment
abbrev exactComplex := SourceOperationScalarPresentation.presentationComplex (R:=ℤ) (s:=sort) (sourceRaw seed frame).environment
theorem exact_complex : (exactComplex seed frame).Exact :=
  SourceOperationScalarPresentation.presentationComplex_exact (R:=ℤ) (s:=sort) (sourceRaw seed frame).environment
def proofFace : SourceNativeRootSemanticFaceAt (Shared.root frame (installedConfiguration seed))
    (Shared.visit frame (installedConfiguration seed)) where
  projection := (installed seed frame).embed (.inr (.inr PUnit.unit))
  active := PUnit.unit
  classifier_eq := rfl
abbrev proof := (proofFace seed frame).rootRead
theorem proof_effect : (sourceRaw seed frame).expression.eval (sourceRaw seed frame).environment =
    (completed seed frame).1 := by
  have sound := SourceOperationDerivations.Derivation.sound (proof seed frame)
  exact sound.trans ((RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (Mother.baseState (epoch frame)).root.toAuthoritativeRoot (occurrenceRaw seed (epoch frame))
    (Shared.actualOccurrence frame)).symm.trans (occurrence_value seed frame))
abbrev cochain := SourceOperationScalarCochain.cochain (R:=ℤ) (s:=sort)
  (before seed frame).environment (increment seed frame)
theorem cochain_zero : (cochain seed frame).d 0 1 ≫ (cochain seed frame).d 1 2 = 0 :=
  (cochain seed frame).d_comp_d 0 1 2
abbrev fullEvidence := SourceOperationLogic.fibreDecomposition (evaluator seed frame)
theorem full_word_read (word : Formal ℤ (PairValue PhysicalValue) PhysicalVar sort) :
    (fullEvidence seed frame).symm (fullEvidence seed frame word) = word :=
  (fullEvidence seed frame).symm_apply_apply word

variable (initial : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
abbrev topology (count : Nat) := CofinalAllPrimeTopology.allStageSourceUniformity (L:=field seed initial count)
abbrev allPrime (count : Nat) := CofinalAllPrimeTopology.allPrimeMap (L:=field seed initial count)
theorem topology_residual (count : Nat) (value : field seed initial count) :
    @Inseparable (field seed initial count) (topology seed initial count).toTopologicalSpace value 0 ↔
      value ∈ LinearMap.ker (allPrime seed initial count) :=
  CofinalAllPrimeTopology.source_inseparable_zero_iff_kernel value
theorem actual_tick (count : Nat) : type_of% (Context.History.stage_receipt (inventoryRuntime seed initial) count) :=
  Context.History.stage_receipt (inventoryRuntime seed initial) count
theorem character_next (count : Nat) (word : Context.History.Words
    (PhysicalValue:=PairValue PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=sort)) :
    type_of% (Context.Faces.Cofinal.next_source (inventoryRuntime seed initial) (rawSource seed initial) count word) :=
  Context.Faces.Cofinal.next_source (inventoryRuntime seed initial) (rawSource seed initial) count word
theorem inverse_programme_source (count : Nat) : type_of%
    (Inverse.raw_next seed (Request.frameAt seed initial count)) :=
  Inverse.raw_next seed (Request.frameAt seed initial count)

abbrev generated := (Request.generated seed initial,rawSource seed initial,
  fun count => (field seed initial count,relationField seed initial count,successor seed initial count,
    topology seed initial count,allPrime seed initial count),
  fun count => (proof seed (Request.frameAt seed initial count),
    exactComplex seed (Request.frameAt seed initial count),cochain seed (Request.frameAt seed initial count),
    fullEvidence seed (Request.frameAt seed initial count)))

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.UpdatedFaces
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
