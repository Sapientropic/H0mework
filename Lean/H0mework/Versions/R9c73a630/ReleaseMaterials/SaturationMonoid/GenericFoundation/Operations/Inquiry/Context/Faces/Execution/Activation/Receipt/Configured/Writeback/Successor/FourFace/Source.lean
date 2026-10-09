import H0mework.Foundation.Responsibility.JointSource.Native.ResidualRequest
import H0mework.Realization.Operations.Execution.Relations.History.Monotone
import H0mework.Versions.MF.Realization.Perfectification.Cofinal.LivingLawRootGeneratedCofinalRelationComplexKernel
import H0mework.Versions.PR.Realization.Perfectification.LivingLawRootGeneratedUnifiedFourFaceKernel
import H0mework.Realization.Perfectification.Cofinal.Topology.LivingLawRootGeneratedCofinalAllPrimeTopologyKernel
import H0mework.Realization.Operations.CompleteWordDual
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.FourFace
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarPresentation CofinalHistorySettlement CategoryTheory SourceGeneratedScalarDifferentialResidual
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest
  (MaterialAt expression input relations relation_boundary updated_value residual_value)
end N
namespace P
export SourceOperationPaidRelations
  (exposure words complete_steps paid_boundary history prefixHistory boundary_in_inventory relations_next)
end P
namespace C
export CofinalRelationGeneratedComplex
  (natComplex relationInclusion natComplex_d_zero_one differential_sq completion_kills_generated_differential)
end C
namespace E
export UnifiedFourFace.Evaluation
  (Input generate RootEvaluation Coimage canonical embedding embedding_canonical embedding_injective)
end E
section Material
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ s, AddCommGroup (Value s)] {sort : Sorts}
variable {Nw : WorldRelationNetwork.{u}} {Voc : Vocabulary.{u}}
variable {lower : SourceNativeLedgerRootClosure Nw Voc} {current : Voc.Current}
variable {occurrence : lower.source.source.toRootSource.actual.OccurrenceAt current}
variable (material : N.MaterialAt (Value := Value) (Var := Var) (sort := sort) occurrence)

abbrev boundary : Formal ℤ Value Var sort := relationMap (R := ℤ) material.environment (N.relations (R := ℤ) material)
def sourceOccurrence := (P.exposure material.state.2).map (fun event => (occurrence, event))
abbrev history := P.prefixHistory (sourceOccurrence material) (P.exposure material.state.2)
def actualRelation : (history material).relationClosure :=
  ⟨boundary material, P.boundary_in_inventory (sourceOccurrence material) material.state.2⟩
abbrev complex := C.natComplex (history material)

theorem source_root : (sourceOccurrence material).root = (occurrence, PresentedRelationEventAt.generator material.raw) := rfl
theorem source_trace : (sourceOccurrence material).trace =
    (P.exposure material.state.2).trace.map (fun event => (occurrence, event)) :=
  SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock.mapped_trace _ _
theorem full_paid_steps : (P.words material.state.2).length = material.state.2.length := P.complete_steps _
theorem source_boundary : boundary material = Finsupp.single material.raw 1 - Finsupp.single material.state.1 1 :=
  N.relation_boundary (R := ℤ) material

theorem generated_differential :
    (((complex material).d 0 1).hom (actualRelation material)).val = boundary material := by
  rw [C.natComplex_d_zero_one]
  rfl
theorem completion_zero : (history material).completionProjection
    (((complex material).d 0 1).hom (actualRelation material)) = 0 :=
  C.completion_kills_generated_differential _ _

abbrev FullWord := Formal ℤ Value Var sort
def algebraAt (point : type_of% (sourceOccurrence material).root) :=
  (point, material, material.raw, material.state.1, N.expression material,
   SourceGeneratedCompleteWordDual.pairing (Index := Expr Value Var sort))
def combinatorialAt (point : type_of% (sourceOccurrence material).root) :=
  (point, material.state.2, P.exposure material.state.2, P.words material.state.2)
def topologicalAt (point : type_of% (sourceOccurrence material).root) :=
  (point, CofinalAllPrimeTopology.TopologicalAt.generate (history material))
def logicalAt (point : type_of% (sourceOccurrence material).root) :=
  (point, PLift.up (fun degree : Nat => C.differential_sq (history material) degree))
def relationAt (point : type_of% (sourceOccurrence material).root) :=
  (point, actualRelation material)
def cochainAt (point : type_of% (sourceOccurrence material).root) := (point, complex material)

def effectInput := ({
  occurrence := sourceOccurrence material
  algebraAt := algebraAt material
  combinatorialAt := combinatorialAt material
  topologicalAt := topologicalAt material
  logicalAt := logicalAt material
  relationAt := relationAt material
  cochainAt := cochainAt material
  evaluationAt := fun _ => evaluation (R := ℤ) (N.input material).environment
  faithfulAt := fun _ => LinearMap.id
 } : E.Input _ _ _ _ _ _ _ (Formal ℤ Value Var sort) (Value sort))
def effectFaces := E.generate (effectInput material)
def paidCoordinate := (effectFaces material).canonical (boundary material)

def wholeInput := ({
  occurrence := sourceOccurrence material
  algebraAt := algebraAt material
  combinatorialAt := combinatorialAt material
  topologicalAt := topologicalAt material
  logicalAt := logicalAt material
  relationAt := relationAt material
  cochainAt := cochainAt material
  dualEvaluationAt := fun _ => SourceGeneratedCompleteWordDual.pairing
  faithfulAt := fun _ => LinearMap.id
 } : UnifiedFourFace.Input _ _ _ _ _ _ _ (Formal ℤ Value Var sort) (Formal ℤ Value Var sort))
def wholeFaces := UnifiedFourFace.generate (wholeInput material)

theorem same_source : (effectInput material).occurrence = (wholeInput material).occurrence := rfl
theorem generated_relation : (effectFaces material).relationFace.root.2 = actualRelation material := rfl
theorem generated_cochain : (effectFaces material).cochainFace.root.2 = complex material := rfl
theorem whole_paid_trace : (wholeFaces material).combinatorialFace.root.2.1 = material.state.2 := rfl

theorem actual_inverse :
    ((effectFaces material).rangeEquiv (paidCoordinate material)).val =
      (N.expression material).eval (N.input material).environment :=
  N.residual_value (R := ℤ) material

theorem actual_effect : (effectFaces material).embedding (paidCoordinate material) =
    effectEvaluator (R := ℤ) material.environment material.increment (boundary material) := by
  have same : (effectFaces material).embedding (paidCoordinate material) =
      ((effectFaces material).rangeEquiv (paidCoordinate material)).val := rfl
  exact same.trans ((actual_inverse material).trans (N.updated_value (R := ℤ) material))

theorem differential_effect : (effectFaces material).embedding
    ((effectFaces material).canonical (((complex material).d 0 1).hom (actualRelation material)).val) =
    effectEvaluator (R := ℤ) material.environment material.increment (boundary material) := by
  rw [generated_differential]
  exact actual_effect material

theorem whole_recovery (word : Formal ℤ Value Var sort) :
    SourceGeneratedCompleteWordDual.coimageRecovery ((wholeFaces material).canonical word) = word :=
  SourceGeneratedCompleteWordDual.recovery_source word

theorem relation_recovery : SourceGeneratedCompleteWordDual.coimageRecovery
    ((wholeFaces material).canonical (boundary material)) = boundary material := whole_recovery material _

theorem native_zero_iff : paidCoordinate material = 0 ↔ (N.expression material).eval (N.input material).environment = 0 :=
  RootGeneratedDebtActivationJointSource.Native.ResidualRequest.residual_zero_iff (R := ℤ) material

end Material
end SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.FourFace
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
