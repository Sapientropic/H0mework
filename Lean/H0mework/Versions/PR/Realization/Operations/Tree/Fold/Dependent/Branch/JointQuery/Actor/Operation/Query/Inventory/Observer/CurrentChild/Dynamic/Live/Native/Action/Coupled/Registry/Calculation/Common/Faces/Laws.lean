import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Source
import H0mework.Realization.Operations.Execution.Relations.History.Laws
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Faces.Fibre
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Perfect.Kernel
import H0mework.Realization.Perfectification.Cofinal.Topology.LivingLawRootGeneratedCofinalAllPrimeTopologyKernel
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower
open CategoryTheory RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation
variable {S : Type u} {W X : S → Type u} [∀ slot,AddCommGroup (W slot)] {s : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=W) (Var:=X) (sort:=s))
variable (cfg : E.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : I.Occurrence frame (current:=current))
def queryLogic := SourceOperationLogic.fibreDecomposition (evaluation (R:=ℤ) (s:=s) (raw frame cfg supplied).environment)
def sourceCochain := SourceOperationScalarCochain.cochain (R:=ℤ) (s:=s)
 (I.materialAt frame supplied).raw.environment
 ((I.materialAt frame supplied).nextRaw.environment-(I.materialAt frame supplied).raw.environment)
theorem source_cochain_zero : (sourceCochain frame supplied).d 0 1 ≫ (sourceCochain frame supplied).d 1 2=0 :=
 (sourceCochain frame supplied).d_comp_d 0 1 2
theorem complete_word_recovery (word : wordCarrier cfg) :
 SourceGeneratedCompleteWordDual.coimageRecovery
 (SourceGeneratedPerfectification.canonicalMap (pairing cfg) word)=word :=
 SourceGeneratedCompleteWordDual.recovery_source word

theorem actual_trace_cost : (trace frame cfg supplied).length=remaining (raw frame cfg supplied).expression := execution_length _ _
theorem actual_relation_sound : evaluation (R:=ℤ) (raw frame cfg supplied).environment
 (relationMap (R:=ℤ) (raw frame cfg supplied).environment ((trace frame cfg supplied).relationWords (R:=ℤ)))=0 :=
 (trace frame cfg supplied).relation_old (R:=ℤ)
theorem physical_source_update : (I.materialAt frame supplied).pair=
 ((I.materialAt frame supplied).raw.expression.eval (I.materialAt frame supplied).raw.environment,
 (I.materialAt frame supplied).raw.expression.effect (I.materialAt frame supplied).raw.environment
 ((I.materialAt frame supplied).nextRaw.environment-(I.materialAt frame supplied).raw.environment)) :=
 SourceOperationInquiry.Context.Installation.pair_value frame supplied

namespace Elimination
abbrev Packet := type_of% (material frame cfg supplied)
variable (packet : Packet frame cfg supplied)
abbrev packetRaw := packet.2.2.1
abbrev packetTrace := packet.2.2.2.1
abbrev packetPhysical := packet.2.1
abbrev packetPairing := packet.2.2.2.2.2.2.1
abbrev packetBoundary := packet.2.2.2.2.2.2.2

def history := SourceOperationPaidRelations.history (RootedAccountedUnfolding.zero packet.1)
 (packetTrace frame cfg supplied packet)
def topology := CofinalAllPrimeTopology.TopologicalAt.generate (history frame cfg supplied packet)
def logical := SourceOperationLogic.fibreDecomposition
 (evaluation (R:=ℤ) (s:=s) (packetRaw frame cfg supplied packet).environment)
def faithful := SourceOperationPaidRelations.face (RootedAccountedUnfolding.zero packet.1)
 (packetTrace frame cfg supplied packet)
def cochain := SourceOperationScalarCochain.cochain (R:=ℤ) (s:=s)
 (packetPhysical frame cfg supplied packet).raw.environment
 ((packetPhysical frame cfg supplied packet).nextRaw.environment-(packetPhysical frame cfg supplied packet).raw.environment)
def relationAction : (history frame cfg supplied packet).relationClosure →ₗ[ℤ]
 (history frame cfg supplied packet).generatorClosure :=
 Submodule.inclusion (history frame cfg supplied packet).relationClosure_le_generatorClosure

abbrev AlgebraFace := Packet frame cfg supplied × (wordCarrier cfg →ₗ[ℤ] Module.Dual ℤ (wordCarrier cfg))
abbrev CombinatorialFace := Σ original : Packet frame cfg supplied, type_of% (history frame cfg supplied original)
abbrev TopologicalFace := Σ original : Packet frame cfg supplied, type_of% (topology frame cfg supplied original)
abbrev LogicalFace := Σ original : Packet frame cfg supplied, type_of% (logical frame cfg supplied original)
abbrev RelationFace := Σ original : Packet frame cfg supplied,
 (type_of% (faithful frame cfg supplied original)) × (type_of% (relationAction frame cfg supplied original))
abbrev CochainFace := Σ original : Packet frame cfg supplied, type_of% (cochain frame cfg supplied original)
def faceInput := ({
 occurrence:=RootedAccountedUnfolding.zero packet
 algebraAt:=fun original => (original,packetPairing frame cfg supplied original)
 combinatorialAt:=fun original => ⟨original,history frame cfg supplied original⟩
 topologicalAt:=fun original => ⟨original,topology frame cfg supplied original⟩
 logicalAt:=fun original => ⟨original,logical frame cfg supplied original⟩
 relationAt:=fun original => ⟨original,faithful frame cfg supplied original,relationAction frame cfg supplied original⟩
 cochainAt:=fun original => ⟨original,cochain frame cfg supplied original⟩
 dualEvaluationAt:=fun original => packetPairing frame cfg supplied original
 faithfulAt:=fun _ => LinearMap.id } : UnifiedFourFace.Input (Packet frame cfg supplied) (AlgebraFace frame cfg supplied)
 (CombinatorialFace frame cfg supplied) (TopologicalFace frame cfg supplied) (LogicalFace frame cfg supplied)
 (RelationFace frame cfg supplied) (CochainFace frame cfg supplied) (wordCarrier cfg) (wordCarrier cfg))
def fourFaces := UnifiedFourFace.generate (faceInput frame cfg supplied packet)
theorem dual_readback : type_of% (UnifiedFourFace.generated_dual_readback (faceInput frame cfg supplied packet)) :=
 UnifiedFourFace.generated_dual_readback _
theorem original_root : (faceInput frame cfg supplied packet).occurrence.root=packet := rfl
end Elimination

def actual_faces := Elimination.fourFaces (E.epoch frame) cfg (E.S.actualOccurrence frame) (face frame cfg).rootRead
theorem actual_dual_readback : type_of% (Elimination.dual_readback
 (E.epoch frame) cfg (E.S.actualOccurrence frame) (face frame cfg).rootRead) := Elimination.dual_readback _ _ _ _
theorem source_boundary_equation :
 (evaluation (R:=ℤ) (s:=s) (mixedEnvironment (I.materialAt frame supplied).raw.environment
 ((I.materialAt frame supplied).nextRaw.environment-(I.materialAt frame supplied).raw.environment))).comp
 (SourceOperationScalarCochain.boundary (R:=ℤ) (Value:=W) (Var:=X) (s:=s))=0 :=
 SourceOperationScalarCochain.evaluation_boundary (R:=ℤ) _ _
theorem installed_boundary_equation :
 (evaluation (R:=ℤ) (s:=s) (mixedEnvironment (face frame cfg).rootRead.2.1.raw.environment
 ((face frame cfg).rootRead.2.1.nextRaw.environment-(face frame cfg).rootRead.2.1.raw.environment))).comp
 (face frame cfg).rootRead.2.2.2.2.2.2.2=0 := SourceOperationScalarCochain.evaluation_boundary (R:=ℤ) _ _

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
