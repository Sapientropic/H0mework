import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower
 (Value groups)
end L
namespace SF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily
 (Factory Seed Packet cfg defaultFactory)
end SF
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (AdmissionPacket nativeAfterAdmission bornAfterNative nextSeed nextBase stockCfg generatedPairStock localNativeReceipt admissionPresentation)
end AS
namespace AI
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation
 (withActualInput)
end AI
namespace Admissions
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
 (packetAt packetAt_successor actual_index index sourceRuntime history_end_index)
end Admissions
namespace T
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock
 (preserve)
end T
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (next nextBorn actualOccurrence runtime frames)
namespace Complete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion
 (receipt atReceipt receipt_compiles receipt_next)
end Complete
end S
namespace PR
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual
 (raw pairInventory priorPairInventory liftedInventory)
end PR
namespace J
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint
 (history face disposition kernelWord queryRaw queryReader queryResult kernel_word_read kernel_word_value complete_query_trace coverage_query_value)
namespace Past
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past
 (written current_written_preserved)
namespace I
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.InventoryTransport
 (bornHistory currentHistory completionTransition OutputAt output born_kernel_member born_kernel_zero)
end I
end Past
end J

private theorem preserve_generated {α : Type u} (prior : Option (RootedAccountedUnfolding α))
 (generated : RootedAccountedUnfolding α) (event : α) (present : event ∈ generated.trace) :
 event ∈ (T.preserve prior generated).trace := by
 cases prior with
 | none => exact present
 | some prior => exact (SourceHistoryCommon.parallel_right _ _ _).1 event present

section Source
variable {W X : Unit → Type} [∀ target,AddCommGroup (W target)]
local instance writerGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value W grade target) := L.groups W grade

-- The witness is the installed programme seed, recovered before birth augments packet.data.2.
def InstalledWriter (grade : Nat)
 (programme : A.Programme (PhysicalValue:=L.Value W grade) (PhysicalVar:=X) (sort:=()))
 (seed : SF.Seed W X () grade) : Prop :=
 ∀ currentFrame : A.M.Frame (Value:=L.Value W grade) (Var:=X) (sort:=()),
 ∃ carried : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (L.Value W grade)) X ())),
  programme.nextPairInventory currentFrame = some carried ∧
  ∀ event ∈ (J.Past.written seed currentFrame).trace,event ∈ carried.trace

variable (code : Expr (PairValue W) X ())

theorem factory_cfg_installed (grade : Nat) (seed : SF.Seed W X () grade) :
 InstalledWriter grade (SF.cfg (AI.withActualInput code (SF.defaultFactory W X ())) grade seed) seed := by
 intro currentFrame
 refine ⟨_,rfl,?_⟩
 exact (SourceHistoryCommon.parallel_left _ _ _).1

/-- Before birth augments its stock, the native packet retains the exact installed seed. -/
theorem native_after_admission_installed (packet : AS.AdmissionPacket (W:=W) (X:=X) (s:=())) :
 let factory:=AI.withActualInput code (SF.defaultFactory W X ())
 let native:=AS.nativeAfterAdmission factory packet
 InstalledWriter native.1 native.2.2.1 native.2.1.2 := by
 dsimp only
 rcases packet with ⟨grade,data,programme,⟨sameVar⟩⟩
 cases programme with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=X at sameVar
  cases sameVar
  intro currentFrame
  refine ⟨_,rfl,?_⟩
  exact (SourceHistoryCommon.parallel_left _ _ _).1

variable (grade : Nat)
variable (programme : A.Programme (PhysicalValue:=L.Value W grade) (PhysicalVar:=X) (sort:=()))
variable (seed : SF.Seed W X () grade)
variable (installed : InstalledWriter grade programme seed)

include installed in
theorem stock_installed : InstalledWriter grade (AS.stockCfg programme) seed := by
 intro currentFrame
 obtain ⟨carried,writes,preserved⟩:=installed currentFrame
 refine ⟨_,rfl,?_⟩
 intro event present
 apply preserve_generated
 change event ∈ (T.preserve (programme.nextPairInventory currentFrame) _).trace
 rw [writes]
 exact (SourceHistoryCommon.parallel_left _ _ _).1 event (preserved event present)

section Receipt
variable (sourceFrame : A.M.Frame (Value:=L.Value W grade) (Var:=X) (sort:=()))

include installed in
/-- The selected receipt's real next receives this writer's complete inventory. -/
theorem actual_writer_preserved :
 let selected:=S.Complete.atReceipt programme sourceFrame 0
 let target:=S.next selected programme
 ∀ event ∈ (J.Past.written seed selected).trace,
  event ∈ (PR.pairInventory seed (A.epoch target) (S.actualOccurrence target)).trace := by
 dsimp only
 let selected:=S.Complete.atReceipt programme sourceFrame 0
 have actual:= (S.Complete.receipt programme sourceFrame 0).2.2.2
 have nextBorn : S.next selected programme=S.nextBorn selected programme := by
  unfold S.next
  rw [actual]
 rw [nextBorn]
 obtain ⟨carried,writes,preserved⟩:=installed selected
 have inventory : (A.epoch (S.nextBorn selected programme)).pairInventory=some carried := writes
 intro event present
 apply (SourceHistoryCommon.parallel_left _ _ _).1
 unfold PR.priorPairInventory
 rw [inventory]
 exact (SourceHistoryCommon.parallel_left _ _ _).1 event (preserved event present)

abbrev actualWriterTransition := J.Past.I.completionTransition seed
 (S.Complete.atReceipt programme sourceFrame 0)
 (S.next (S.Complete.atReceipt programme sourceFrame 0) programme)
 (actual_writer_preserved grade programme seed installed sourceFrame)

/-- This consumes the original disposition and keeps all four outcomes. -/
def actualWriterOutput := J.Past.I.output seed
 (S.Complete.atReceipt programme sourceFrame 0)
 (S.next (S.Complete.atReceipt programme sourceFrame 0) programme)
 (actual_writer_preserved grade programme seed installed sourceFrame)

include installed in
theorem actual_writer_trace :
 let selected:=S.Complete.atReceipt programme sourceFrame 0
 let target:=S.next selected programme
 ∀ event ∈ (SourceOperationPaidRelations.exposure
  (J.queryResult seed (A.epoch selected) (S.actualOccurrence selected)).2.1.2).trace,
  event ∈ (PR.pairInventory seed (A.epoch target) (S.actualOccurrence target)).trace := by
 intro selected target event present
 exact actual_writer_preserved grade programme seed installed sourceFrame event
  (J.Past.current_written_preserved seed selected event
   (J.complete_query_trace seed (A.epoch selected) (S.actualOccurrence selected) event present))

open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
variable (sound : GeneratedRelationSoundnessAt
 (J.face seed (A.epoch (S.Complete.atReceipt programme sourceFrame 0))
  (S.actualOccurrence (S.Complete.atReceipt programme sourceFrame 0))))
variable (obstruction : GeneratedCoverageResidualObstructionAt
 (J.face seed (A.epoch (S.Complete.atReceipt programme sourceFrame 0))
  (S.actualOccurrence (S.Complete.atReceipt programme sourceFrame 0))) sound)
variable (coordinate : GeneratedKernelResidualCoordinateAt
 (J.face seed (A.epoch (S.Complete.atReceipt programme sourceFrame 0))
  (S.actualOccurrence (S.Complete.atReceipt programme sourceFrame 0))) sound)
variable (selected : J.disposition seed (A.epoch (S.Complete.atReceipt programme sourceFrame 0))
 (S.actualOccurrence (S.Complete.atReceipt programme sourceFrame 0))=
 .kernelResidual sound obstruction coordinate)

theorem kernel_source_certificate :
 ∃ certificate : SourceOperationScalarPresentation.RelationIndex ℤ
  (PR.raw seed (A.epoch (S.Complete.atReceipt programme sourceFrame 0))
   (S.actualOccurrence (S.Complete.atReceipt programme sourceFrame 0))).environment () →₀ ℤ,
 SourceOperationScalarPresentation.relationMap (R:=ℤ)
  (PR.raw seed (A.epoch (S.Complete.atReceipt programme sourceFrame 0))
   (S.actualOccurrence (S.Complete.atReceipt programme sourceFrame 0))).environment certificate=
 (J.kernelWord seed (A.epoch (S.Complete.atReceipt programme sourceFrame 0))
  (S.actualOccurrence (S.Complete.atReceipt programme sourceFrame 0)) sound coordinate).val := by
 change (J.kernelWord seed (A.epoch (S.Complete.atReceipt programme sourceFrame 0))
  (S.actualOccurrence (S.Complete.atReceipt programme sourceFrame 0)) sound coordinate).val ∈
  LinearMap.range (SourceOperationScalarPresentation.relationMap (R:=ℤ) _)
 rw [SourceOperationScalarPresentation.relation_range_eq_kernel]
 exact J.kernel_word_value seed _ _ sound coordinate

include obstruction selected in
theorem actual_kernel_ast :
 (J.queryRaw seed (A.epoch (S.Complete.atReceipt programme sourceFrame 0))
  (S.actualOccurrence (S.Complete.atReceipt programme sourceFrame 0))
  (J.disposition seed (A.epoch (S.Complete.atReceipt programme sourceFrame 0))
   (S.actualOccurrence (S.Complete.atReceipt programme sourceFrame 0)))).expression=
 Coefficients.expression (J.kernelWord seed (A.epoch (S.Complete.atReceipt programme sourceFrame 0))
  (S.actualOccurrence (S.Complete.atReceipt programme sourceFrame 0)) sound coordinate).val := by
 rw [selected]
 rfl

include obstruction selected in
theorem actual_kernel_query_value :
 (J.queryResult seed (A.epoch (S.Complete.atReceipt programme sourceFrame 0))
  (S.actualOccurrence (S.Complete.atReceipt programme sourceFrame 0))).2.2.1=0 := by
 have value:=RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (SourceOperationInquiry.Context.Faces.Execution.Mother.baseState
   (A.epoch (S.Complete.atReceipt programme sourceFrame 0))).root.toAuthoritativeRoot
  (J.queryReader seed (A.epoch (S.Complete.atReceipt programme sourceFrame 0)))
  (S.actualOccurrence (S.Complete.atReceipt programme sourceFrame 0))
 apply value.trans
 change (J.queryRaw seed _ _ (J.disposition seed _ _)).expression.eval
  (J.queryRaw seed _ _ (J.disposition seed _ _)).environment=0
 rw [selected]
 change (Coefficients.expression (J.kernelWord seed _ _ sound coordinate).val).eval
  (PR.raw seed _ _).environment=0
 rw [Coefficients.expression_eval]
 exact J.kernel_word_value seed _ _ sound coordinate

include obstruction selected in
theorem actual_kernel_paid :
 CofinalHistoryTransition.GeneratedTransition.completionMap _ _
  (actualWriterTransition grade programme seed installed sourceFrame) coordinate.coordinate.val=0 :=
 J.Past.I.born_kernel_zero seed (S.Complete.atReceipt programme sourceFrame 0)
  (S.next (S.Complete.atReceipt programme sourceFrame 0) programme)
  (actual_writer_preserved grade programme seed installed sourceFrame)
  sound obstruction coordinate selected
end Receipt

end Source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
