import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceiptPosition
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceiptIntervalFibre

set_option autoImplicit false
set_option Elab.async false
noncomputable section
universe u uParent uIndex uWhole uNext uHistoryEnd uHistory

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceiptPosition
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open CofinalHistorySettlement CenteredGram.IntegralGraphJointAction

namespace P
export SourceOperationPaidRelations (paidCut_word)
end P
namespace M
export ActualCofinalResidualModelSplice (semanticZero semantic_model_equiv)
export ActualCofinalCommonAction (projection)
end M
namespace Cx
export CofinalRelationGeneratedComplex (natComplex completion_kills_generated_differential)
end Cx

open private jointFromRelation from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt
open private actual_birth_closed reindex_closed from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceiptFibre
open private request_closed from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceiptIntervalFibre
open private jointHistoryAt from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Transport
open private relation_word_in_stock from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceiptPosition

namespace Cfa
export ActualCofinalSourceAction.SF (Factory)
end Cfa

section Generic
variable {S : Type u} {V Var W X : S → Type u} [∀ t, AddCommGroup (V t)] [∀ t, AddCommGroup (W t)]
variable {s : S}
local instance fibreLevelGroups (grade : Nat) : ∀ t, AddCommGroup (Cfa.Value W grade t) := Cfa.groups W grade

private theorem trace_closed {environment : Env V Var} {first last : Expr V Var s}
    (trace : Trace environment first last) :
    PaidSyntax.NoVariable first → PaidSyntax.NoVariable last := by
  induction trace with
  | nil => exact id
  | cons step _ previous => exact fun closed => previous (PaidSyntax.step_noVariable step closed)

private theorem closed_step_semantic {packet : Cfa.AdmissionPacket (W := W) (X := X) (s := s)}
    (execution : R.ExecutionAt packet) (closed : PaidSyntax.NoVariable execution.request.expression)
    (index : Fin (P.words execution.paid).length) : (execution.step index).word ∈ M.semanticZero := by
  let cut := P.paidCut execution.paid index
  have entryClosed := trace_closed cut.past closed
  have exitClosed := PaidSyntax.step_noVariable cut.step entryClosed
  have nativeEquation : cut.entry.eval execution.decoder = cut.exit.eval execution.decoder := cut.step.sound
  have wordEq : (execution.step index).word = Finsupp.single cut.entry 1 - Finsupp.single cut.exit 1 :=
    ((P.stepOccurrence execution.paid index).transport_word execution.segment).trans
      (P.paidCut_word execution.paid index)
  rw [wordEq]
  intro environment
  rw [map_sub]
  simp only [evaluation, Finsupp.linearCombination_single, one_smul]
  exact sub_eq_zero.mpr
    ((PaidSyntax.eval_eq cut.entry entryClosed environment execution.decoder).trans
      (nativeEquation.trans (PaidSyntax.eval_eq cut.exit exitClosed execution.decoder environment)))

private theorem located_semantic {Y : S → Type u}
    (factory : Cfa.Factory W X s) (packet : Cfa.AdmissionPacket (W := W) (X := X) (s := s))
    (birth : R.ExecutionAt packet) (closed : PaidSyntax.NoVariable birth.request.expression)
    {target : Cfa.AdmissionPacket (W := W) (X := Y) (s := s)}
    {language : packet.2.2.1.LowVar = Y}
    {same : Cfa.packetTransport language (Cfa.sourceBorn factory packet) = target}
    {decoder : Env (Cfa.Value W (Cfa.sourceBorn factory packet).1) packet.2.2.1.LowVar}
    {stock : R.InventoryAt target} {position : Nat} {word : Formal ℤ (Cfa.Value W target.1) Y s}
    (found : LocatedAt (Cfa.sourceBorn factory packet) target language same decoder
      (B.requests factory packet birth) stock position word) : word ∈ M.semanticZero := by
  have originClosed : PaidSyntax.NoVariable found.nativeExecution.request.expression :=
    found.request_source.symm ▸ request_closed factory packet birth closed
      ((B.requests factory packet birth).get found.requestIndex) (List.get_mem _ _)
  have reindexed : PaidSyntax.NoVariable found.execution.request.expression :=
    reindex_closed (Cfa.sourceBorn factory packet) target language same found.nativeExecution originClosed
  exact found.word_eq ▸ closed_step_semantic found.execution reindexed found.index
end Generic

local notation "slot" => CompletedSourceRCalculation.Slot.branches
local instance fibreActualGroups (grade : Nat) : ∀ t, AddCommGroup (Cfa.Value A.W grade t) := Cfa.groups A.W grade

/-- A located Step enters the original relation span of its installed packet. -/
def LocatedAt.installedRelation {X Y : CompletedSourceRCalculation.Slot → Type}
    {native : Cfa.AdmissionPacket (W := A.W) (X := X) (s := slot)}
    {target : Cfa.AdmissionPacket (W := A.W) (X := Y) (s := slot)}
    {language : X = Y} {same : Cfa.packetTransport language native = target}
    {decoder : Env (Cfa.Value A.W native.1) X}
    {requests : List (F.Request (V := Cfa.Value A.W native.1) (X := X) (s := slot))}
    {stock : R.InventoryAt target} {position : Nat} {word : Formal ℤ (Cfa.Value A.W target.1) Y slot}
    (found : LocatedAt native target language same decoder requests stock position word) :
    RF.RelationAt target := by
  refine ⟨stock, found.execution.installed.trans (congrArg some found.stock_eq), word, ?_⟩
  exact (congrArg₂
    (fun (value : Formal ℤ (Cfa.Value A.W target.1) Y slot) (inventory : R.InventoryAt target) =>
      value ∈ F.relationSpace inventory)
    found.word_eq found.stock_eq).mp (relation_word_in_stock (found.execution.step found.index))

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
variable {Parent : Sort uParent} {Index : Sort uIndex} {Whole : Sort uWhole}
variable {Next : Sort uNext} {HistoryEnd : Sort uHistoryEnd} {History : Sort uHistory}
variable {update cutoff : Nat}
variable (method : BornRSourcePrice.SourcePriceMethodReceipt (Parent := Parent) (Index := Index)
  (Whole := Whole) (Next := Next) (HistoryEnd := HistoryEnd) (History := History)
  observation nontrivial half depth ordinal update cutoff)

local notation "factory" => A.fixedRFactory observation nontrivial half
local notation "initial" => H.receiver observation nontrivial half depth ordinal
local notation "programme" => H.methodProgramme observation nontrivial half depth ordinal
local notation "site" => Cfa.packetAt factory initial programme rfl
local notation "current" => site (update+2)
local notation "nextOrdinal" => ((update+2)+1)
local notation "nextSite" => site nextOrdinal
local notation "born" => N.actualBirth observation nontrivial half depth ordinal method
local notation "nextJoint" => jointHistoryAt nextSite

set_option quotPrecheck false in
local notation "positionProof" =>
  (fun (position : Nat) word lower upper actual =>
    let found := actualPosition observation nontrivial half depth ordinal method position word lower upper actual
    let joint := jointFromRelation found.installedRelation
    let semantic := located_semantic factory current born
      (actual_birth_closed observation nontrivial half depth ordinal method) found
    And.intro
      (Cx.completion_kills_generated_differential nextJoint joint)
      (M.semantic_model_equiv factory initial programme rfl nextOrdinal word 0
        (Submodule.sub_mem M.semanticZero semantic (Submodule.zero_mem M.semanticZero))))

set_option cleanup.letToHave false in
set_option backward.isDefEq.respectTransparency false in
/-- The same located Step enters the original Joint and pays its own full future Model fibre. -/
theorem actual_position_consumption : type_of% positionProof := positionProof

end CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceiptPosition
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
