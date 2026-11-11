import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceiptBlock
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceiptFibre

set_option autoImplicit false
set_option Elab.async false
noncomputable section
universe u uParent uIndex uWhole uNext uHistoryEnd uHistory

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceiptIntervalFibre
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open CofinalHistorySettlement CenteredGram.IntegralGraphJointAction
open ActualNativeRelationTransport (OccurrenceBlock)

namespace F
export SourceInventoryExecutionFeed (Request Event request_origin_from eventItems receipt)
export SourceInventoryExecutionFeed.ReceiptOccurrence (executedTrace requestWord)
end F
namespace Cfa
export ActualCofinalSourceAction (sourceBorn bornStock born_inventory nativePacket selected packetTransport)
export ActualCofinalSourceAction.AS (AdmissionPacket)
export ActualCofinalSourceAction.D (packetAt)
export ActualCofinalSourceAction.L (Value groups)
export ActualCofinalSourceAction.SF (Factory)
export ActualNativeRelationTransport.AS (stockDecodedEnvironment)
end Cfa
namespace Batch
export ActualCofinalSourceAction.SourceReceiptOccurrence.Batch (requests actedWords sourceBlock nextBlock)
end Batch
namespace R
export ActualCofinalSourceAction.SourceReceiptOccurrence (ExecutionAt)
end R
namespace M
export ActualCofinalResidualModelSplice
  (semanticZero PacketWords packetWordTransport packetLanguageWord packet_semantic_zero packet_language_semantic_zero
   semantic_model_equiv all_word_site_invisible)
export ActualCofinalCommonAction (projection)
end M
open private executedTrace_append from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt.Block
open private acted_word_closed actual_birth_closed from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceiptFibre
open private following_literal from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt
open private block_reindex from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceiptBlock

section Generic
variable {S : Type u} {V X : S → Type u} [∀ t, AddCommGroup (V t)] {s : S}

/-- Restrict an actual executed batch without summing or sorting any of its requests. -/
private def restrictBlock (decoder : Env V X) (requests : List (F.Request (V := V) (X := X) (s := s)))
    {stock : List (F.Event (V := V) (X := X) (s := s))}
    (whole : OccurrenceBlock (F.executedTrace decoder requests) stock) (first count : Nat) :
    OccurrenceBlock (F.executedTrace decoder ((requests.drop first).take count)) stock := by
  let front := F.executedTrace decoder (requests.take first)
  let back := F.executedTrace decoder ((requests.drop first).drop count)
  let middle := F.executedTrace decoder ((requests.drop first).take count)
  refine ⟨whole.before ++ front, back ++ whole.after, whole.trace_eq.trans ?_⟩
  have split : F.executedTrace decoder requests = front ++ middle ++ back := by
    have firstSplit := (congrArg (F.executedTrace decoder) (List.take_append_drop first requests).symm).trans
      (executedTrace_append decoder (requests.take first) (requests.drop first))
    have lastSplit := (congrArg (F.executedTrace decoder)
      (List.take_append_drop count (requests.drop first)).symm).trans
        (executedTrace_append decoder ((requests.drop first).take count) ((requests.drop first).drop count))
    exact firstSplit.trans ((congrArg (fun tail => front ++ tail) lastSplit).trans
      (List.append_assoc front middle back).symm)
  exact (congrArg (fun trace => whole.before ++ trace ++ whole.after) split).trans
    (by simp only [List.append_assoc, middle])

private theorem request_semantic (decoder : Env V X) (request : F.Request (V := V) (X := X) (s := s))
    (closed : PaidSyntax.NoVariable request.expression) : F.requestWord decoder request ∈ M.semanticZero := by
  unfold SourceInventoryExecutionFeed.ReceiptOccurrence.requestWord
  apply Submodule.smul_mem
  rw [SourceOperationPaidRelations.paid_boundary, (F.receipt decoder request).relation_boundary (R := ℤ)]
  intro environment
  rw [map_sub]
  simp only [evaluation, Finsupp.linearCombination_single, one_smul, Expr.eval]
  exact sub_eq_zero.mpr (PaidSyntax.eval_eq request.expression closed environment decoder)

end Generic

section Abstract
variable {S : Type u} {W X : S → Type u} [∀ t, AddCommGroup (W t)] {s : S}
local instance gradeGroups (grade : Nat) : ∀ t, AddCommGroup (Cfa.Value W grade t) := Cfa.groups W grade
variable (factory : Cfa.Factory W X s) (packet : Cfa.AdmissionPacket (W := W) (X := X) (s := s))
variable (execution : R.ExecutionAt packet)
set_option quotPrecheck false in
local notation "decoder" => Cfa.stockDecodedEnvironment (Cfa.selected factory packet) (Cfa.nativePacket factory packet).2.2.1
local notation "requests" => Batch.requests factory packet execution

private theorem request_closed (closed : PaidSyntax.NoVariable execution.request.expression)
    (item : F.Request (V := Cfa.Value W (packet.1+1)) (X := packet.2.2.1.LowVar) (s := s))
    (present : item ∈ requests) : PaidSyntax.NoVariable item.expression := by
  let words := Batch.actedWords packet execution
  let events := words.map PresentedRelationEventAt.relation
  obtain ⟨front, back, exactEvent, _, support⟩ := F.request_origin_from
    (Batch.sourceBlock factory packet execution).before.length events item present
  have event : item.sourceEvent ∈ events := by
    rw [exactEvent]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨word, source, same⟩ := List.mem_map.mp event
  obtain ⟨old, oldSource, transported⟩ := List.mem_map.mp source
  have allClosed := acted_word_closed packet old
    (PaidSyntax.trace_words_noVariable execution.paid closed old oldSource)
  have wordClosed : PaidSyntax.WordNoVariable word := transported ▸ allClosed
  rw [← same] at support
  change (item.expression,item.coefficient) ∈ Coefficients.sourceItems word at support
  unfold Coefficients.sourceItems at support
  obtain ⟨term, member, occurs⟩ := List.mem_map.mp support
  have sameExpr : term = item.expression := congrArg Prod.fst occurs
  exact sameExpr ▸ wordClosed term (Finset.mem_toList.mp member)

private theorem interval_semantic (closed : PaidSyntax.NoVariable execution.request.expression)
    (first count : Nat) :
    ((((requests).drop first).take count).map (F.requestWord decoder)).sum ∈ M.semanticZero := by
  apply _root_.list_sum_mem
  intro word belongs
  obtain ⟨request, present, rfl⟩ := List.mem_map.mp belongs
  exact request_semantic decoder request (request_closed factory packet execution closed request
    (List.mem_of_mem_drop (List.mem_of_mem_take present)))

variable {Y : S → Type u}
variable (target : Cfa.AdmissionPacket (W := W) (X := Y) (s := s))
variable (language : packet.2.2.1.LowVar = Y)
variable (same : Cfa.packetTransport language (Cfa.sourceBorn factory packet) = target)

private def reindexedInterval (first count : Nat) : M.PacketWords target :=
  M.packetWordTransport same
    (M.packetLanguageWord language (Cfa.sourceBorn factory packet)
      ((((requests).drop first).take count).map (F.requestWord decoder)).sum)

private theorem reindexed_interval_semantic (closed : PaidSyntax.NoVariable execution.request.expression)
    (first count : Nat) :
    reindexedInterval factory packet execution target language same first count ∈ M.semanticZero :=
  M.packet_semantic_zero same _
    (M.packet_language_semantic_zero language (Cfa.sourceBorn factory packet) _
      (interval_semantic factory packet execution closed first count))

end Abstract

namespace A
export BornRCanonicalMethodRuntime (W X fixedRFactory)
end A
namespace H
export BornRSourceMethodHistory (receiver methodProgramme)
end H
namespace N
export PhysicalGammaNextReceipt (actualBirth)
end N
namespace T
export ActualCofinalNativeTower (Words)
end T

local notation "slot" => CompletedSourceRCalculation.Slot.branches
local instance levelGroups (grade : Nat) : ∀ target, AddCommGroup (Cfa.Value A.W grade target) :=
  Cfa.groups A.W grade

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
local notation "native" => Cfa.sourceBorn factory current
local notation "literal" => following_literal observation nontrivial half depth ordinal (update := update)
local notation "born" => N.actualBirth observation nontrivial half depth ordinal method
local notation "allRequests" => Batch.requests factory current born
set_option quotPrecheck false in
local notation "decoder" => Cfa.stockDecodedEnvironment (Cfa.selected factory current)
  (Cfa.nativePacket factory current).2.2.1

set_option cleanup.letToHave false in
/-- The chosen consecutive requests have their complete written traces in the same literal next stock. -/
def actualInterval (first count : Nat) :=
  block_reindex native nextSite (current).2.2.2.down literal
    (Cfa.bornStock factory current) (Cfa.born_inventory factory current)
    (F.executedTrace decoder (((allRequests).drop first).take count))
    (restrictBlock decoder allRequests (Batch.nextBlock factory current born) first count)

/-- The signed sum is taken only after selecting the actual interval and its paid traces. -/
def intervalWord (first count : Nat) : T.Words factory initial programme rfl nextOrdinal :=
  reindexedInterval factory current born nextSite (current).2.2.2.down literal first count

set_option cleanup.letToHave false in
theorem actual_interval_semantic (first count : Nat) :
    intervalWord observation nontrivial half depth ordinal method first count ∈ M.semanticZero :=
  reindexed_interval_semantic factory current born nextSite (current).2.2.2.down literal
    (actual_birth_closed observation nontrivial half depth ordinal method) first count

set_option cleanup.letToHave false in
/-- Every retained interval pays the existing full future Model, at its actual next site. -/
theorem actual_interval_fibre (first count : Nat) :
    M.projection factory initial programme rfl
      (DFinsupp.single nextOrdinal (intervalWord observation nontrivial half depth ordinal method first count)) =
    M.projection factory initial programme rfl (DFinsupp.single nextOrdinal 0) :=
  M.semantic_model_equiv factory initial programme rfl nextOrdinal _ _
    (by rw [sub_zero]; exact actual_interval_semantic observation nontrivial half depth ordinal method first count)

end CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceiptIntervalFibre
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
