import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Trace.VariableFree
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Common.RootConsumer.Semantics
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalGammaNextReceiptFibre"

set_option autoImplicit false
set_option Elab.async false
noncomputable section
universe u uParent uIndex uWhole uNext uHistoryEnd uHistory
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceiptFibre
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations CofinalHistorySettlement CenteredGram.IntegralGraphJointAction
namespace S
export PaidSyntax (NoVariable WordNoVariable eval_eq lift_noVariable lift_word_noVariable trace_words_noVariable)
end S
namespace Cfa
export ActualCofinalSourceAction (sourceBorn sourceWordAction wordTransport packetTransport)
export ActualCofinalSourceAction.AS (AdmissionPacket)
export ActualCofinalSourceAction.D (packetAt)
export ActualCofinalSourceAction.SF (Factory)
end Cfa
namespace Lower
export ActualCofinalSourceAction.L (Value groups)
end Lower
namespace R
export ActualCofinalSourceAction.SourceReceiptOccurrence (ExecutionAt InventoryAt SupportIndex acted atBirth)
export ActualCofinalSourceAction.SourceReceiptOccurrence.ExecutionAt (reindex)
end R
namespace P
export SourceOperationPaidRelations (words stepOccurrence stepOccurrence_word)
end P
namespace WR
export SourceInventoryExecutionFeed.WordReceipt (RelationOccurrence)
end WR
namespace M
export ActualCofinalCommonAction (projection model_fibre)
export ActualCofinalResidualModelSplice (semanticZero semantic_model_equiv)
export ActualCofinalNativeTower (Words)
end M

section Abstract

variable {Sorts : Type u} {W X Y : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
local instance abstractGroups (grade : Nat) : ∀ target, AddCommGroup (Lower.Value W grade target) :=
  Lower.groups W grade

private theorem reindex_closed (original : Cfa.AdmissionPacket (W := W) (X := X) (s := s))
    (target : Cfa.AdmissionPacket (W := W) (X := Y) (s := s))
    (language : X = Y) (same : Cfa.packetTransport language original = target)
    (execution : R.ExecutionAt original) (closed : S.NoVariable execution.request.expression) :
    S.NoVariable (R.reindex original target language same execution).request.expression := by
  cases language
  cases same
  exact closed

private theorem paid_step_closed {packet : Cfa.AdmissionPacket (W := W) (X := X) (s := s)}
    (execution : R.ExecutionAt packet) (closed : S.NoVariable execution.request.expression)
    (index : Fin (P.words execution.paid).length) :
    S.WordNoVariable (execution.step index).word := by
  change S.WordNoVariable ((P.stepOccurrence execution.paid index).transport execution.segment).word
  rw [(P.stepOccurrence execution.paid index).transport_word execution.segment, P.stepOccurrence_word]
  exact S.trace_words_noVariable execution.paid closed _ (List.get_mem _ index)

private theorem transport_word_closed {V : Sorts → Type u} [∀ target, AddCommGroup (V target)]
    (language : X = Y) (word : Formal ℤ V X s) (closed : S.WordNoVariable word) :
    S.WordNoVariable (Cfa.wordTransport language word) := by
  cases language
  exact closed

private theorem acted_word_closed (packet : Cfa.AdmissionPacket (W := W) (X := X) (s := s))
    (word : Formal ℤ (Lower.Value W packet.1) X s) (closed : S.WordNoVariable word) :
    S.WordNoVariable (Cfa.sourceWordAction packet word) := by
  change S.WordNoVariable (Cfa.wordTransport packet.2.2.2.down.symm (liftMap (R := ℤ) word))
  exact transport_word_closed _ _ (S.lift_word_noVariable word closed)

private theorem source_item_closed {V : Sorts → Type u} [∀ target, AddCommGroup (V target)]
    (word : Formal ℤ V X s) (closed : S.WordNoVariable word)
    (index : Fin (Coefficients.sourceItems word).length) :
    S.NoVariable ((Coefficients.sourceItems word).get index).1 := by
  have member := List.get_mem (Coefficients.sourceItems word) index
  change (Coefficients.sourceItems word).get index ∈
    word.support.toList.map (fun term => (term, word term)) at member
  obtain ⟨term, supported, same⟩ := List.mem_map.mp member
  exact (congrArg Prod.fst same) ▸ closed term (Finset.mem_toList.mp supported)

private theorem native_request_closed (factory : Cfa.Factory W X s)
    (packet : Cfa.AdmissionPacket (W := W) (X := X) (s := s))
    (prior : R.InventoryAt packet) (installed : packet.2.1.1.inventory = some prior)
    (atom : WR.RelationOccurrence prior) (closed : S.WordNoVariable atom.word)
    (index : R.SupportIndex factory packet prior installed atom) :
    S.NoVariable (R.atBirth factory packet prior installed atom index).request.expression := by
  let acted := R.acted factory packet prior installed atom
  have carried : S.WordNoVariable acted.word := acted_word_closed packet atom.word closed
  change S.NoVariable ((Coefficients.sourceItems acted.word).get index).1
  exact source_item_closed acted.word carried index

private theorem receipt_semantic {packet : Cfa.AdmissionPacket (W := W) (X := X) (s := s)}
    (execution : R.ExecutionAt packet) (closed : S.NoVariable execution.request.expression) :
    Finsupp.single execution.request.expression 1 -
      Finsupp.single (.const (execution.request.expression.eval execution.decoder)) 1 ∈ M.semanticZero := by
  intro environment
  rw [map_sub]
  simp only [evaluation, Finsupp.linearCombination_single, one_smul, Expr.eval]
  exact sub_eq_zero.mpr
    ((S.eval_eq execution.request.expression closed environment execution.decoder).trans execution.paid.sound)

end Abstract

namespace A
export BornRCanonicalMethodRuntime (W X fixedRFactory)
end A
namespace H
export BornRSourceMethodHistory (receiver methodProgramme)
end H
namespace Q
export PhysicalGammaActionQuery (request sourceOccurrence sourceOccurrence_expression sourceData)
end Q
namespace BF
export PhysicalGammaBoundaryFeedback (StepIndex)
end BF
namespace N
export PhysicalGammaNextReceipt
  (actualBirth actualStep nativeNextReceipt actualNextReceipt nextReceiptRelation SupportIndex)
end N

open private born_packet_literal from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.BoundaryFeedback
open private originalBirth actualIndex following_literal from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt

local notation "slot" => CompletedSourceRCalculation.Slot.branches
local instance levelGroups (grade : Nat) : ∀ target, AddCommGroup (Lower.Value A.W grade target) :=
  Lower.groups A.W grade

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
variable {input : CompletedSourceRCalculation.Value slot}

private theorem literal_expression_closed (data : ActionMaterial observation nontrivial half input) :
    S.NoVariable (ActionSource.expression observation nontrivial half data) := by
  rw [ActionSource.expression_positions]
  exact ⟨⟨True.intro, True.intro⟩, ⟨⟨True.intro, True.intro⟩, ⟨True.intro, True.intro⟩⟩⟩

private theorem grade_expression_closed
    (data : ActionMaterial observation nontrivial half input) (grade : Nat) :
    S.NoVariable (ActionSource.atGrade observation nontrivial half data grade) := by
  induction grade with
  | zero =>
    exact S.lift_noVariable _ (literal_expression_closed observation nontrivial half data)
  | succ grade previous =>
    exact S.lift_noVariable (ActionSource.atGrade observation nontrivial half data grade) previous

private theorem query_request_closed (packet : Cfa.AdmissionPacket (W := A.W) (X := A.X) (s := slot)) :
    S.NoVariable (Q.request observation nontrivial half packet).expression := by
  change S.NoVariable (Q.sourceOccurrence observation nontrivial half packet).expression
  rw [Q.sourceOccurrence_expression]
  rcases packet with ⟨grade, ⟨frame, seed⟩, ⟨Y, datum, scalar, pair⟩, ⟨language⟩⟩
  cases language
  exact grade_expression_closed observation nontrivial half _ (grade + 1)

variable (depth ordinal : Nat)
local notation "factory" => A.fixedRFactory observation nontrivial half
local notation "initial" => H.receiver observation nontrivial half depth ordinal
local notation "programme" => H.methodProgramme observation nontrivial half depth ordinal
local notation "site" => Cfa.packetAt factory initial programme rfl
variable {Parent : Sort uParent} {Index : Sort uIndex} {Whole : Sort uWhole}
variable {Next : Sort uNext} {HistoryEnd : Sort uHistoryEnd} {History : Sort uHistory}
variable {update cutoff : Nat}
variable (method : BornRSourcePrice.SourcePriceMethodReceipt (Parent := Parent) (Index := Index)
  (Whole := Whole) (Next := Next) (HistoryEnd := HistoryEnd) (History := History)
  observation nontrivial half depth ordinal update cutoff)

local notation "sourceSite" => site (update+2)
local notation "receiptOrdinal" => ((update+2)+1)
local notation "receiptSite" => site receiptOrdinal
local notation "birth" => N.actualBirth observation nontrivial half depth ordinal method
local notation "AtomIndex" => BF.StepIndex observation nontrivial half method.source
local notation "Support" => N.SupportIndex observation nontrivial half depth ordinal method

private theorem actual_birth_closed : S.NoVariable (birth).request.expression :=
  reindex_closed (Cfa.sourceBorn factory method.source) sourceSite method.source.2.2.2.down
    (born_packet_literal observation nontrivial half depth ordinal method)
    (originalBirth observation nontrivial half depth ordinal method)
    (query_request_closed observation nontrivial half method.source)

private theorem actual_atom_closed (index : AtomIndex) :
    S.WordNoVariable (N.actualStep observation nontrivial half depth ordinal method index).word :=
  paid_step_closed birth (actual_birth_closed observation nontrivial half depth ordinal method)
    (actualIndex observation nontrivial half depth ordinal method index)

local notation "requestAt" => N.actualNextReceipt observation nontrivial half depth ordinal method

private theorem actual_next_request_closed (index : AtomIndex) (support : Support index) :
    S.NoVariable (requestAt index support).request.expression :=
  reindex_closed (Cfa.sourceBorn factory sourceSite) receiptSite (sourceSite).2.2.2.down
    (following_literal observation nontrivial half depth ordinal (update := update))
    (N.nativeNextReceipt observation nontrivial half depth ordinal method index support)
    (native_request_closed factory sourceSite (birth).stock (birth).installed
      (N.actualStep observation nontrivial half depth ordinal method index)
      (actual_atom_closed observation nontrivial half depth ordinal method index) support)

/-- The actual paid boundary remains valid in every environment of the original next packet. -/
theorem actual_next_relation_semantic (index : AtomIndex) (support : Support index) :
    (N.nextReceiptRelation observation nontrivial half depth ordinal method index support).val ∈ M.semanticZero :=
  receipt_semantic (requestAt index support)
    (actual_next_request_closed observation nontrivial half depth ordinal method index support)

set_option cleanup.letToHave false in
/-- The old Model reads the exact next receipt and its actual terminal in the same full future fibre. -/
theorem actual_next_receipt_model_fibre (index : AtomIndex) (support : Support index) :
    let executed := requestAt index support
    let raw : M.Words factory initial programme rfl receiptOrdinal :=
      Finsupp.single executed.request.expression 1
    let terminal : M.Words factory initial programme rfl receiptOrdinal :=
      Finsupp.single (.const (executed.request.expression.eval executed.decoder)) 1
    M.projection factory initial programme rfl (DFinsupp.single receiptOrdinal raw) =
      M.projection factory initial programme rfl (DFinsupp.single receiptOrdinal terminal) :=
  M.semantic_model_equiv factory initial programme rfl receiptOrdinal _ _
    (actual_next_relation_semantic observation nontrivial half depth ordinal method index support)

end CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceiptFibre
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
