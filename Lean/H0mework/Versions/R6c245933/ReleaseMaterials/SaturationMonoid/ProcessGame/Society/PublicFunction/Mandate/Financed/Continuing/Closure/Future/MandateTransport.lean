import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Future.Source
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed.Transport
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed.Cuts

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle

variable {fuel : ℚ} {inputs : List (List Action)}

 theorem common_prefix_transports_the_whole_mandate_state (cut : Cut fuel inputs) (word : List Action)
    (birth : Fin (cut.depth + 1))
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val)) (last : Nat) (within : last ≤ cut.depth) :
    (Runtime.traceGrant fuel (branchInputs cut word) birth.val last
      (transportOriginalGrant cut word birth grant)).continuation.state =
    (Runtime.traceGrant fuel inputs birth.val last grant).continuation.state := by
  exact Lifecycle.Observed.through_state_congr last
    (transported_grant_keeps_original_acceptance_index cut word birth grant)
    (transported_grant_has_the_same_native_admission cut word birth grant)
    (fun visit earlier => (original_current_and_word_at_each_birth cut word ⟨visit, by omega⟩).1)
    (fun visit earlier => (original_current_and_word_at_each_birth cut word ⟨visit, by omega⟩).2)


abbrev oldBefore {fuel : ℚ} {inputs : List (List Action)} (cut : Cut fuel inputs)
    (birth : Fin (cut.depth + 1))
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val)) (visit : Nat) :=
  Lifecycle.Observed.beforeVisit (base := base) (scope := scope)
    (currentAt := Runtime.mandateCurrentAt fuel inputs) (wordAt := Runtime.mandateWordAt fuel inputs)
    (birth := birth.val) (grant := grant) visit

abbrev newBefore {fuel : ℚ} {inputs : List (List Action)} (cut : Cut fuel inputs) (word : List Action)
    (birth : Fin (cut.depth + 1))
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val)) (visit : Nat) :=
  Lifecycle.Observed.beforeVisit (base := base) (scope := scope)
    (currentAt := Runtime.mandateCurrentAt fuel (branchInputs cut word))
    (wordAt := Runtime.mandateWordAt fuel (branchInputs cut word))
    (birth := birth.val) (grant := transportOriginalGrant cut word birth grant) visit

 theorem common_prefix_transports_every_partial_visit (cut : Cut fuel inputs) (word : List Action)
    (birth : Fin (cut.depth + 1))
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val)) (visit count : Nat) (within : visit ≤ cut.depth) :
    ((newBefore cut word birth grant visit).visitPrefix visit count).state =
      ((oldBefore cut birth grant visit).visitPrefix visit count).state := by
  have same := Lifecycle.Observed.beforeVisit_state_congr cut.depth visit within
    (transported_grant_keeps_original_acceptance_index cut word birth grant)
    (transported_grant_has_the_same_native_admission cut word birth grant)
    (fun visit earlier => (original_current_and_word_at_each_birth cut word ⟨visit, by omega⟩).1)
    (fun visit earlier => (original_current_and_word_at_each_birth cut word ⟨visit, by omega⟩).2)
  exact Lifecycle.Observed.History.visitPrefix_state_congr
    (transported_grant_keeps_original_acceptance_index cut word birth grant) _ _ same visit count
    (original_current_and_word_at_each_birth cut word ⟨visit, by omega⟩).1
    (original_current_and_word_at_each_birth cut word ⟨visit, by omega⟩).2

 theorem common_prefix_preserves_each_complete_read_effect (cut : Cut fuel inputs) (word : List Action)
    (birth : Fin (cut.depth + 1))
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val)) (visit count : Nat) (within : visit ≤ cut.depth)
    (item : {item // item ∈ law.rawItems (Runtime.mandateCurrentAt fuel inputs visit) (Runtime.mandateWordAt fuel inputs visit)}) :
    HEq ((Lifecycle.Observed.readEvent
      ((newBefore cut word birth grant visit).visitPrefix visit count).obligation
      ((newBefore cut word birth grant visit).visitPrefix visit count).origin visit
      (Lifecycle.Observed.reindexItem
        (original_current_and_word_at_each_birth cut word ⟨visit, by omega⟩).1
        (original_current_and_word_at_each_birth cut word ⟨visit, by omega⟩).2 item)).map Lifecycle.Observed.effect)
    ((Lifecycle.Observed.readEvent
      ((oldBefore cut birth grant visit).visitPrefix visit count).obligation
      ((oldBefore cut birth grant visit).visitPrefix visit count).origin visit item).map Lifecycle.Observed.effect) :=
  Lifecycle.Observed.History.read_effect_heq
    (transported_grant_keeps_original_acceptance_index cut word birth grant) _ _
    (common_prefix_transports_every_partial_visit cut word birth grant visit count within) visit _ _ item


def PerItemEvidenceAgreement (cut : Cut fuel inputs) (word : List Action) (birth : Fin (cut.depth + 1))
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val)) : Prop :=
  ∀ (visit count : Nat) (within : visit ≤ cut.depth)
    (item : {item // item ∈ law.rawItems (Runtime.mandateCurrentAt fuel inputs visit) (Runtime.mandateWordAt fuel inputs visit)}),
    HEq ((Lifecycle.Observed.readEvent
      ((newBefore cut word birth grant visit).visitPrefix visit count).obligation
      ((newBefore cut word birth grant visit).visitPrefix visit count).origin visit
      (Lifecycle.Observed.reindexItem
        (original_current_and_word_at_each_birth cut word ⟨visit, by omega⟩).1
        (original_current_and_word_at_each_birth cut word ⟨visit, by omega⟩).2 item)).map Lifecycle.Observed.effect)
    ((Lifecycle.Observed.readEvent
      ((oldBefore cut birth grant visit).visitPrefix visit count).obligation
      ((oldBefore cut birth grant visit).visitPrefix visit count).origin visit item).map Lifecycle.Observed.effect)

noncomputable section

structure MandateTransport (cut : Cut fuel inputs) (word : List Action)
    (birth : Fin (cut.depth + 1))
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val)) where
  private mk ::
  old : Runtime.TracedGrant fuel inputs birth.val cut.depth
  old_exact : old = Runtime.traceGrant fuel inputs birth.val cut.depth grant
  common : Runtime.TracedGrant fuel (branchInputs cut word) birth.val cut.depth
  common_exact : common = Runtime.traceGrant fuel (branchInputs cut word) birth.val cut.depth
    (transportOriginalGrant cut word birth grant)
  same_state : common.continuation.state = old.continuation.state
  per_item : PerItemEvidenceAgreement cut word birth grant
  next : Runtime.TracedGrant fuel (branchInputs cut word) birth.val (afterInput cut word).depth
  next_exact : next = Runtime.traceGrant fuel (branchInputs cut word) birth.val (afterInput cut word).depth
    (transportOriginalGrant cut word birth grant)
  crossing : (Lifecycle.Observed.process (base := base) (scope := scope)
    (currentAt := Runtime.mandateCurrentAt fuel (branchInputs cut word))
    (wordAt := Runtime.mandateWordAt fuel (branchInputs cut word))
    (birth := birth.val) (grant := transportOriginalGrant cut word birth grant)).Run
    old.continuation.state next.continuation.state
  recorded : grant ∈ grantsAt base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val) →
    (⟨⟨birth.val, by change birth.val < (branchInputs cut word).length + 1; rw [branchInputs_length]; omega⟩, next⟩ :
      Sigma fun born : Fin ((afterInput cut word).depth + 1) =>
        Runtime.TracedGrant fuel (branchInputs cut word) born.val (afterInput cut word).depth) ∈
      Runtime.recordsAt fuel (branchInputs cut word) (afterInput cut word).depth

def transportMandate (cut : Cut fuel inputs) (word : List Action) (birth : Fin (cut.depth + 1))
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val)) : MandateTransport cut word birth grant := by
  refine ⟨Runtime.traceGrant fuel inputs birth.val cut.depth grant, rfl,
    Runtime.traceGrant fuel (branchInputs cut word) birth.val cut.depth (transportOriginalGrant cut word birth grant), rfl,
    common_prefix_transports_the_whole_mandate_state cut word birth grant cut.depth (Nat.le_refl _),
    common_prefix_preserves_each_complete_read_effect cut word birth grant,
    Runtime.traceGrant fuel (branchInputs cut word) birth.val (afterInput cut word).depth (transportOriginalGrant cut word birth grant), rfl, ?_, ?_⟩
  · have crossing := Lifecycle.Observed.fromActualCut (base := base) (scope := scope)
      (currentAt := Runtime.mandateCurrentAt fuel (branchInputs cut word))
      (wordAt := Runtime.mandateWordAt fuel (branchInputs cut word))
      (birth := birth.val) (grant := transportOriginalGrant cut word birth grant) cut.depth 1
    change (Lifecycle.Observed.process).Run
      (Runtime.traceGrant fuel (branchInputs cut word) birth.val cut.depth (transportOriginalGrant cut word birth grant)).continuation.state
      (Runtime.traceGrant fuel (branchInputs cut word) birth.val (cut.depth + 1) (transportOriginalGrant cut word birth grant)).continuation.state at crossing
    rw [common_prefix_transports_the_whole_mandate_state cut word birth grant cut.depth (Nat.le_refl _)] at crossing
    have depth : (afterInput cut word).depth = cut.depth + 1 := branchInputs_length cut word
    rw [depth]
    exact crossing
  · intro actual
    exact Runtime.every_original_grant_is_retained _ _ _ _ _
      (transported_grant_is_actually_present cut word birth grant actual)

end

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure
